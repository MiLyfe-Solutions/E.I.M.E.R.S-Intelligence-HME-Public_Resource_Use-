import V185TrunkScan23Chunk1162

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6890053 : List Nat := [1, 3, 1, 1, 1, 5, 1, 4, 2, 4]
def baseStart_6890053 : Nat := 118140960795 + 6890053 * 2 ^ 59
def prefixEnd_6890053 : Nat := 4983230072969 + 3 ^ 40 * 6890053 * 2
def baseEnd_6890053 : Nat := 1179302974650945456550243

theorem tailTrace_6890053 : CollatzResearch.WordTrace tailWord_6890053 prefixEnd_6890053 1179302974650945456550243 := by
  unfold tailWord_6890053
  simp only [CollatzResearch.WordTrace]
  refine ⟨251300878107522183213458813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167533918738348122142305875 251300878107522183213458813)
  ·
    refine ⟨94237829290320818705047055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251300878107522183213458813 94237829290320818705047055)
    ·
      refine ⟨141356743935481228057570583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94237829290320818705047055 141356743935481228057570583)
      ·
        refine ⟨212035115903221842086355875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141356743935481228057570583 212035115903221842086355875)
        ·
          refine ⟨318052673854832763129533813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212035115903221842086355875 318052673854832763129533813)
          ·
            refine ⟨29817438173890571543393795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 318052673854832763129533813 29817438173890571543393795)
            ·
              refine ⟨44726157260835857315090693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29817438173890571543393795 44726157260835857315090693)
              ·
                refine ⟨8386154486406723246579505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44726157260835857315090693 8386154486406723246579505)
                ·
                  refine ⟨6289615864805042434934629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8386154486406723246579505 6289615864805042434934629)
                  ·
                    refine ⟨1179302974650945456550243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6289615864805042434934629 1179302974650945456550243)
                    ·
                      rfl

theorem cell23_6890053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4, 2, 4].length) (baseStart_6890053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6890053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6890053 prefixEnd_6890053 := by exact prefixLift 6890053
  have htrace : WordTrace (prefixWord ++ tailWord_6890053) baseStart_6890053 baseEnd_6890053 := by
    simpa [prefixWord, tailWord_6890053, baseEnd_6890053] using wordTrace_append hprefix tailTrace_6890053
  have hstable : (prefixWord ++ tailWord_6890053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6890053).length < 2 ^ (prefixWord ++ tailWord_6890053).sum := by decide
  have hdescent : baseEnd_6890053 < baseStart_6890053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6890053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6890060 : List Nat := [2, 2, 1, 3, 1, 2, 2, 3, 3, 2, 2]
def baseStart_6890060 : Nat := 118140960795 + 6890060 * 2 ^ 59
def prefixEnd_6890060 : Nat := 4983230072969 + 3 ^ 40 * 6890060 * 2
def baseEnd_6890060 : Nat := 3537912518317417842263197

theorem tailTrace_6890060 : CollatzResearch.WordTrace tailWord_6890060 prefixEnd_6890060 3537912518317417842263197 := by
  unfold tailWord_6890060
  simp only [CollatzResearch.WordTrace]
  refine ⟨125650566709248411704481817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167534088945664548939309089 125650566709248411704481817)
  ·
    refine ⟨94237925031936308778361363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125650566709248411704481817 94237925031936308778361363)
    ·
      refine ⟨141356887547904463167542045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94237925031936308778361363 141356887547904463167542045)
      ·
        refine ⟨53008832830464173687828267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141356887547904463167542045 53008832830464173687828267)
        ·
          refine ⟨79513249245696260531742401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53008832830464173687828267 79513249245696260531742401)
          ·
            refine ⟨59634936934272195398806801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79513249245696260531742401 59634936934272195398806801)
            ·
              refine ⟨44726202700704146549105101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59634936934272195398806801 44726202700704146549105101)
              ·
                refine ⟨16772326012764054955914413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44726202700704146549105101 16772326012764054955914413)
                ·
                  refine ⟨6289622254786520608467905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16772326012764054955914413 6289622254786520608467905)
                  ·
                    refine ⟨4717216691089890456350929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6289622254786520608467905 4717216691089890456350929)
                    ·
                      refine ⟨3537912518317417842263197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4717216691089890456350929 3537912518317417842263197)
                      ·
                        rfl

theorem cell23_6890060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 3, 2, 2].length) (baseStart_6890060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6890060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6890060 prefixEnd_6890060 := by exact prefixLift 6890060
  have htrace : WordTrace (prefixWord ++ tailWord_6890060) baseStart_6890060 baseEnd_6890060 := by
    simpa [prefixWord, tailWord_6890060, baseEnd_6890060] using wordTrace_append hprefix tailTrace_6890060
  have hstable : (prefixWord ++ tailWord_6890060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6890060).length < 2 ^ (prefixWord ++ tailWord_6890060).sum := by decide
  have hdescent : baseEnd_6890060 < baseStart_6890060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6890060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6890094 : List Nat := [4, 1, 2, 2, 2, 1, 1, 5, 1, 2, 2]
def baseStart_6890094 : Nat := 118140960795 + 6890094 * 2 ^ 59
def prefixEnd_6890094 : Nat := 4983230072969 + 3 ^ 40 * 6890094 * 2
def baseEnd_6890094 : Nat := 3537929976659670709238041

theorem tailTrace_6890094 : CollatzResearch.WordTrace tailWord_6890094 prefixEnd_6890094 3537929976659670709238041 := by
  unfold tailWord_6890094
  simp only [CollatzResearch.WordTrace]
  refine ⟨31412796687546705901962667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167534915666915764810467557 31412796687546705901962667)
  ·
    refine ⟨47119195031320058852944001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31412796687546705901962667 47119195031320058852944001)
    ·
      refine ⟨35339396273490044139708001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47119195031320058852944001 35339396273490044139708001)
      ·
        refine ⟨26504547205117533104781001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35339396273490044139708001 26504547205117533104781001)
        ·
          refine ⟨19878410403838149828585751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26504547205117533104781001 19878410403838149828585751)
          ·
            refine ⟨29817615605757224742878627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19878410403838149828585751 29817615605757224742878627)
            ·
              refine ⟨44726423408635837114317941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29817615605757224742878627 44726423408635837114317941)
              ·
                refine ⟨4193102194559609729467307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44726423408635837114317941 4193102194559609729467307)
                ·
                  refine ⟨6289653291839414594200961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4193102194559609729467307 6289653291839414594200961)
                  ·
                    refine ⟨4717239968879560945650721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6289653291839414594200961 4717239968879560945650721)
                    ·
                      refine ⟨3537929976659670709238041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4717239968879560945650721 3537929976659670709238041)
                      ·
                        rfl

theorem cell23_6890094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_6890094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6890094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6890094 prefixEnd_6890094 := by exact prefixLift 6890094
  have htrace : WordTrace (prefixWord ++ tailWord_6890094) baseStart_6890094 baseEnd_6890094 := by
    simpa [prefixWord, tailWord_6890094, baseEnd_6890094] using wordTrace_append hprefix tailTrace_6890094
  have hstable : (prefixWord ++ tailWord_6890094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6890094).length < 2 ^ (prefixWord ++ tailWord_6890094).sum := by decide
  have hdescent : baseEnd_6890094 < baseStart_6890094 := by decide
  rcases family_descends (prefixWord ++ tailWord_6890094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6890114 : List Nat := [3, 4, 3, 1, 1, 1, 1, 2, 1, 1, 5]
def baseStart_6890114 : Nat := 118140960795 + 6890114 * 2 ^ 59
def prefixEnd_6890114 : Nat := 4983230072969 + 3 ^ 40 * 6890114 * 2
def baseEnd_6890114 : Nat := 3537940246272760630987949

theorem tailTrace_6890114 : CollatzResearch.WordTrace tailWord_6890114 prefixEnd_6890114 3537940246272760630987949 := by
  unfold tailWord_6890114
  simp only [CollatzResearch.WordTrace]
  refine ⟨62825775740075297657857349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167535401973534127087619597 62825775740075297657857349)
  ·
    refine ⟨11779832951264118310848253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62825775740075297657857349 11779832951264118310848253)
    ·
      refine ⟨4417437356724044366568095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11779832951264118310848253 4417437356724044366568095)
      ·
        refine ⟨6626156035086066549852143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4417437356724044366568095 6626156035086066549852143)
        ·
          refine ⟨9939234052629099824778215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6626156035086066549852143 9939234052629099824778215)
          ·
            refine ⟨14908851078943649737167323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9939234052629099824778215 14908851078943649737167323)
            ·
              refine ⟨22363276618415474605750985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14908851078943649737167323 22363276618415474605750985)
              ·
                refine ⟨16772457463811605954313239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22363276618415474605750985 16772457463811605954313239)
                ·
                  refine ⟨25158686195717408931469859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16772457463811605954313239 25158686195717408931469859)
                  ·
                    refine ⟨37738029293576113397204789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25158686195717408931469859 37738029293576113397204789)
                    ·
                      refine ⟨3537940246272760630987949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37738029293576113397204789 3537940246272760630987949)
                      ·
                        rfl

theorem cell23_6890114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_6890114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6890114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6890114 prefixEnd_6890114 := by exact prefixLift 6890114
  have htrace : WordTrace (prefixWord ++ tailWord_6890114) baseStart_6890114 baseEnd_6890114 := by
    simpa [prefixWord, tailWord_6890114, baseEnd_6890114] using wordTrace_append hprefix tailTrace_6890114
  have hstable : (prefixWord ++ tailWord_6890114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6890114).length < 2 ^ (prefixWord ++ tailWord_6890114).sum := by decide
  have hdescent : baseEnd_6890114 < baseStart_6890114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6890114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6890173 : List Nat := [1, 4, 1, 2, 1, 3, 3, 1, 7]
def baseStart_6890173 : Nat := 118140960795 + 6890173 * 2 ^ 59
def prefixEnd_6890173 : Nat := 4983230072969 + 3 ^ 40 * 6890173 * 2
def baseEnd_6890173 : Nat := 393107837959041766683353

theorem tailTrace_6890173 : CollatzResearch.WordTrace tailWord_6890173 prefixEnd_6890173 393107837959041766683353 := by
  unfold tailWord_6890173
  simp only [CollatzResearch.WordTrace]
  refine ⟨251305254867087443707827173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167536836578058295805218115 251305254867087443707827173)
  ·
    refine ⟨47119735287578895695217595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 251305254867087443707827173 47119735287578895695217595)
    ·
      refine ⟨70679602931368343542826393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47119735287578895695217595 70679602931368343542826393)
      ·
        refine ⟨53009702198526257657119795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70679602931368343542826393 53009702198526257657119795)
        ·
          refine ⟨79514553297789386485679693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53009702198526257657119795 79514553297789386485679693)
          ·
            refine ⟨29817957486671019932129885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79514553297789386485679693 29817957486671019932129885)
            ·
              refine ⟨11181734057501632474548707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29817957486671019932129885 11181734057501632474548707)
              ·
                refine ⟨16772601086252448711823061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11181734057501632474548707 16772601086252448711823061)
                ·
                  refine ⟨393107837959041766683353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16772601086252448711823061 393107837959041766683353)
                  ·
                    rfl

theorem cell23_6890173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 7].length) (baseStart_6890173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6890173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6890173 prefixEnd_6890173 := by exact prefixLift 6890173
  have htrace : WordTrace (prefixWord ++ tailWord_6890173) baseStart_6890173 baseEnd_6890173 := by
    simpa [prefixWord, tailWord_6890173, baseEnd_6890173] using wordTrace_append hprefix tailTrace_6890173
  have hstable : (prefixWord ++ tailWord_6890173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6890173).length < 2 ^ (prefixWord ++ tailWord_6890173).sum := by decide
  have hdescent : baseEnd_6890173 < baseStart_6890173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6890173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6890184 : List Nat := [2, 1, 3, 1, 2, 3, 4, 1, 2, 2, 2]
def baseStart_6890184 : Nat := 118140960795 + 6890184 * 2 ^ 59
def prefixEnd_6890184 : Nat := 4983230072969 + 3 ^ 40 * 6890184 * 2
def baseEnd_6890184 : Nat := 3537976189918575357112627

theorem tailTrace_6890184 : CollatzResearch.WordTrace tailWord_6890184 prefixEnd_6890184 3537976189918575357112627 := by
  unfold tailWord_6890184
  simp only [CollatzResearch.WordTrace]
  refine ⟨125652828035023796293238803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167537104046698395057651737 125652828035023796293238803)
  ·
    refine ⟨188479242052535694439858205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125652828035023796293238803 188479242052535694439858205)
    ·
      refine ⟨70679715769700885414946827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188479242052535694439858205 70679715769700885414946827)
      ·
        refine ⟨106019573654551328122420241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70679715769700885414946827 106019573654551328122420241)
        ·
          refine ⟨79514680240913496091815181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106019573654551328122420241 79514680240913496091815181)
          ·
            refine ⟨29818005090342561034430693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79514680240913496091815181 29818005090342561034430693)
            ·
              refine ⟨5590875954439230193955755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29818005090342561034430693 5590875954439230193955755)
              ·
                refine ⟨8386313931658845290933633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5590875954439230193955755 8386313931658845290933633)
                ·
                  refine ⟨6289735448744133968200225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8386313931658845290933633 6289735448744133968200225)
                  ·
                    refine ⟨4717301586558100476150169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6289735448744133968200225 4717301586558100476150169)
                    ·
                      refine ⟨3537976189918575357112627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4717301586558100476150169 3537976189918575357112627)
                      ·
                        rfl

theorem cell23_6890184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 1, 2, 2, 2].length) (baseStart_6890184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6890184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6890184 prefixEnd_6890184 := by exact prefixLift 6890184
  have htrace : WordTrace (prefixWord ++ tailWord_6890184) baseStart_6890184 baseEnd_6890184 := by
    simpa [prefixWord, tailWord_6890184, baseEnd_6890184] using wordTrace_append hprefix tailTrace_6890184
  have hstable : (prefixWord ++ tailWord_6890184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6890184).length < 2 ^ (prefixWord ++ tailWord_6890184).sum := by decide
  have hdescent : baseEnd_6890184 < baseStart_6890184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6890184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6890213 : List Nat := [1, 3, 1, 4, 1, 2, 1, 2, 1, 2, 5]
def baseStart_6890213 : Nat := 118140960795 + 6890213 * 2 ^ 59
def prefixEnd_6890213 : Nat := 4983230072969 + 3 ^ 40 * 6890213 * 2
def baseEnd_6890213 : Nat := 3537991080857555743649993

theorem tailTrace_6890213 : CollatzResearch.WordTrace tailWord_6890213 prefixEnd_6890213 3537991080857555743649993 := by
  unfold tailWord_6890213
  simp only [CollatzResearch.WordTrace]
  refine ⟨251306713786942530539283293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167537809191295020359522195 251306713786942530539283293)
  ·
    refine ⟨94240017670103448952231235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251306713786942530539283293 94240017670103448952231235)
    ·
      refine ⟨141360026505155173428346853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94240017670103448952231235 141360026505155173428346853)
      ·
        refine ⟨26505004969716595017815035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141360026505155173428346853 26505004969716595017815035)
        ·
          refine ⟨39757507454574892526722553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26505004969716595017815035 39757507454574892526722553)
          ·
            refine ⟨29818130590931169395041915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39757507454574892526722553 29818130590931169395041915)
            ·
              refine ⟨44727195886396754092562873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29818130590931169395041915 44727195886396754092562873)
              ·
                refine ⟨33545396914797565569422155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44727195886396754092562873 33545396914797565569422155)
                ·
                  refine ⟨50318095372196348354133233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33545396914797565569422155 50318095372196348354133233)
                  ·
                    refine ⟨37738571529147261265599925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50318095372196348354133233 37738571529147261265599925)
                    ·
                      refine ⟨3537991080857555743649993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37738571529147261265599925 3537991080857555743649993)
                      ·
                        rfl

theorem cell23_6890213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_6890213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6890213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6890213 prefixEnd_6890213 := by exact prefixLift 6890213
  have htrace : WordTrace (prefixWord ++ tailWord_6890213) baseStart_6890213 baseEnd_6890213 := by
    simpa [prefixWord, tailWord_6890213, baseEnd_6890213] using wordTrace_append hprefix tailTrace_6890213
  have hstable : (prefixWord ++ tailWord_6890213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6890213).length < 2 ^ (prefixWord ++ tailWord_6890213).sum := by decide
  have hdescent : baseEnd_6890213 < baseStart_6890213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6890213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6890233 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 7, 4]
def baseStart_6890233 : Nat := 118140960795 + 6890233 * 2 ^ 59
def prefixEnd_6890233 : Nat := 4983230072969 + 3 ^ 40 * 6890233 * 2
def baseEnd_6890233 : Nat := 1179333783490215221799967

theorem tailTrace_6890233 : CollatzResearch.WordTrace tailWord_6890233 prefixEnd_6890233 1179333783490215221799967 := by
  unfold tailWord_6890233
  simp only [CollatzResearch.WordTrace]
  refine ⟨251307443246870073955011353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167538295497913382636674235 251307443246870073955011353)
  ·
    refine ⟨188480582435152555466258515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251307443246870073955011353 188480582435152555466258515)
    ·
      refine ⟨282720873652728833199387773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188480582435152555466258515 282720873652728833199387773)
      ·
        refine ⟨106020327619773312449770415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282720873652728833199387773 106020327619773312449770415)
        ·
          refine ⟨159030491429659968674655623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106020327619773312449770415 159030491429659968674655623)
          ·
            refine ⟨238545737144489953011983435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159030491429659968674655623 238545737144489953011983435)
            ·
              refine ⟨357818605716734929517975153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238545737144489953011983435 357818605716734929517975153)
              ·
                refine ⟨268363954287551197138481365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 357818605716734929517975153 268363954287551197138481365)
                ·
                  refine ⟨6289780178614481182933157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 268363954287551197138481365 6289780178614481182933157)
                  ·
                    refine ⟨1179333783490215221799967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6289780178614481182933157 1179333783490215221799967)
                    ·
                      rfl

theorem cell23_6890233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 7, 4].length) (baseStart_6890233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6890233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6890233 prefixEnd_6890233 := by exact prefixLift 6890233
  have htrace : WordTrace (prefixWord ++ tailWord_6890233) baseStart_6890233 baseEnd_6890233 := by
    simpa [prefixWord, tailWord_6890233, baseEnd_6890233] using wordTrace_append hprefix tailTrace_6890233
  have hstable : (prefixWord ++ tailWord_6890233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6890233).length < 2 ^ (prefixWord ++ tailWord_6890233).sum := by decide
  have hdescent : baseEnd_6890233 < baseStart_6890233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6890233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6890243 : List Nat := [1, 1, 1, 3, 2, 2, 1, 4, 1, 4, 3]
def baseStart_6890243 : Nat := 118140960795 + 6890243 * 2 ^ 59
def prefixEnd_6890243 : Nat := 4983230072969 + 3 ^ 40 * 6890243 * 2
def baseEnd_6890243 : Nat := 3538006485277190626274855

theorem tailTrace_6890243 : CollatzResearch.WordTrace tailWord_6890243 prefixEnd_6890243 3538006485277190626274855 := by
  unfold tailWord_6890243
  simp only [CollatzResearch.WordTrace]
  refine ⟨251307807976833845662875383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167538538651222563775250255 251307807976833845662875383)
  ·
    refine ⟨376961711965250768494313075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251307807976833845662875383 376961711965250768494313075)
    ·
      refine ⟨565442567947876152741469613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376961711965250768494313075 565442567947876152741469613)
      ·
        refine ⟨212040962980453557278051105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 565442567947876152741469613 212040962980453557278051105)
        ·
          refine ⟨159030722235340167958538329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212040962980453557278051105 159030722235340167958538329)
          ·
            refine ⟨119273041676505125968903747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159030722235340167958538329 119273041676505125968903747)
            ·
              refine ⟨178909562514757688953355621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119273041676505125968903747 178909562514757688953355621)
              ·
                refine ⟨33545542971517066678754179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 178909562514757688953355621 33545542971517066678754179)
                ·
                  refine ⟨50318314457275600018131269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33545542971517066678754179 50318314457275600018131269)
                  ·
                    refine ⟨9434683960739175003399613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50318314457275600018131269 9434683960739175003399613)
                    ·
                      refine ⟨3538006485277190626274855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9434683960739175003399613 3538006485277190626274855)
                      ·
                        rfl

theorem cell23_6890243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 4, 3].length) (baseStart_6890243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6890243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6890243 prefixEnd_6890243 := by exact prefixLift 6890243
  have htrace : WordTrace (prefixWord ++ tailWord_6890243) baseStart_6890243 baseEnd_6890243 := by
    simpa [prefixWord, tailWord_6890243, baseEnd_6890243] using wordTrace_append hprefix tailTrace_6890243
  have hstable : (prefixWord ++ tailWord_6890243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6890243).length < 2 ^ (prefixWord ++ tailWord_6890243).sum := by decide
  have hdescent : baseEnd_6890243 < baseStart_6890243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6890243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6890250 : List Nat := [3, 1, 2, 2, 1, 2, 3, 2, 3, 4]
def baseStart_6890250 : Nat := 118140960795 + 6890250 * 2 ^ 59
def prefixEnd_6890250 : Nat := 4983230072969 + 3 ^ 40 * 6890250 * 2
def baseEnd_6890250 : Nat := 1179336693213924032962441

theorem tailTrace_6890250 : CollatzResearch.WordTrace tailWord_6890250 prefixEnd_6890250 1179336693213924032962441 := by
  unfold tailWord_6890250
  simp only [CollatzResearch.WordTrace]
  refine ⟨62827015821952121464595051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167538708858538990572253469 62827015821952121464595051)
  ·
    refine ⟨94240523732928182196892577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62827015821952121464595051 94240523732928182196892577)
    ·
      refine ⟨70680392799696136647669433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94240523732928182196892577 70680392799696136647669433)
      ·
        refine ⟨53010294599772102485752075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70680392799696136647669433 53010294599772102485752075)
        ·
          refine ⟨79515441899658153728628113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53010294599772102485752075 79515441899658153728628113)
          ·
            refine ⟨59636581424743615296471085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79515441899658153728628113 59636581424743615296471085)
            ·
              refine ⟨22363718034278855736176657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59636581424743615296471085 22363718034278855736176657)
              ·
                refine ⟨16772788525709141802132493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22363718034278855736176657 16772788525709141802132493)
                ·
                  refine ⟨6289795697140928175799685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16772788525709141802132493 6289795697140928175799685)
                  ·
                    refine ⟨1179336693213924032962441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6289795697140928175799685 1179336693213924032962441)
                    ·
                      rfl

theorem cell23_6890250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 3, 4].length) (baseStart_6890250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6890250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6890250 prefixEnd_6890250 := by exact prefixLift 6890250
  have htrace : WordTrace (prefixWord ++ tailWord_6890250) baseStart_6890250 baseEnd_6890250 := by
    simpa [prefixWord, tailWord_6890250, baseEnd_6890250] using wordTrace_append hprefix tailTrace_6890250
  have hstable : (prefixWord ++ tailWord_6890250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6890250).length < 2 ^ (prefixWord ++ tailWord_6890250).sum := by decide
  have hdescent : baseEnd_6890250 < baseStart_6890250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6890250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6890323 : List Nat := [1, 1, 1, 2, 1, 1, 3, 6, 1, 6]
def baseStart_6890323 : Nat := 118140960795 + 6890323 * 2 ^ 59
def prefixEnd_6890323 : Nat := 4983230072969 + 3 ^ 40 * 6890323 * 2
def baseEnd_6890323 : Nat := 1179349187909850104424829

theorem tailTrace_6890323 : CollatzResearch.WordTrace tailWord_6890323 prefixEnd_6890323 1179349187909850104424829 := by
  unfold tailWord_6890323
  simp only [CollatzResearch.WordTrace]
  refine ⟨251310725816544019325787623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167540483877696012883858415 251310725816544019325787623)
  ·
    refine ⟨376966088724816028988681435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251310725816544019325787623 376966088724816028988681435)
    ·
      refine ⟨565449133087224043483022153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376966088724816028988681435 565449133087224043483022153)
      ·
        refine ⟨424086849815418032612266615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 565449133087224043483022153 424086849815418032612266615)
        ·
          refine ⟨636130274723127048918399923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424086849815418032612266615 636130274723127048918399923)
          ·
            refine ⟨954195412084690573377599885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 636130274723127048918399923 954195412084690573377599885)
            ·
              refine ⟨357823279531758965016599957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 954195412084690573377599885 357823279531758965016599957)
              ·
                refine ⟨16772966228051201485153123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 357823279531758965016599957 16772966228051201485153123)
                ·
                  refine ⟨25159449342076802227729685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16772966228051201485153123 25159449342076802227729685)
                  ·
                    refine ⟨1179349187909850104424829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25159449342076802227729685 1179349187909850104424829)
                    ·
                      rfl

theorem cell23_6890323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 6].length) (baseStart_6890323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6890323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6890323 prefixEnd_6890323 := by exact prefixLift 6890323
  have htrace : WordTrace (prefixWord ++ tailWord_6890323) baseStart_6890323 baseEnd_6890323 := by
    simpa [prefixWord, tailWord_6890323, baseEnd_6890323] using wordTrace_append hprefix tailTrace_6890323
  have hstable : (prefixWord ++ tailWord_6890323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6890323).length < 2 ^ (prefixWord ++ tailWord_6890323).sum := by decide
  have hdescent : baseEnd_6890323 < baseStart_6890323 := by decide
  rcases family_descends (prefixWord ++ tailWord_6890323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6890353 : List Nat := [1, 2, 2, 2, 1, 4, 1, 10]
def baseStart_6890353 : Nat := 118140960795 + 6890353 * 2 ^ 59
def prefixEnd_6890353 : Nat := 4983230072969 + 3 ^ 40 * 6890353 * 2
def baseEnd_6890353 : Nat := 131039369190710562811087

theorem tailTrace_6890353 : CollatzResearch.WordTrace tailWord_6890353 prefixEnd_6890353 131039369190710562811087 := by
  unfold tailWord_6890353
  simp only [CollatzResearch.WordTrace]
  refine ⟨251311820006435334449379713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167541213337623556299586475 251311820006435334449379713)
  ·
    refine ⟨188483865004826500837034785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251311820006435334449379713 188483865004826500837034785)
    ·
      refine ⟨141362898753619875627776089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188483865004826500837034785 141362898753619875627776089)
      ·
        refine ⟨106022174065214906720832067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141362898753619875627776089 106022174065214906720832067)
        ·
          refine ⟨159033261097822360081248101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106022174065214906720832067 159033261097822360081248101)
          ·
            refine ⟨29818736455841692515234019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159033261097822360081248101 29818736455841692515234019)
            ·
              refine ⟨44728104683762538772851029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29818736455841692515234019 44728104683762538772851029)
              ·
                refine ⟨131039369190710562811087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 44728104683762538772851029 131039369190710562811087)
                ·
                  rfl

theorem cell23_6890353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 10].length) (baseStart_6890353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6890353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6890353 prefixEnd_6890353 := by exact prefixLift 6890353
  have htrace : WordTrace (prefixWord ++ tailWord_6890353) baseStart_6890353 baseEnd_6890353 := by
    simpa [prefixWord, tailWord_6890353, baseEnd_6890353] using wordTrace_append hprefix tailTrace_6890353
  have hstable : (prefixWord ++ tailWord_6890353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6890353).length < 2 ^ (prefixWord ++ tailWord_6890353).sum := by decide
  have hdescent : baseEnd_6890353 < baseStart_6890353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6890353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6890367 : List Nat := [1, 1, 2, 2, 1, 1, 7, 2, 1, 2, 3]
def baseStart_6890367 : Nat := 118140960795 + 6890367 * 2 ^ 59
def prefixEnd_6890367 : Nat := 4983230072969 + 3 ^ 40 * 6890367 * 2
def baseEnd_6890367 : Nat := 3538070156878348141124285

theorem tailTrace_6890367 : CollatzResearch.WordTrace tailWord_6890367 prefixEnd_6890367 3538070156878348141124285 := by
  unfold tailWord_6890367
  simp only [CollatzResearch.WordTrace]
  refine ⟨251312330628384614840389355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167541553752256409893592903 251312330628384614840389355)
  ·
    refine ⟨376968495942576922260584033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251312330628384614840389355 376968495942576922260584033)
    ·
      refine ⟨282726371956932691695438025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376968495942576922260584033 282726371956932691695438025)
      ·
        refine ⟨212044778967699518771578519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282726371956932691695438025 212044778967699518771578519)
        ·
          refine ⟨318067168451549278157367779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212044778967699518771578519 318067168451549278157367779)
          ·
            refine ⟨477100752677323917236051669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318067168451549278157367779 477100752677323917236051669)
            ·
              refine ⟨11182048890874779310219961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 477100752677323917236051669 11182048890874779310219961)
              ·
                refine ⟨8386536668156084482664971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11182048890874779310219961 8386536668156084482664971)
                ·
                  refine ⟨12579805002234126723997457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8386536668156084482664971 12579805002234126723997457)
                  ·
                    refine ⟨9434853751675595042998093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12579805002234126723997457 9434853751675595042998093)
                    ·
                      refine ⟨3538070156878348141124285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9434853751675595042998093 3538070156878348141124285)
                      ·
                        rfl

theorem cell23_6890367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2, 1, 2, 3].length) (baseStart_6890367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6890367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6890367 prefixEnd_6890367 := by exact prefixLift 6890367
  have htrace : WordTrace (prefixWord ++ tailWord_6890367) baseStart_6890367 baseEnd_6890367 := by
    simpa [prefixWord, tailWord_6890367, baseEnd_6890367] using wordTrace_append hprefix tailTrace_6890367
  have hstable : (prefixWord ++ tailWord_6890367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6890367).length < 2 ^ (prefixWord ++ tailWord_6890367).sum := by decide
  have hdescent : baseEnd_6890367 < baseStart_6890367 := by decide
  rcases family_descends (prefixWord ++ tailWord_6890367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6890380 : List Nat := [2, 2, 1, 2, 1, 2, 3, 1, 3, 3, 3]
def baseStart_6890380 : Nat := 118140960795 + 6890380 * 2 ^ 59
def prefixEnd_6890380 : Nat := 4983230072969 + 3 ^ 40 * 6890380 * 2
def baseEnd_6890380 : Nat := 3538076832126856590261725

theorem tailTrace_6890380 : CollatzResearch.WordTrace tailWord_6890380 prefixEnd_6890380 3538076832126856590261725 := by
  unfold tailWord_6890380
  simp only [CollatzResearch.WordTrace]
  refine ⟨125656402388668759030306297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167541869851558345373741729 125656402388668759030306297)
  ·
    refine ⟨94242301791501569272729723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125656402388668759030306297 94242301791501569272729723)
    ·
      refine ⟨141363452687252353909094585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94242301791501569272729723 141363452687252353909094585)
      ·
        refine ⟨106022589515439265431820939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141363452687252353909094585 106022589515439265431820939)
        ·
          refine ⟨159033884273158898147731409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106022589515439265431820939 159033884273158898147731409)
          ·
            refine ⟨119275413204869173610798557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159033884273158898147731409 119275413204869173610798557)
            ·
              refine ⟨44728279951825940104049459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119275413204869173610798557 44728279951825940104049459)
              ·
                refine ⟨67092419927738910156074189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44728279951825940104049459 67092419927738910156074189)
                ·
                  refine ⟨25159657472902091308527821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67092419927738910156074189 25159657472902091308527821)
                  ·
                    refine ⟨9434871552338284240697933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25159657472902091308527821 9434871552338284240697933)
                    ·
                      refine ⟨3538076832126856590261725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9434871552338284240697933 3538076832126856590261725)
                      ·
                        rfl

theorem cell23_6890380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 3, 3, 3].length) (baseStart_6890380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6890380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6890380 prefixEnd_6890380 := by exact prefixLift 6890380
  have htrace : WordTrace (prefixWord ++ tailWord_6890380) baseStart_6890380 baseEnd_6890380 := by
    simpa [prefixWord, tailWord_6890380, baseEnd_6890380] using wordTrace_append hprefix tailTrace_6890380
  have hstable : (prefixWord ++ tailWord_6890380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6890380).length < 2 ^ (prefixWord ++ tailWord_6890380).sum := by decide
  have hdescent : baseEnd_6890380 < baseStart_6890380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6890380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6890430 : List Nat := [4, 2, 1, 1, 1, 2, 1, 2, 1, 8]
def baseStart_6890430 : Nat := 118140960795 + 6890430 * 2 ^ 59
def prefixEnd_6890430 : Nat := 4983230072969 + 3 ^ 40 * 6890430 * 2
def baseEnd_6890430 : Nat := 1179367502053193798212165

theorem tailTrace_6890430 : CollatzResearch.WordTrace tailWord_6890430 prefixEnd_6890430 1179367502053193798212165 := by
  unfold tailWord_6890430
  simp only [CollatzResearch.WordTrace]
  refine ⟨31414328553394547074991593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167543085618104251066621829 31414328553394547074991593)
  ·
    refine ⟨23560746415045910306243695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31414328553394547074991593 23560746415045910306243695)
    ·
      refine ⟨35341119622568865459365543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23560746415045910306243695 35341119622568865459365543)
      ·
        refine ⟨53011679433853298189048315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35341119622568865459365543 53011679433853298189048315)
        ·
          refine ⟨79517519150779947283572473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53011679433853298189048315 79517519150779947283572473)
          ·
            refine ⟨59638139363084960462679355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79517519150779947283572473 59638139363084960462679355)
            ·
              refine ⟨89457209044627440694019033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59638139363084960462679355 89457209044627440694019033)
              ·
                refine ⟨67092906783470580520514275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89457209044627440694019033 67092906783470580520514275)
                ·
                  refine ⟨100639360175205870780771413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67092906783470580520514275 100639360175205870780771413)
                  ·
                    refine ⟨1179367502053193798212165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 100639360175205870780771413 1179367502053193798212165)
                    ·
                      rfl

theorem cell23_6890430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_6890430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6890430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6890430 prefixEnd_6890430 := by exact prefixLift 6890430
  have htrace : WordTrace (prefixWord ++ tailWord_6890430) baseStart_6890430 baseEnd_6890430 := by
    simpa [prefixWord, tailWord_6890430, baseEnd_6890430] using wordTrace_append hprefix tailTrace_6890430
  have hstable : (prefixWord ++ tailWord_6890430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6890430).length < 2 ^ (prefixWord ++ tailWord_6890430).sum := by decide
  have hdescent : baseEnd_6890430 < baseStart_6890430 := by decide
  rcases family_descends (prefixWord ++ tailWord_6890430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6890471 : List Nat := [1, 1, 5, 2, 2, 3, 1, 1, 1, 4, 2]
def baseStart_6890471 : Nat := 118140960795 + 6890471 * 2 ^ 59
def prefixEnd_6890471 : Nat := 4983230072969 + 3 ^ 40 * 6890471 * 2
def baseEnd_6890471 : Nat := 3538123558866415734223807

theorem tailTrace_6890471 : CollatzResearch.WordTrace tailWord_6890471 prefixEnd_6890471 3538123558866415734223807 := by
  unfold tailWord_6890471
  simp only [CollatzResearch.WordTrace]
  refine ⟨251316123820007840602175267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167544082546671893734783511 251316123820007840602175267)
  ·
    refine ⟨376974185730011760903262901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251316123820007840602175267 376974185730011760903262901)
    ·
      refine ⟨35341329912188602584680897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 376974185730011760903262901 35341329912188602584680897)
      ·
        refine ⟨26505997434141451938510673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35341329912188602584680897 26505997434141451938510673)
        ·
          refine ⟨19879498075606088953883005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26505997434141451938510673 19879498075606088953883005)
          ·
            refine ⟨7454811778352283357706127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19879498075606088953883005 7454811778352283357706127)
            ·
              refine ⟨11182217667528425036559191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7454811778352283357706127 11182217667528425036559191)
              ·
                refine ⟨16773326501292637554838787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11182217667528425036559191 16773326501292637554838787)
                ·
                  refine ⟨25159989751938956332258181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16773326501292637554838787 25159989751938956332258181)
                  ·
                    refine ⟨4717498078488554312298409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25159989751938956332258181 4717498078488554312298409)
                    ·
                      refine ⟨3538123558866415734223807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4717498078488554312298409 3538123558866415734223807)
                      ·
                        rfl

theorem cell23_6890471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_6890471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6890471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6890471 prefixEnd_6890471 := by exact prefixLift 6890471
  have htrace : WordTrace (prefixWord ++ tailWord_6890471) baseStart_6890471 baseEnd_6890471 := by
    simpa [prefixWord, tailWord_6890471, baseEnd_6890471] using wordTrace_append hprefix tailTrace_6890471
  have hstable : (prefixWord ++ tailWord_6890471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6890471).length < 2 ^ (prefixWord ++ tailWord_6890471).sum := by decide
  have hdescent : baseEnd_6890471 < baseStart_6890471 := by decide
  rcases family_descends (prefixWord ++ tailWord_6890471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6890490 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 6, 5]
def baseStart_6890490 : Nat := 118140960795 + 6890490 * 2 ^ 59
def prefixEnd_6890490 : Nat := 4983230072969 + 3 ^ 40 * 6890490 * 2
def baseEnd_6890490 : Nat := 1179377771666283719962073

theorem tailTrace_6890490 : CollatzResearch.WordTrace tailWord_6890490 prefixEnd_6890490 1179377771666283719962073 := by
  unfold tailWord_6890490
  simp only [CollatzResearch.WordTrace]
  refine ⟨62829204201734751711779231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167544544537959337898077949 62829204201734751711779231)
  ·
    refine ⟨94243806302602127567668847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62829204201734751711779231 94243806302602127567668847)
    ·
      refine ⟨141365709453903191351503271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94243806302602127567668847 141365709453903191351503271)
      ·
        refine ⟨212048564180854787027254907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141365709453903191351503271 212048564180854787027254907)
        ·
          refine ⟨318072846271282180540882361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212048564180854787027254907 318072846271282180540882361)
          ·
            refine ⟨238554634703461635405661771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318072846271282180540882361 238554634703461635405661771)
            ·
              refine ⟨357831952055192453108492657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238554634703461635405661771 357831952055192453108492657)
              ·
                refine ⟨268373964041394339831369493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 357831952055192453108492657 268373964041394339831369493)
                ·
                  refine ⟨12580029564440359679595445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 268373964041394339831369493 12580029564440359679595445)
                  ·
                    refine ⟨1179377771666283719962073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12580029564440359679595445 1179377771666283719962073)
                    ·
                      rfl

theorem cell23_6890490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 6, 5].length) (baseStart_6890490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6890490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6890490 prefixEnd_6890490 := by exact prefixLift 6890490
  have htrace : WordTrace (prefixWord ++ tailWord_6890490) baseStart_6890490 baseEnd_6890490 := by
    simpa [prefixWord, tailWord_6890490, baseEnd_6890490] using wordTrace_append hprefix tailTrace_6890490
  have hstable : (prefixWord ++ tailWord_6890490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6890490).length < 2 ^ (prefixWord ++ tailWord_6890490).sum := by decide
  have hdescent : baseEnd_6890490 < baseStart_6890490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6890490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6890507 : List Nat := [1, 1, 1, 1, 6, 3, 1, 2, 2, 5]
def baseStart_6890507 : Nat := 118140960795 + 6890507 * 2 ^ 59
def prefixEnd_6890507 : Nat := 4983230072969 + 3 ^ 40 * 6890507 * 2
def baseEnd_6890507 : Nat := 1179380681389992531124547

theorem tailTrace_6890507 : CollatzResearch.WordTrace tailWord_6890507 prefixEnd_6890507 1179380681389992531124547 := by
  unfold tailWord_6890507
  simp only [CollatzResearch.WordTrace]
  refine ⟨251317436847877418750485775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167544957898584945833657183 251317436847877418750485775)
  ·
    refine ⟨376976155271816128125728663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251317436847877418750485775 376976155271816128125728663)
    ·
      refine ⟨565464232907724192188592995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376976155271816128125728663 565464232907724192188592995)
      ·
        refine ⟨848196349361586288282889493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565464232907724192188592995 848196349361586288282889493)
        ·
          refine ⟨39759203876324357263260445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 848196349361586288282889493 39759203876324357263260445)
          ·
            refine ⟨14909701453621633973722667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39759203876324357263260445 14909701453621633973722667)
            ·
              refine ⟨22364552180432450960584001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14909701453621633973722667 22364552180432450960584001)
              ·
                refine ⟨16773414135324338220438001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22364552180432450960584001 16773414135324338220438001)
                ·
                  refine ⟨12580060601493253665328501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16773414135324338220438001 12580060601493253665328501)
                  ·
                    refine ⟨1179380681389992531124547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12580060601493253665328501 1179380681389992531124547)
                    ·
                      rfl

theorem cell23_6890507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2, 5].length) (baseStart_6890507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6890507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6890507 prefixEnd_6890507 := by exact prefixLift 6890507
  have htrace : WordTrace (prefixWord ++ tailWord_6890507) baseStart_6890507 baseEnd_6890507 := by
    simpa [prefixWord, tailWord_6890507, baseEnd_6890507] using wordTrace_append hprefix tailTrace_6890507
  have hstable : (prefixWord ++ tailWord_6890507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6890507).length < 2 ^ (prefixWord ++ tailWord_6890507).sum := by decide
  have hdescent : baseEnd_6890507 < baseStart_6890507 := by decide
  rcases family_descends (prefixWord ++ tailWord_6890507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6890517 : List Nat := [1, 3, 2, 1, 4, 2, 1, 1, 1, 2, 5]
def baseStart_6890517 : Nat := 118140960795 + 6890517 * 2 ^ 59
def prefixEnd_6890517 : Nat := 4983230072969 + 3 ^ 40 * 6890517 * 2
def baseEnd_6890517 : Nat := 3538147178976522554248595

theorem tailTrace_6890517 : CollatzResearch.WordTrace tailWord_6890517 prefixEnd_6890517 3538147178976522554248595 := by
  unfold tailWord_6890517
  simp only [CollatzResearch.WordTrace]
  refine ⟨251317801577841190458349805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167545201051894126972233203 251317801577841190458349805)
  ·
    refine ⟨94244175591690446421881177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251317801577841190458349805 94244175591690446421881177)
    ·
      refine ⟨70683131693767834816410883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94244175591690446421881177 70683131693767834816410883)
      ·
        refine ⟨106024697540651752224616325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70683131693767834816410883 106024697540651752224616325)
        ·
          refine ⟨19879630788872203542115561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106024697540651752224616325 19879630788872203542115561)
          ·
            refine ⟨14909723091654152656586671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19879630788872203542115561 14909723091654152656586671)
            ·
              refine ⟨22364584637481228984880007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14909723091654152656586671 22364584637481228984880007)
              ·
                refine ⟨33546876956221843477320011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22364584637481228984880007 33546876956221843477320011)
                ·
                  refine ⟨50320315434332765215980017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33546876956221843477320011 50320315434332765215980017)
                  ·
                    refine ⟨37740236575749573911985013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50320315434332765215980017 37740236575749573911985013)
                    ·
                      refine ⟨3538147178976522554248595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37740236575749573911985013 3538147178976522554248595)
                      ·
                        rfl

theorem cell23_6890517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_6890517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6890517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6890517 prefixEnd_6890517 := by exact prefixLift 6890517
  have htrace : WordTrace (prefixWord ++ tailWord_6890517) baseStart_6890517 baseEnd_6890517 := by
    simpa [prefixWord, tailWord_6890517, baseEnd_6890517] using wordTrace_append hprefix tailTrace_6890517
  have hstable : (prefixWord ++ tailWord_6890517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6890517).length < 2 ^ (prefixWord ++ tailWord_6890517).sum := by decide
  have hdescent : baseEnd_6890517 < baseStart_6890517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6890517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6890567 : List Nat := [1, 1, 4, 1, 3, 2, 1, 4, 6]
def baseStart_6890567 : Nat := 118140960795 + 6890567 * 2 ^ 59
def prefixEnd_6890567 : Nat := 4983230072969 + 3 ^ 40 * 6890567 * 2
def baseEnd_6890567 : Nat := 393130317001027484291485

theorem tailTrace_6890567 : CollatzResearch.WordTrace tailWord_6890567 prefixEnd_6890567 393130317001027484291485 := by
  unfold tailWord_6890567
  simp only [CollatzResearch.WordTrace]
  refine ⟨251319625227660048997669955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167546416818440032665113303 251319625227660048997669955)
  ·
    refine ⟨376979437841490073496504933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251319625227660048997669955 376979437841490073496504933)
    ·
      refine ⟨70683644595279388780594675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 376979437841490073496504933 70683644595279388780594675)
      ·
        refine ⟨106025466892919083170892013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70683644595279388780594675 106025466892919083170892013)
        ·
          refine ⟨39759550084844656189084505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106025466892919083170892013 39759550084844656189084505)
          ·
            refine ⟨29819662563633492141813379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39759550084844656189084505 29819662563633492141813379)
            ·
              refine ⟨44729493845450238212720069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29819662563633492141813379 44729493845450238212720069)
              ·
                refine ⟨8386780096021919664885013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44729493845450238212720069 8386780096021919664885013)
                ·
                  refine ⟨393130317001027484291485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8386780096021919664885013 393130317001027484291485)
                  ·
                    rfl

theorem cell23_6890567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4, 6].length) (baseStart_6890567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6890567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6890567 prefixEnd_6890567 := by exact prefixLift 6890567
  have htrace : WordTrace (prefixWord ++ tailWord_6890567) baseStart_6890567 baseEnd_6890567 := by
    simpa [prefixWord, tailWord_6890567, baseEnd_6890567] using wordTrace_append hprefix tailTrace_6890567
  have hstable : (prefixWord ++ tailWord_6890567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6890567).length < 2 ^ (prefixWord ++ tailWord_6890567).sum := by decide
  have hdescent : baseEnd_6890567 < baseStart_6890567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6890567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6890597 : List Nat := [1, 3, 1, 3, 2, 1, 1, 3, 3, 5]
def baseStart_6890597 : Nat := 118140960795 + 6890597 * 2 ^ 59
def prefixEnd_6890597 : Nat := 4983230072969 + 3 ^ 40 * 6890597 * 2
def baseEnd_6890597 : Nat := 1179396085809627413749409

theorem tailTrace_6890597 : CollatzResearch.WordTrace tailWord_6890597 prefixEnd_6890597 1179396085809627413749409 := by
  unfold tailWord_6890597
  simp only [CollatzResearch.WordTrace]
  refine ⟨251320719417551364121262045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167547146278367576080841363 251320719417551364121262045)
  ·
    refine ⟨94245269781581761545473267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251320719417551364121262045 94245269781581761545473267)
    ·
      refine ⟨141367904672372642318209901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94245269781581761545473267 141367904672372642318209901)
      ·
        refine ⟨53012964252139740869328713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141367904672372642318209901 53012964252139740869328713)
        ·
          refine ⟨39759723189104805651996535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53012964252139740869328713 39759723189104805651996535)
          ·
            refine ⟨59639584783657208477994803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39759723189104805651996535 59639584783657208477994803)
            ·
              refine ⟨89459377175485812716992205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59639584783657208477994803 89459377175485812716992205)
              ·
                refine ⟨33547266440807179768872077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89459377175485812716992205 33547266440807179768872077)
                ·
                  refine ⟨12580224915302692413327029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33547266440807179768872077 12580224915302692413327029)
                  ·
                    refine ⟨1179396085809627413749409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12580224915302692413327029 1179396085809627413749409)
                    ·
                      rfl

theorem cell23_6890597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 5].length) (baseStart_6890597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6890597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6890597 prefixEnd_6890597 := by exact prefixLift 6890597
  have htrace : WordTrace (prefixWord ++ tailWord_6890597) baseStart_6890597 baseEnd_6890597 := by
    simpa [prefixWord, tailWord_6890597, baseEnd_6890597] using wordTrace_append hprefix tailTrace_6890597
  have hstable : (prefixWord ++ tailWord_6890597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6890597).length < 2 ^ (prefixWord ++ tailWord_6890597).sum := by decide
  have hdescent : baseEnd_6890597 < baseStart_6890597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6890597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6890604 : List Nat := [2, 2, 1, 1, 3, 2, 3, 1, 1, 5, 2]
def baseStart_6890604 : Nat := 118140960795 + 6890604 * 2 ^ 59
def prefixEnd_6890604 : Nat := 4983230072969 + 3 ^ 40 * 6890604 * 2
def baseEnd_6890604 : Nat := 3538191851793463713860695

theorem tailTrace_6890604 : CollatzResearch.WordTrace tailWord_6890604 prefixEnd_6890604 3538191851793463713860695 := by
  unfold tailWord_6890604
  simp only [CollatzResearch.WordTrace]
  refine ⟨125660487364263002158383433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167547316485684002877844577 125660487364263002158383433)
  ·
    refine ⟨94245365523197251618787575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125660487364263002158383433 94245365523197251618787575)
    ·
      refine ⟨141368048284795877428181363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94245365523197251618787575 141368048284795877428181363)
      ·
        refine ⟨212052072427193816142272045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141368048284795877428181363 212052072427193816142272045)
        ·
          refine ⟨79519527160197681053352017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212052072427193816142272045 79519527160197681053352017)
          ·
            refine ⟨59639645370148260790014013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79519527160197681053352017 59639645370148260790014013)
            ·
              refine ⟨22364867013805597796255255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59639645370148260790014013 22364867013805597796255255)
              ·
                refine ⟨33547300520708396694382883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22364867013805597796255255 33547300520708396694382883)
                ·
                  refine ⟨50320950781062595041574325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33547300520708396694382883 50320950781062595041574325)
                  ·
                    refine ⟨4717589135724618285147593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50320950781062595041574325 4717589135724618285147593)
                    ·
                      refine ⟨3538191851793463713860695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4717589135724618285147593 3538191851793463713860695)
                      ·
                        rfl

theorem cell23_6890604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 5, 2].length) (baseStart_6890604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6890604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6890604 prefixEnd_6890604 := by exact prefixLift 6890604
  have htrace : WordTrace (prefixWord ++ tailWord_6890604) baseStart_6890604 baseEnd_6890604 := by
    simpa [prefixWord, tailWord_6890604, baseEnd_6890604] using wordTrace_append hprefix tailTrace_6890604
  have hstable : (prefixWord ++ tailWord_6890604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6890604).length < 2 ^ (prefixWord ++ tailWord_6890604).sum := by decide
  have hdescent : baseEnd_6890604 < baseStart_6890604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6890604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6890628 : List Nat := [2, 3, 2, 1, 2, 2, 2, 4, 1, 1, 3]
def baseStart_6890628 : Nat := 118140960795 + 6890628 * 2 ^ 59
def prefixEnd_6890628 : Nat := 4983230072969 + 3 ^ 40 * 6890628 * 2
def baseEnd_6890628 : Nat := 3538204175329171619960585

theorem tailTrace_6890628 : CollatzResearch.WordTrace tailWord_6890628 prefixEnd_6890628 3538204175329171619960585 := by
  unfold tailWord_6890628
  simp only [CollatzResearch.WordTrace]
  refine ⟨125660925040219528207820269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167547900053626037610427025 125660925040219528207820269)
  ·
    refine ⟨47122846890082323077932601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125660925040219528207820269 47122846890082323077932601)
    ·
      refine ⟨35342135167561742308449451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47122846890082323077932601 35342135167561742308449451)
      ·
        refine ⟨53013202751342613462674177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35342135167561742308449451 53013202751342613462674177)
        ·
          refine ⟨39759902063506960097005633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53013202751342613462674177 39759902063506960097005633)
          ·
            refine ⟨29819926547630220072754225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39759902063506960097005633 29819926547630220072754225)
            ·
              refine ⟨22364944910722665054565669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29819926547630220072754225 22364944910722665054565669)
              ·
                refine ⟨4193427170760499697731063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22364944910722665054565669 4193427170760499697731063)
                ·
                  refine ⟨6290140756140749546596595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4193427170760499697731063 6290140756140749546596595)
                  ·
                    refine ⟨9435211134211124319894893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6290140756140749546596595 9435211134211124319894893)
                    ·
                      refine ⟨3538204175329171619960585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9435211134211124319894893 3538204175329171619960585)
                      ·
                        rfl

theorem cell23_6890628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 4, 1, 1, 3].length) (baseStart_6890628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6890628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6890628 prefixEnd_6890628 := by exact prefixLift 6890628
  have htrace : WordTrace (prefixWord ++ tailWord_6890628) baseStart_6890628 baseEnd_6890628 := by
    simpa [prefixWord, tailWord_6890628, baseEnd_6890628] using wordTrace_append hprefix tailTrace_6890628
  have hstable : (prefixWord ++ tailWord_6890628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6890628).length < 2 ^ (prefixWord ++ tailWord_6890628).sum := by decide
  have hdescent : baseEnd_6890628 < baseStart_6890628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6890628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6890657 : List Nat := [1, 2, 3, 3, 1, 1, 3, 9]
def baseStart_6890657 : Nat := 118140960795 + 6890657 * 2 ^ 59
def prefixEnd_6890657 : Nat := 4983230072969 + 3 ^ 40 * 6890657 * 2
def baseEnd_6890657 : Nat := 131045150602524148388813

theorem tailTrace_6890657 : CollatzResearch.WordTrace tailWord_6890657 prefixEnd_6890657 131045150602524148388813 := by
  unfold tailWord_6890657
  simp only [CollatzResearch.WordTrace]
  refine ⟨251322907797333994368446225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167548605198222662912297483 251322907797333994368446225)
  ·
    refine ⟨188492180848000495776334669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251322907797333994368446225 188492180848000495776334669)
    ·
      refine ⟨70684567818000185916125501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188492180848000495776334669 70684567818000185916125501)
      ·
        refine ⟨26506712931750069718547063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70684567818000185916125501 26506712931750069718547063)
        ·
          refine ⟨39760069397625104577820595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26506712931750069718547063 39760069397625104577820595)
          ·
            refine ⟨59640104096437656866730893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39760069397625104577820595 59640104096437656866730893)
            ·
              refine ⟨22365039036164121325024085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59640104096437656866730893 22365039036164121325024085)
              ·
                refine ⟨131045150602524148388813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22365039036164121325024085 131045150602524148388813)
                ·
                  rfl

theorem cell23_6890657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 9].length) (baseStart_6890657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6890657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6890657 prefixEnd_6890657 := by exact prefixLift 6890657
  have htrace : WordTrace (prefixWord ++ tailWord_6890657) baseStart_6890657 baseEnd_6890657 := by
    simpa [prefixWord, tailWord_6890657, baseEnd_6890657] using wordTrace_append hprefix tailTrace_6890657
  have hstable : (prefixWord ++ tailWord_6890657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6890657).length < 2 ^ (prefixWord ++ tailWord_6890657).sum := by decide
  have hdescent : baseEnd_6890657 < baseStart_6890657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6890657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6890668 : List Nat := [2, 2, 1, 1, 1, 1, 1, 9, 1, 2, 2]
def baseStart_6890668 : Nat := 118140960795 + 6890668 * 2 ^ 59
def prefixEnd_6890668 : Nat := 4983230072969 + 3 ^ 40 * 6890668 * 2
def baseEnd_6890668 : Nat := 3538224714555351463460401

theorem tailTrace_6890668 : CollatzResearch.WordTrace tailWord_6890668 prefixEnd_6890668 3538224714555351463460401 := by
  unfold tailWord_6890668
  simp only [CollatzResearch.WordTrace]
  refine ⟨125661654500147071623548329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167548872666862762164731105 125661654500147071623548329)
  ·
    refine ⟨94246240875110303717661247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125661654500147071623548329 94246240875110303717661247)
    ·
      refine ⟨141369361312665455576491871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94246240875110303717661247 141369361312665455576491871)
      ·
        refine ⟨212054041968998183364737807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141369361312665455576491871 212054041968998183364737807)
        ·
          refine ⟨318081062953497275047106711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212054041968998183364737807 318081062953497275047106711)
          ·
            refine ⟨477121594430245912570660067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318081062953497275047106711 477121594430245912570660067)
            ·
              refine ⟨715682391645368868855990101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 477121594430245912570660067 715682391645368868855990101)
              ·
                refine ⟨4193451513547083215953067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 715682391645368868855990101 4193451513547083215953067)
                ·
                  refine ⟨6290177270320624823929601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4193451513547083215953067 6290177270320624823929601)
                  ·
                    refine ⟨4717632952740468617947201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6290177270320624823929601 4717632952740468617947201)
                    ·
                      refine ⟨3538224714555351463460401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4717632952740468617947201 3538224714555351463460401)
                      ·
                        rfl

theorem cell23_6890668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 9, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 9, 1, 2, 2].length) (baseStart_6890668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6890668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6890668 prefixEnd_6890668 := by exact prefixLift 6890668
  have htrace : WordTrace (prefixWord ++ tailWord_6890668) baseStart_6890668 baseEnd_6890668 := by
    simpa [prefixWord, tailWord_6890668, baseEnd_6890668] using wordTrace_append hprefix tailTrace_6890668
  have hstable : (prefixWord ++ tailWord_6890668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6890668).length < 2 ^ (prefixWord ++ tailWord_6890668).sum := by decide
  have hdescent : baseEnd_6890668 < baseStart_6890668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6890668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6890707 : List Nat := [1, 1, 1, 2, 1, 1, 1, 6, 2, 3, 4]
def baseStart_6890707 : Nat := 118140960795 + 6890707 * 2 ^ 59
def prefixEnd_6890707 : Nat := 4983230072969 + 3 ^ 40 * 6890707 * 2
def baseEnd_6890707 : Nat := 3538244740300876810872721

theorem tailTrace_6890707 : CollatzResearch.WordTrace tailWord_6890707 prefixEnd_6890707 3538244740300876810872721 := by
  unfold tailWord_6890707
  simp only [CollatzResearch.WordTrace]
  refine ⟨251324731447152852907766375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167549820964768568605177583 251324731447152852907766375)
  ·
    refine ⟨376987097170729279361649563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251324731447152852907766375 376987097170729279361649563)
    ·
      refine ⟨565480645756093919042474345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376987097170729279361649563 565480645756093919042474345)
      ·
        refine ⟨424110484317070439281855759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 565480645756093919042474345 424110484317070439281855759)
        ·
          refine ⟨636165726475605658922783639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424110484317070439281855759 636165726475605658922783639)
          ·
            refine ⟨954248589713408488384175459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 636165726475605658922783639 954248589713408488384175459)
            ·
              refine ⟨1431372884570112732576263189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 954248589713408488384175459 1431372884570112732576263189)
              ·
                refine ⟨67095603964224034339512337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1431372884570112732576263189 67095603964224034339512337)
                ·
                  refine ⟨50321702973168025754634253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67095603964224034339512337 50321702973168025754634253)
                  ·
                    refine ⟨18870638614938009657987845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50321702973168025754634253 18870638614938009657987845)
                    ·
                      refine ⟨3538244740300876810872721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18870638614938009657987845 3538244740300876810872721)
                      ·
                        rfl

theorem cell23_6890707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3, 4].length) (baseStart_6890707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6890707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6890707 prefixEnd_6890707 := by exact prefixLift 6890707
  have htrace : WordTrace (prefixWord ++ tailWord_6890707) baseStart_6890707 baseEnd_6890707 := by
    simpa [prefixWord, tailWord_6890707, baseEnd_6890707] using wordTrace_append hprefix tailTrace_6890707
  have hstable : (prefixWord ++ tailWord_6890707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6890707).length < 2 ^ (prefixWord ++ tailWord_6890707).sum := by decide
  have hdescent : baseEnd_6890707 < baseStart_6890707 := by decide
  rcases family_descends (prefixWord ++ tailWord_6890707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6890737 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 2, 3, 6]
def baseStart_6890737 : Nat := 118140960795 + 6890737 * 2 ^ 59
def prefixEnd_6890737 : Nat := 4983230072969 + 3 ^ 40 * 6890737 * 2
def baseEnd_6890737 : Nat := 3538260144720511693497583

theorem tailTrace_6890737 : CollatzResearch.WordTrace tailWord_6890737 prefixEnd_6890737 3538260144720511693497583 := by
  unfold tailWord_6890737
  simp only [CollatzResearch.WordTrace]
  refine ⟨251325825637044168031358465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167550550424696112020905643 251325825637044168031358465)
  ·
    refine ⟨188494369227783126023518849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251325825637044168031358465 188494369227783126023518849)
    ·
      refine ⟨141370776920837344517639137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188494369227783126023518849 141370776920837344517639137)
      ·
        refine ⟨106028082690628008388229353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141370776920837344517639137 106028082690628008388229353)
        ·
          refine ⟨79521062017971006291172015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106028082690628008388229353 79521062017971006291172015)
          ·
            refine ⟨119281593026956509436758023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79521062017971006291172015 119281593026956509436758023)
            ·
              refine ⟨178922389540434764155137035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119281593026956509436758023 178922389540434764155137035)
              ·
                refine ⟨268383584310652146232705553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178922389540434764155137035 268383584310652146232705553)
                ·
                  refine ⟨201287688232989109674529165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 268383584310652146232705553 201287688232989109674529165)
                  ·
                    refine ⟨75482883087370916127948437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 201287688232989109674529165 75482883087370916127948437)
                    ·
                      refine ⟨3538260144720511693497583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75482883087370916127948437 3538260144720511693497583)
                      ·
                        rfl

theorem cell23_6890737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_6890737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6890737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6890737 prefixEnd_6890737 := by exact prefixLift 6890737
  have htrace : WordTrace (prefixWord ++ tailWord_6890737) baseStart_6890737 baseEnd_6890737 := by
    simpa [prefixWord, tailWord_6890737, baseEnd_6890737] using wordTrace_append hprefix tailTrace_6890737
  have hstable : (prefixWord ++ tailWord_6890737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6890737).length < 2 ^ (prefixWord ++ tailWord_6890737).sum := by decide
  have hdescent : baseEnd_6890737 < baseStart_6890737 := by decide
  rcases family_descends (prefixWord ++ tailWord_6890737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6890764 : List Nat := [2, 2, 1, 2, 2, 4, 1, 2, 7]
def baseStart_6890764 : Nat := 118140960795 + 6890764 * 2 ^ 59
def prefixEnd_6890764 : Nat := 4983230072969 + 3 ^ 40 * 6890764 * 2
def baseEnd_6890764 : Nat := 393141556522020343095551

theorem tailTrace_6890764 : CollatzResearch.WordTrace tailWord_6890764 prefixEnd_6890764 393141556522020343095551 := by
  unfold tailWord_6890764
  simp only [CollatzResearch.WordTrace]
  refine ⟨125663405203973175821295673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167551206938630901095060897 125663405203973175821295673)
  ·
    refine ⟨94247553902979881865971755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125663405203973175821295673 94247553902979881865971755)
    ·
      refine ⟨141371330854469822798957633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94247553902979881865971755 141371330854469822798957633)
      ·
        refine ⟨106028498140852367099218225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141371330854469822798957633 106028498140852367099218225)
        ·
          refine ⟨79521373605639275324413669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106028498140852367099218225 79521373605639275324413669)
          ·
            refine ⟨14910257551057364123327563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79521373605639275324413669 14910257551057364123327563)
            ·
              refine ⟨22365386326586046184991345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14910257551057364123327563 22365386326586046184991345)
              ·
                refine ⟨16774039744939534638743509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22365386326586046184991345 16774039744939534638743509)
                ·
                  refine ⟨393141556522020343095551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16774039744939534638743509 393141556522020343095551)
                  ·
                    rfl

theorem cell23_6890764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 7].length) (baseStart_6890764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6890764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6890764 prefixEnd_6890764 := by exact prefixLift 6890764
  have htrace : WordTrace (prefixWord ++ tailWord_6890764) baseStart_6890764 baseEnd_6890764 := by
    simpa [prefixWord, tailWord_6890764, baseEnd_6890764] using wordTrace_append hprefix tailTrace_6890764
  have hstable : (prefixWord ++ tailWord_6890764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6890764).length < 2 ^ (prefixWord ++ tailWord_6890764).sum := by decide
  have hdescent : baseEnd_6890764 < baseStart_6890764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6890764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6890792 : List Nat := [2, 1, 5, 1, 2, 3, 1, 2, 2, 2, 2]
def baseStart_6890792 : Nat := 118140960795 + 6890792 * 2 ^ 59
def prefixEnd_6890792 : Nat := 4983230072969 + 3 ^ 40 * 6890792 * 2
def baseEnd_6890792 : Nat := 3538288386156508978309831

theorem tailTrace_6890792 : CollatzResearch.WordTrace tailWord_6890792 prefixEnd_6890792 3538288386156508978309831 := by
  unfold tailWord_6890792
  simp only [CollatzResearch.WordTrace]
  refine ⟨125663915825922456212305315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167551887767896608283073753 125663915825922456212305315)
  ·
    refine ⟨188495873738883684318457973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125663915825922456212305315 188495873738883684318457973)
    ·
      refine ⟨17671488163020345404855435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 188495873738883684318457973 17671488163020345404855435)
      ·
        refine ⟨26507232244530518107283153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17671488163020345404855435 26507232244530518107283153)
        ·
          refine ⟨19880424183397888580462365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26507232244530518107283153 19880424183397888580462365)
          ·
            refine ⟨7455159068774208217673387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19880424183397888580462365 7455159068774208217673387)
            ·
              refine ⟨11182738603161312326510081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7455159068774208217673387 11182738603161312326510081)
              ·
                refine ⟨8387053952370984244882561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11182738603161312326510081 8387053952370984244882561)
                ·
                  refine ⟨6290290464278238183661921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8387053952370984244882561 6290290464278238183661921)
                  ·
                    refine ⟨4717717848208678637746441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6290290464278238183661921 4717717848208678637746441)
                    ·
                      refine ⟨3538288386156508978309831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4717717848208678637746441 3538288386156508978309831)
                      ·
                        rfl

theorem cell23_6890792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_6890792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6890792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6890792 prefixEnd_6890792 := by exact prefixLift 6890792
  have htrace : WordTrace (prefixWord ++ tailWord_6890792) baseStart_6890792 baseEnd_6890792 := by
    simpa [prefixWord, tailWord_6890792, baseEnd_6890792] using wordTrace_append hprefix tailTrace_6890792
  have hstable : (prefixWord ++ tailWord_6890792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6890792).length < 2 ^ (prefixWord ++ tailWord_6890792).sum := by decide
  have hdescent : baseEnd_6890792 < baseStart_6890792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6890792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6890834 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5]
def baseStart_6890834 : Nat := 118140960795 + 6890834 * 2 ^ 59
def prefixEnd_6890834 : Nat := 4983230072969 + 3 ^ 40 * 6890834 * 2
def baseEnd_6890834 : Nat := 3538309952343997813984637

theorem tailTrace_6890834 : CollatzResearch.WordTrace tailWord_6890834 prefixEnd_6890834 3538309952343997813984637 := by
  unfold tailWord_6890834
  simp only [CollatzResearch.WordTrace]
  refine ⟨62832340879423188399409889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167552909011795169065093037 62832340879423188399409889)
  ·
    refine ⟨47124255659567391299557417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62832340879423188399409889 47124255659567391299557417)
    ·
      refine ⟨35343191744675543474668063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47124255659567391299557417 35343191744675543474668063)
      ·
        refine ⟨53014787617013315212002095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35343191744675543474668063 53014787617013315212002095)
        ·
          refine ⟨79522181425519972818003143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53014787617013315212002095 79522181425519972818003143)
          ·
            refine ⟨119283272138279959227004715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79522181425519972818003143 119283272138279959227004715)
            ·
              refine ⟨178924908207419938840507073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119283272138279959227004715 178924908207419938840507073)
              ·
                refine ⟨134193681155564954130380305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178924908207419938840507073 134193681155564954130380305)
                ·
                  refine ⟨100645260866673715597785229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134193681155564954130380305 100645260866673715597785229)
                  ·
                    refine ⟨37741972825002643349169461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100645260866673715597785229 37741972825002643349169461)
                    ·
                      refine ⟨3538309952343997813984637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37741972825002643349169461 3538309952343997813984637)
                      ·
                        rfl

theorem cell23_6890834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_6890834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6890834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6890834 prefixEnd_6890834 := by exact prefixLift 6890834
  have htrace : WordTrace (prefixWord ++ tailWord_6890834) baseStart_6890834 baseEnd_6890834 := by
    simpa [prefixWord, tailWord_6890834, baseEnd_6890834] using wordTrace_append hprefix tailTrace_6890834
  have hstable : (prefixWord ++ tailWord_6890834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6890834).length < 2 ^ (prefixWord ++ tailWord_6890834).sum := by decide
  have hdescent : baseEnd_6890834 < baseStart_6890834 := by decide
  rcases family_descends (prefixWord ++ tailWord_6890834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6890851 : List Nat := [1, 1, 1, 5, 2, 2, 1, 1, 4, 2, 3]
def baseStart_6890851 : Nat := 118140960795 + 6890851 * 2 ^ 59
def prefixEnd_6890851 : Nat := 4983230072969 + 3 ^ 40 * 6890851 * 2
def baseEnd_6890851 : Nat := 3538318681515124247472059

theorem tailTrace_6890851 : CollatzResearch.WordTrace tailWord_6890851 prefixEnd_6890851 3538318681515124247472059 := by
  unfold tailWord_6890851
  simp only [CollatzResearch.WordTrace]
  refine ⟨251329983558631165501008407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167553322372420777000672271 251329983558631165501008407)
  ·
    refine ⟨376994975337946748251512611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251329983558631165501008407 376994975337946748251512611)
    ·
      refine ⟨565492463006920122377268917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376994975337946748251512611 565492463006920122377268917)
      ·
        refine ⟨53014918406898761472868961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 565492463006920122377268917 53014918406898761472868961)
        ·
          refine ⟨39761188805174071104651721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53014918406898761472868961 39761188805174071104651721)
          ·
            refine ⟨29820891603880553328488791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39761188805174071104651721 29820891603880553328488791)
            ·
              refine ⟨44731337405820829992733187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29820891603880553328488791 44731337405820829992733187)
              ·
                refine ⟨67097006108731244989099781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44731337405820829992733187 67097006108731244989099781)
                ·
                  refine ⟨12580688645387108435456209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67097006108731244989099781 12580688645387108435456209)
                  ·
                    refine ⟨9435516484040331326592157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12580688645387108435456209 9435516484040331326592157)
                    ·
                      refine ⟨3538318681515124247472059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9435516484040331326592157 3538318681515124247472059)
                      ·
                        rfl

theorem cell23_6890851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_6890851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6890851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6890851 prefixEnd_6890851 := by exact prefixLift 6890851
  have htrace : WordTrace (prefixWord ++ tailWord_6890851) baseStart_6890851 baseEnd_6890851 := by
    simpa [prefixWord, tailWord_6890851, baseEnd_6890851] using wordTrace_append hprefix tailTrace_6890851
  have hstable : (prefixWord ++ tailWord_6890851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6890851).length < 2 ^ (prefixWord ++ tailWord_6890851).sum := by decide
  have hdescent : baseEnd_6890851 < baseStart_6890851 := by decide
  rcases family_descends (prefixWord ++ tailWord_6890851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6890901 : List Nat := [1, 3, 2, 1, 1, 2, 2, 5, 1, 5]
def baseStart_6890901 : Nat := 118140960795 + 6890901 * 2 ^ 59
def prefixEnd_6890901 : Nat := 4983230072969 + 3 ^ 40 * 6890901 * 2
def baseEnd_6890901 : Nat := 1179448118515949683948943

theorem tailTrace_6890901 : CollatzResearch.WordTrace tailWord_6890901 prefixEnd_6890901 1179448118515949683948943 := by
  unfold tailWord_6890901
  simp only [CollatzResearch.WordTrace]
  refine ⟨251331807208450024040328557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167554538138966682693552371 251331807208450024040328557)
  ·
    refine ⟨94249427703168759015123209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251331807208450024040328557 94249427703168759015123209)
    ·
      refine ⟨70687070777376569261342407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94249427703168759015123209 70687070777376569261342407)
      ·
        refine ⟨106030606166064853892013611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70687070777376569261342407 106030606166064853892013611)
        ·
          refine ⟨159045909249097280838020417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106030606166064853892013611 159045909249097280838020417)
          ·
            refine ⟨119284431936822960628515313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159045909249097280838020417 119284431936822960628515313)
            ·
              refine ⟨89463323952617220471386485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119284431936822960628515313 89463323952617220471386485)
              ·
                refine ⟨8387186620557864419192483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89463323952617220471386485 8387186620557864419192483)
                ·
                  refine ⟨12580779930836796628788725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8387186620557864419192483 12580779930836796628788725)
                  ·
                    refine ⟨1179448118515949683948943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12580779930836796628788725 1179448118515949683948943)
                    ·
                      rfl

theorem cell23_6890901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5, 1, 5].length) (baseStart_6890901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6890901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6890901 prefixEnd_6890901 := by exact prefixLift 6890901
  have htrace : WordTrace (prefixWord ++ tailWord_6890901) baseStart_6890901 baseEnd_6890901 := by
    simpa [prefixWord, tailWord_6890901, baseEnd_6890901] using wordTrace_append hprefix tailTrace_6890901
  have hstable : (prefixWord ++ tailWord_6890901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6890901).length < 2 ^ (prefixWord ++ tailWord_6890901).sum := by decide
  have hdescent : baseEnd_6890901 < baseStart_6890901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6890901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6890915 : List Nat := [1, 1, 1, 4, 1, 3, 3, 4, 1, 1, 3]
def baseStart_6890915 : Nat := 118140960795 + 6890915 * 2 ^ 59
def prefixEnd_6890915 : Nat := 4983230072969 + 3 ^ 40 * 6890915 * 2
def baseEnd_6890915 : Nat := 3538351544277011997071765

theorem tailTrace_6890915 : CollatzResearch.WordTrace tailWord_6890915 prefixEnd_6890915 3538351544277011997071765 := by
  unfold tailWord_6890915
  simp only [CollatzResearch.WordTrace]
  refine ⟨251332317830399304431338199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167554878553599536287558799 251332317830399304431338199)
  ·
    refine ⟨376998476745598956647007299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251332317830399304431338199 376998476745598956647007299)
    ·
      refine ⟨565497715118398434970510949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376998476745598956647007299 565497715118398434970510949)
      ·
        refine ⟨106030821584699706556970803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 565497715118398434970510949 106030821584699706556970803)
        ·
          refine ⟨159046232377049559835456205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106030821584699706556970803 159046232377049559835456205)
          ·
            refine ⟨59642337141393584938296077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159046232377049559835456205 59642337141393584938296077)
            ·
              refine ⟨22365876428022594351861029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59642337141393584938296077 22365876428022594351861029)
              ·
                refine ⟨4193601830254236440973943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22365876428022594351861029 4193601830254236440973943)
                ·
                  refine ⟨6290402745381354661460915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4193601830254236440973943 6290402745381354661460915)
                  ·
                    refine ⟨9435604118072031992191373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6290402745381354661460915 9435604118072031992191373)
                    ·
                      refine ⟨3538351544277011997071765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9435604118072031992191373 3538351544277011997071765)
                      ·
                        rfl

theorem cell23_6890915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 4, 1, 1, 3].length) (baseStart_6890915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6890915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6890915 prefixEnd_6890915 := by exact prefixLift 6890915
  have htrace : WordTrace (prefixWord ++ tailWord_6890915) baseStart_6890915 baseEnd_6890915 := by
    simpa [prefixWord, tailWord_6890915, baseEnd_6890915] using wordTrace_append hprefix tailTrace_6890915
  have hstable : (prefixWord ++ tailWord_6890915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6890915).length < 2 ^ (prefixWord ++ tailWord_6890915).sum := by decide
  have hdescent : baseEnd_6890915 < baseStart_6890915 := by decide
  rcases family_descends (prefixWord ++ tailWord_6890915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6890921 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 4, 6, 2]
def baseStart_6890921 : Nat := 118140960795 + 6890921 * 2 ^ 59
def prefixEnd_6890921 : Nat := 4983230072969 + 3 ^ 40 * 6890921 * 2
def baseEnd_6890921 : Nat := 3538354625160938973596737

theorem tailTrace_6890921 : CollatzResearch.WordTrace tailWord_6890921 prefixEnd_6890921 3538354625160938973596737 := by
  unfold tailWord_6890921
  simp only [CollatzResearch.WordTrace]
  refine ⟨251332536668377567456056617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167555024445585044970704411 251332536668377567456056617)
  ·
    refine ⟨188499402501283175592042463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251332536668377567456056617 188499402501283175592042463)
    ·
      refine ⟨282749103751924763388063695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188499402501283175592042463 282749103751924763388063695)
      ·
        refine ⟨424123655627887145082095543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282749103751924763388063695 424123655627887145082095543)
        ·
          refine ⟨636185483441830717623143315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424123655627887145082095543 636185483441830717623143315)
          ·
            refine ⟨954278225162746076434714973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 636185483441830717623143315 954278225162746076434714973)
            ·
              refine ⟨357854334436029778663018115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 954278225162746076434714973 357854334436029778663018115)
              ·
                refine ⟨536781501654044667994527173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 357854334436029778663018115 536781501654044667994527173)
                ·
                  refine ⟨100646531560133375248973845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 536781501654044667994527173 100646531560133375248973845)
                  ·
                    refine ⟨4717806166881251964795649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 100646531560133375248973845 4717806166881251964795649)
                    ·
                      refine ⟨3538354625160938973596737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4717806166881251964795649 3538354625160938973596737)
                      ·
                        rfl

theorem cell23_6890921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 6, 2].length) (baseStart_6890921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6890921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6890921 prefixEnd_6890921 := by exact prefixLift 6890921
  have htrace : WordTrace (prefixWord ++ tailWord_6890921) baseStart_6890921 baseEnd_6890921 := by
    simpa [prefixWord, tailWord_6890921, baseEnd_6890921] using wordTrace_append hprefix tailTrace_6890921
  have hstable : (prefixWord ++ tailWord_6890921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6890921).length < 2 ^ (prefixWord ++ tailWord_6890921).sum := by decide
  have hdescent : baseEnd_6890921 < baseStart_6890921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6890921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6890944 : List Nat := [2, 1, 1, 2, 3, 1, 2, 11]
def baseStart_6890944 : Nat := 118140960795 + 6890944 * 2 ^ 59
def prefixEnd_6890944 : Nat := 4983230072969 + 3 ^ 40 * 6890944 * 2
def baseEnd_6890944 : Nat := 131050608711703421615153

theorem tailTrace_6890944 : CollatzResearch.WordTrace tailWord_6890944 prefixEnd_6890944 131050608711703421615153 := by
  unfold tailWord_6890944
  simp only [CollatzResearch.WordTrace]
  refine ⟨125666687773647121192071943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167555583698196161589429257 125666687773647121192071943)
  ·
    refine ⟨188500031660470681788107915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125666687773647121192071943 188500031660470681788107915)
    ·
      refine ⟨282750047490706022682161873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188500031660470681788107915 282750047490706022682161873)
      ·
        refine ⟨212062535618029517011621405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282750047490706022682161873 212062535618029517011621405)
        ·
          refine ⟨79523450856761068879358027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212062535618029517011621405 79523450856761068879358027)
          ·
            refine ⟨119285176285141603319037041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79523450856761068879358027 119285176285141603319037041)
            ·
              refine ⟨89463882213856202489277781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119285176285141603319037041 89463882213856202489277781)
              ·
                refine ⟨131050608711703421615153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 89463882213856202489277781 131050608711703421615153)
                ·
                  rfl

theorem cell23_6890944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 11].length) (baseStart_6890944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6890944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6890944 prefixEnd_6890944 := by exact prefixLift 6890944
  have htrace : WordTrace (prefixWord ++ tailWord_6890944) baseStart_6890944 baseEnd_6890944 := by
    simpa [prefixWord, tailWord_6890944, baseEnd_6890944] using wordTrace_append hprefix tailTrace_6890944
  have hstable : (prefixWord ++ tailWord_6890944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6890944).length < 2 ^ (prefixWord ++ tailWord_6890944).sum := by decide
  have hdescent : baseEnd_6890944 < baseStart_6890944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6890944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6890948 : List Nat := [2, 3, 3, 2, 1, 1, 2, 2, 1, 6]
def baseStart_6890948 : Nat := 118140960795 + 6890948 * 2 ^ 59
def prefixEnd_6890948 : Nat := 4983230072969 + 3 ^ 40 * 6890948 * 2
def baseEnd_6890948 : Nat := 1179456163046203455986371

theorem tailTrace_6890948 : CollatzResearch.WordTrace tailWord_6890948 prefixEnd_6890948 1179456163046203455986371 := by
  unfold tailWord_6890948
  simp only [CollatzResearch.WordTrace]
  refine ⟨125666760719639875533644749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167555680959519834044859665 125666760719639875533644749)
  ·
    refine ⟨47125035269864953325116781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125666760719639875533644749 47125035269864953325116781)
    ·
      refine ⟨17671888226199357496918793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47125035269864953325116781 17671888226199357496918793)
      ·
        refine ⟨13253916169649518122689095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17671888226199357496918793 13253916169649518122689095)
        ·
          refine ⟨19880874254474277184033643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13253916169649518122689095 19880874254474277184033643)
          ·
            refine ⟨29821311381711415776050465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19880874254474277184033643 29821311381711415776050465)
            ·
              refine ⟨22365983536283561832037849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29821311381711415776050465 22365983536283561832037849)
              ·
                refine ⟨16774487652212671374028387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22365983536283561832037849 16774487652212671374028387)
                ·
                  refine ⟨25161731478319007061042581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16774487652212671374028387 25161731478319007061042581)
                  ·
                    refine ⟨1179456163046203455986371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25161731478319007061042581 1179456163046203455986371)
                    ·
                      rfl

theorem cell23_6890948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_6890948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6890948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6890948 prefixEnd_6890948 := by exact prefixLift 6890948
  have htrace : WordTrace (prefixWord ++ tailWord_6890948) baseStart_6890948 baseEnd_6890948 := by
    simpa [prefixWord, tailWord_6890948, baseEnd_6890948] using wordTrace_append hprefix tailTrace_6890948
  have hstable : (prefixWord ++ tailWord_6890948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6890948).length < 2 ^ (prefixWord ++ tailWord_6890948).sum := by decide
  have hdescent : baseEnd_6890948 < baseStart_6890948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6890948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6890951 : List Nat := [1, 1, 4, 1, 1, 3, 1, 4, 1, 2, 4]
def baseStart_6890951 : Nat := 118140960795 + 6890951 * 2 ^ 59
def prefixEnd_6890951 : Nat := 4983230072969 + 3 ^ 40 * 6890951 * 2
def baseEnd_6890951 : Nat := 3538370029580573856221599

theorem tailTrace_6890951 : CollatzResearch.WordTrace tailWord_6890951 prefixEnd_6890951 3538370029580573856221599 := by
  unfold tailWord_6890951
  simp only [CollatzResearch.WordTrace]
  refine ⟨251333630858268882579648707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167555753905512588386432471 251333630858268882579648707)
  ·
    refine ⟨377000446287403323869473061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251333630858268882579648707 377000446287403323869473061)
    ·
      refine ⟨70687583678888123225526199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 377000446287403323869473061 70687583678888123225526199)
      ·
        refine ⟨106031375518332184838289299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70687583678888123225526199 106031375518332184838289299)
        ·
          refine ⟨159047063277498277257433949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106031375518332184838289299 159047063277498277257433949)
          ·
            refine ⟨59642648729061853971537731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159047063277498277257433949 59642648729061853971537731)
            ·
              refine ⟨89463973093592780957306597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59642648729061853971537731 89463973093592780957306597)
              ·
                refine ⟨16774494955048646429494987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89463973093592780957306597 16774494955048646429494987)
                ·
                  refine ⟨25161742432572969644242481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16774494955048646429494987 25161742432572969644242481)
                  ·
                    refine ⟨18871306824429727233181861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25161742432572969644242481 18871306824429727233181861)
                    ·
                      refine ⟨3538370029580573856221599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18871306824429727233181861 3538370029580573856221599)
                      ·
                        rfl

theorem cell23_6890951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_6890951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6890951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6890951 prefixEnd_6890951 := by exact prefixLift 6890951
  have htrace : WordTrace (prefixWord ++ tailWord_6890951) baseStart_6890951 baseEnd_6890951 := by
    simpa [prefixWord, tailWord_6890951, baseEnd_6890951] using wordTrace_append hprefix tailTrace_6890951
  have hstable : (prefixWord ++ tailWord_6890951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6890951).length < 2 ^ (prefixWord ++ tailWord_6890951).sum := by decide
  have hdescent : baseEnd_6890951 < baseStart_6890951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6890951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891079 : List Nat := [1, 1, 4, 1, 5, 1, 2, 2, 2, 2, 2]
def baseStart_6891079 : Nat := 118140960795 + 6891079 * 2 ^ 59
def prefixEnd_6891079 : Nat := 4983230072969 + 3 ^ 40 * 6891079 * 2
def baseEnd_6891079 : Nat := 3538435755104349355421011

theorem tailTrace_6891079 : CollatzResearch.WordTrace tailWord_6891079 prefixEnd_6891079 3538435755104349355421011 := by
  unfold tailWord_6891079
  simp only [CollatzResearch.WordTrace]
  refine ⟨251338299401805160440308291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167558866267870106960205527 251338299401805160440308291)
  ·
    refine ⟨377007449102707740660462437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251338299401805160440308291 377007449102707740660462437)
    ·
      refine ⟨70688896706757701373836707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 377007449102707740660462437 70688896706757701373836707)
      ·
        refine ⟨106033345060136552060755061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70688896706757701373836707 106033345060136552060755061)
        ·
          refine ⟨9940626099387801755695787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106033345060136552060755061 9940626099387801755695787)
          ·
            refine ⟨14910939149081702633543681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9940626099387801755695787 14910939149081702633543681)
            ·
              refine ⟨11183204361811276975157761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14910939149081702633543681 11183204361811276975157761)
              ·
                refine ⟨8387403271358457731368321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11183204361811276975157761 8387403271358457731368321)
                ·
                  refine ⟨6290552453518843298526241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8387403271358457731368321 6290552453518843298526241)
                  ·
                    refine ⟨4717914340139132473894681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6290552453518843298526241 4717914340139132473894681)
                    ·
                      refine ⟨3538435755104349355421011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4717914340139132473894681 3538435755104349355421011)
                      ·
                        rfl

theorem cell23_6891079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2, 2, 2, 2].length) (baseStart_6891079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891079 prefixEnd_6891079 := by exact prefixLift 6891079
  have htrace : WordTrace (prefixWord ++ tailWord_6891079) baseStart_6891079 baseEnd_6891079 := by
    simpa [prefixWord, tailWord_6891079, baseEnd_6891079] using wordTrace_append hprefix tailTrace_6891079
  have hstable : (prefixWord ++ tailWord_6891079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891079).length < 2 ^ (prefixWord ++ tailWord_6891079).sum := by decide
  have hdescent : baseEnd_6891079 < baseStart_6891079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891088 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 1, 7, 2]
def baseStart_6891088 : Nat := 118140960795 + 6891088 * 2 ^ 59
def prefixEnd_6891088 : Nat := 4983230072969 + 3 ^ 40 * 6891088 * 2
def baseEnd_6891088 : Nat := 3538440376430239820208469

theorem tailTrace_6891088 : CollatzResearch.WordTrace tailWord_6891088 prefixEnd_6891088 3538440376430239820208469 := by
  unfold tailWord_6891088
  simp only [CollatzResearch.WordTrace]
  refine ⟨125669313829386277488692959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167559085105848369984923945 125669313829386277488692959)
  ·
    refine ⟨188503970744079416233039439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125669313829386277488692959 188503970744079416233039439)
    ·
      refine ⟨282755956116119124349559159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188503970744079416233039439 282755956116119124349559159)
      ·
        refine ⟨424133934174178686524338739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282755956116119124349559159 424133934174178686524338739)
        ·
          refine ⟨636200901261268029786508109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424133934174178686524338739 636200901261268029786508109)
          ·
            refine ⟨238575337972975511169940541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 636200901261268029786508109 238575337972975511169940541)
            ·
              refine ⟨89465751739865816688727703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 238575337972975511169940541 89465751739865816688727703)
              ·
                refine ⟨134198627609798725033091555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89465751739865816688727703 134198627609798725033091555)
                ·
                  refine ⟨201297941414698087549637333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134198627609798725033091555 201297941414698087549637333)
                  ·
                    refine ⟨4717920501906986426944625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 201297941414698087549637333 4717920501906986426944625)
                    ·
                      refine ⟨3538440376430239820208469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4717920501906986426944625 3538440376430239820208469)
                      ·
                        rfl

theorem cell23_6891088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 1, 7, 2].length) (baseStart_6891088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891088 prefixEnd_6891088 := by exact prefixLift 6891088
  have htrace : WordTrace (prefixWord ++ tailWord_6891088) baseStart_6891088 baseEnd_6891088 := by
    simpa [prefixWord, tailWord_6891088, baseEnd_6891088] using wordTrace_append hprefix tailTrace_6891088
  have hstable : (prefixWord ++ tailWord_6891088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891088).length < 2 ^ (prefixWord ++ tailWord_6891088).sum := by decide
  have hdescent : baseEnd_6891088 < baseStart_6891088 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891131 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 6]
def baseStart_6891131 : Nat := 118140960795 + 6891131 * 2 ^ 59
def prefixEnd_6891131 : Nat := 4983230072969 + 3 ^ 40 * 6891131 * 2
def baseEnd_6891131 : Nat := 3538462456098383151970771

theorem tailTrace_6891131 : CollatzResearch.WordTrace tailWord_6891131 prefixEnd_6891131 3538462456098383151970771 := by
  unfold tailWord_6891131
  simp only [CollatzResearch.WordTrace]
  refine ⟨251340195997616773321201247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167560130665077848880800831 251340195997616773321201247)
  ·
    refine ⟨377010293996425159981801871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251340195997616773321201247 377010293996425159981801871)
    ·
      refine ⟨565515440994637739972702807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377010293996425159981801871 565515440994637739972702807)
      ·
        refine ⟨848273161491956609959054211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565515440994637739972702807 848273161491956609959054211)
        ·
          refine ⟨1272409742237934914938581317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 848273161491956609959054211 1272409742237934914938581317)
          ·
            refine ⟨238576826669612796550983997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1272409742237934914938581317 238576826669612796550983997)
            ·
              refine ⟨89466310001104798706618999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 238576826669612796550983997 89466310001104798706618999)
              ·
                refine ⟨134199465001657198059928499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89466310001104798706618999 134199465001657198059928499)
                ·
                  refine ⟨201299197502485797089892749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134199465001657198059928499 201299197502485797089892749)
                  ·
                    refine ⟨75487199063432173908709781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 201299197502485797089892749 75487199063432173908709781)
                    ·
                      refine ⟨3538462456098383151970771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75487199063432173908709781 3538462456098383151970771)
                      ·
                        rfl

theorem cell23_6891131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 6].length) (baseStart_6891131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891131 prefixEnd_6891131 := by exact prefixLift 6891131
  have htrace : WordTrace (prefixWord ++ tailWord_6891131) baseStart_6891131 baseEnd_6891131 := by
    simpa [prefixWord, tailWord_6891131, baseEnd_6891131] using wordTrace_append hprefix tailTrace_6891131
  have hstable : (prefixWord ++ tailWord_6891131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891131).length < 2 ^ (prefixWord ++ tailWord_6891131).sum := by decide
  have hdescent : baseEnd_6891131 < baseStart_6891131 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891225 : List Nat := [1, 2, 1, 2, 3, 4, 1, 1, 3, 1, 4]
def baseStart_6891225 : Nat := 118140960795 + 6891225 * 2 ^ 59
def prefixEnd_6891225 : Nat := 4983230072969 + 3 ^ 40 * 6891225 * 2
def baseEnd_6891225 : Nat := 3538510723279905784195339

theorem tailTrace_6891225 : CollatzResearch.WordTrace tailWord_6891225 prefixEnd_6891225 3538510723279905784195339 := by
  unfold tailWord_6891225
  simp only [CollatzResearch.WordTrace]
  refine ⟨251343624459276227375123129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167562416306184151583415419 251343624459276227375123129)
  ·
    refine ⟨188507718344457170531342347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251343624459276227375123129 188507718344457170531342347)
    ·
      refine ⟨282761577516685755797013521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188507718344457170531342347 282761577516685755797013521)
      ·
        refine ⟨212071183137514316847760141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282761577516685755797013521 212071183137514316847760141)
        ·
          refine ⟨79526693676567868817910053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212071183137514316847760141 79526693676567868817910053)
          ·
            refine ⟨14911255064356475403358135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79526693676567868817910053 14911255064356475403358135)
            ·
              refine ⟨22366882596534713105037203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14911255064356475403358135 22366882596534713105037203)
              ·
                refine ⟨33550323894802069657555805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22366882596534713105037203 33550323894802069657555805)
                ·
                  refine ⟨12581371460550776121583427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33550323894802069657555805 12581371460550776121583427)
                  ·
                    refine ⟨18872057190826164182375141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12581371460550776121583427 18872057190826164182375141)
                    ·
                      refine ⟨3538510723279905784195339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18872057190826164182375141 3538510723279905784195339)
                      ·
                        rfl

theorem cell23_6891225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3, 1, 4].length) (baseStart_6891225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891225 prefixEnd_6891225 := by exact prefixLift 6891225
  have htrace : WordTrace (prefixWord ++ tailWord_6891225) baseStart_6891225 baseEnd_6891225 := by
    simpa [prefixWord, tailWord_6891225, baseEnd_6891225] using wordTrace_append hprefix tailTrace_6891225
  have hstable : (prefixWord ++ tailWord_6891225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891225).length < 2 ^ (prefixWord ++ tailWord_6891225).sum := by decide
  have hdescent : baseEnd_6891225 < baseStart_6891225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891275 : List Nat := [1, 1, 1, 1, 5, 1, 3, 3, 1, 3, 3]
def baseStart_6891275 : Nat := 118140960795 + 6891275 * 2 ^ 59
def prefixEnd_6891275 : Nat := 4983230072969 + 3 ^ 40 * 6891275 * 2
def baseEnd_6891275 : Nat := 3538536397312630588570109

theorem tailTrace_6891275 : CollatzResearch.WordTrace tailWord_6891275 prefixEnd_6891275 3538536397312630588570109 := by
  unfold tailWord_6891275
  simp only [CollatzResearch.WordTrace]
  refine ⟨251345448109095085914443279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167563632072730057276295519 251345448109095085914443279)
  ·
    refine ⟨377018172163642628871664919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251345448109095085914443279 377018172163642628871664919)
    ·
      refine ⟨565527258245463943307497379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377018172163642628871664919 565527258245463943307497379)
      ·
        refine ⟨848290887368195914961246069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565527258245463943307497379 848290887368195914961246069)
        ·
          refine ⟨79527270690768367027616819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 848290887368195914961246069 79527270690768367027616819)
          ·
            refine ⟨119290906036152550541425229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79527270690768367027616819 119290906036152550541425229)
            ·
              refine ⟨44734089763557206453034461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119290906036152550541425229 44734089763557206453034461)
              ·
                refine ⟨16775283661333952419887923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44734089763557206453034461 16775283661333952419887923)
                ·
                  refine ⟨25162925492000928629831885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16775283661333952419887923 25162925492000928629831885)
                  ·
                    refine ⟨9436097059500348236186957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25162925492000928629831885 9436097059500348236186957)
                    ·
                      refine ⟨3538536397312630588570109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9436097059500348236186957 3538536397312630588570109)
                      ·
                        rfl

theorem cell23_6891275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 3, 3].length) (baseStart_6891275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891275 prefixEnd_6891275 := by exact prefixLift 6891275
  have htrace : WordTrace (prefixWord ++ tailWord_6891275) baseStart_6891275 baseEnd_6891275 := by
    simpa [prefixWord, tailWord_6891275, baseEnd_6891275] using wordTrace_append hprefix tailTrace_6891275
  have hstable : (prefixWord ++ tailWord_6891275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891275).length < 2 ^ (prefixWord ++ tailWord_6891275).sum := by decide
  have hdescent : baseEnd_6891275 < baseStart_6891275 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891292 : List Nat := [2, 2, 3, 1, 1, 2, 2, 2, 4, 1, 3]
def baseStart_6891292 : Nat := 118140960795 + 6891292 * 2 ^ 59
def prefixEnd_6891292 : Nat := 4983230072969 + 3 ^ 40 * 6891292 * 2
def baseEnd_6891292 : Nat := 3538545126483757022057531

theorem tailTrace_6891292 : CollatzResearch.WordTrace tailWord_6891292 prefixEnd_6891292 3538545126483757022057531 := by
  unfold tailWord_6891292
  simp only [CollatzResearch.WordTrace]
  refine ⟨125673034075016748908906065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167564045433355665211874753 125673034075016748908906065)
  ·
    refine ⟨94254775556262561681679549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125673034075016748908906065 94254775556262561681679549)
    ·
      refine ⟨35345540833598460630629831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94254775556262561681679549 35345540833598460630629831)
      ·
        refine ⟨53018311250397690945944747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35345540833598460630629831 53018311250397690945944747)
        ·
          refine ⟨79527466875596536418917121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53018311250397690945944747 79527466875596536418917121)
          ·
            refine ⟨59645600156697402314187841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79527466875596536418917121 59645600156697402314187841)
            ·
              refine ⟨44734200117523051735640881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59645600156697402314187841 44734200117523051735640881)
              ·
                refine ⟨33550650088142288801730661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44734200117523051735640881 33550650088142288801730661)
                ·
                  refine ⟨6290746891526679150324499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33550650088142288801730661 6290746891526679150324499)
                  ·
                    refine ⟨9436120337290018725486749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6290746891526679150324499 9436120337290018725486749)
                    ·
                      refine ⟨3538545126483757022057531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9436120337290018725486749 3538545126483757022057531)
                      ·
                        rfl

theorem cell23_6891292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_6891292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891292 prefixEnd_6891292 := by exact prefixLift 6891292
  have htrace : WordTrace (prefixWord ++ tailWord_6891292) baseStart_6891292 baseEnd_6891292 := by
    simpa [prefixWord, tailWord_6891292, baseEnd_6891292] using wordTrace_append hprefix tailTrace_6891292
  have hstable : (prefixWord ++ tailWord_6891292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891292).length < 2 ^ (prefixWord ++ tailWord_6891292).sum := by decide
  have hdescent : baseEnd_6891292 < baseStart_6891292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891335 : List Nat := [1, 1, 4, 1, 2, 1, 2, 2, 2, 4, 3]
def baseStart_6891335 : Nat := 118140960795 + 6891335 * 2 ^ 59
def prefixEnd_6891335 : Nat := 4983230072969 + 3 ^ 40 * 6891335 * 2
def baseEnd_6891335 : Nat := 3538567206151900353819833

theorem tailTrace_6891335 : CollatzResearch.WordTrace tailWord_6891335 prefixEnd_6891335 3538567206151900353819833 := by
  unfold tailWord_6891335
  simp only [CollatzResearch.WordTrace]
  refine ⟨251347636488877716161627459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167565090992585144107751639 251347636488877716161627459)
  ·
    refine ⟨377021454733316574242441189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251347636488877716161627459 377021454733316574242441189)
    ·
      refine ⟨70691522762496857670457723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 377021454733316574242441189 70691522762496857670457723)
      ·
        refine ⟨106037284143745286505686585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70691522762496857670457723 106037284143745286505686585)
        ·
          refine ⟨79527963107808964879264939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106037284143745286505686585 79527963107808964879264939)
          ·
            refine ⟨119291944661713447318897409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79527963107808964879264939 119291944661713447318897409)
            ·
              refine ⟨89468958496285085489173057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119291944661713447318897409 89468958496285085489173057)
              ·
                refine ⟨67101718872213814116879793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89468958496285085489173057 67101718872213814116879793)
                ·
                  refine ⟨50326289154160360587659845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67101718872213814116879793 50326289154160360587659845)
                  ·
                    refine ⟨9436179216405067610186221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50326289154160360587659845 9436179216405067610186221)
                    ·
                      refine ⟨3538567206151900353819833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9436179216405067610186221 3538567206151900353819833)
                      ·
                        rfl

theorem cell23_6891335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 4, 3].length) (baseStart_6891335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891335 prefixEnd_6891335 := by exact prefixLift 6891335
  have htrace : WordTrace (prefixWord ++ tailWord_6891335) baseStart_6891335 baseEnd_6891335 := by
    simpa [prefixWord, tailWord_6891335, baseEnd_6891335] using wordTrace_append hprefix tailTrace_6891335
  have hstable : (prefixWord ++ tailWord_6891335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891335).length < 2 ^ (prefixWord ++ tailWord_6891335).sum := by decide
  have hdescent : baseEnd_6891335 < baseStart_6891335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891349 : List Nat := [1, 3, 2, 2, 2, 2, 1, 2, 4, 2, 2]
def baseStart_6891349 : Nat := 118140960795 + 6891349 * 2 ^ 59
def prefixEnd_6891349 : Nat := 4983230072969 + 3 ^ 40 * 6891349 * 2
def baseEnd_6891349 : Nat := 3538574394881063299044769

theorem tailTrace_6891349 : CollatzResearch.WordTrace tailWord_6891349 prefixEnd_6891349 3538574394881063299044769 := by
  unfold tailWord_6891349
  simp only [CollatzResearch.WordTrace]
  refine ⟨251348147110826996552637101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167565431407217997701758067 251348147110826996552637101)
  ·
    refine ⟨94255555166560123707238913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251348147110826996552637101 94255555166560123707238913)
    ·
      refine ⟨70691666374920092780429185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94255555166560123707238913 70691666374920092780429185)
      ·
        refine ⟨53018749781190069585321889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70691666374920092780429185 53018749781190069585321889)
        ·
          refine ⟨39764062335892552188991417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53018749781190069585321889 39764062335892552188991417)
          ·
            refine ⟨29823046751919414141743563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39764062335892552188991417 29823046751919414141743563)
            ·
              refine ⟨44734570127879121212615345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29823046751919414141743563 44734570127879121212615345)
              ·
                refine ⟨33550927595909340909461509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44734570127879121212615345 33550927595909340909461509)
                ·
                  refine ⟨6290798924233001420524033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33550927595909340909461509 6290798924233001420524033)
                  ·
                    refine ⟨4718099193174751065393025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6290798924233001420524033 4718099193174751065393025)
                    ·
                      refine ⟨3538574394881063299044769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4718099193174751065393025 3538574394881063299044769)
                      ·
                        rfl

theorem cell23_6891349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 4, 2, 2].length) (baseStart_6891349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891349 prefixEnd_6891349 := by exact prefixLift 6891349
  have htrace : WordTrace (prefixWord ++ tailWord_6891349) baseStart_6891349 baseEnd_6891349 := by
    simpa [prefixWord, tailWord_6891349, baseEnd_6891349] using wordTrace_append hprefix tailTrace_6891349
  have hstable : (prefixWord ++ tailWord_6891349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891349).length < 2 ^ (prefixWord ++ tailWord_6891349).sum := by decide
  have hdescent : baseEnd_6891349 < baseStart_6891349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891372 : List Nat := [2, 2, 1, 1, 4, 4, 1, 1, 7]
def baseStart_6891372 : Nat := 118140960795 + 6891372 * 2 ^ 59
def prefixEnd_6891372 : Nat := 4983230072969 + 3 ^ 40 * 6891372 * 2
def baseEnd_6891372 : Nat := 393176244992901856561907

theorem tailTrace_6891372 : CollatzResearch.WordTrace tailWord_6891372 prefixEnd_6891372 393176244992901856561907 := by
  unfold tailWord_6891372
  simp only [CollatzResearch.WordTrace]
  refine ⟨125674492994871835740362185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167565990659829114320482913 125674492994871835740362185)
  ·
    refine ⟨94255869746153876805271639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125674492994871835740362185 94255869746153876805271639)
    ·
      refine ⟨141383804619230815207907459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94255869746153876805271639 141383804619230815207907459)
      ·
        refine ⟨212075706928846222811861189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141383804619230815207907459 212075706928846222811861189)
        ·
          refine ⟨39764195049158666777223973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212075706928846222811861189 39764195049158666777223973)
          ·
            refine ⟨7455786571717250020729495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39764195049158666777223973 7455786571717250020729495)
            ·
              refine ⟨11183679857575875031094243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7455786571717250020729495 11183679857575875031094243)
              ·
                refine ⟨16775519786363812546641365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11183679857575875031094243 16775519786363812546641365)
                ·
                  refine ⟨393176244992901856561907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16775519786363812546641365 393176244992901856561907)
                  ·
                    rfl

theorem cell23_6891372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 7].length) (baseStart_6891372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891372 prefixEnd_6891372 := by exact prefixLift 6891372
  have htrace : WordTrace (prefixWord ++ tailWord_6891372) baseStart_6891372 baseEnd_6891372 := by
    simpa [prefixWord, tailWord_6891372, baseEnd_6891372] using wordTrace_append hprefix tailTrace_6891372
  have hstable : (prefixWord ++ tailWord_6891372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891372).length < 2 ^ (prefixWord ++ tailWord_6891372).sum := by decide
  have hdescent : baseEnd_6891372 < baseStart_6891372 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891385 : List Nat := [1, 2, 1, 3, 2, 2, 1, 2, 4, 5]
def baseStart_6891385 : Nat := 118140960795 + 6891385 * 2 ^ 59
def prefixEnd_6891385 : Nat := 4983230072969 + 3 ^ 40 * 6891385 * 2
def baseEnd_6891385 : Nat := 1179530960061541719398201

theorem tailTrace_6891385 : CollatzResearch.WordTrace tailWord_6891385 prefixEnd_6891385 1179530960061541719398201 := by
  unfold tailWord_6891385
  simp only [CollatzResearch.WordTrace]
  refine ⟨251349460138696574700947609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167566306759131049800631739 251349460138696574700947609)
  ·
    refine ⟨188512095104022431025710707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251349460138696574700947609 188512095104022431025710707)
    ·
      refine ⟨282768142656033646538566061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188512095104022431025710707 282768142656033646538566061)
      ·
        refine ⟨106038053496012617451962273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282768142656033646538566061 106038053496012617451962273)
        ·
          refine ⟨79528540122009463088971705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106038053496012617451962273 79528540122009463088971705)
          ·
            refine ⟨59646405091507097316728779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79528540122009463088971705 59646405091507097316728779)
            ·
              refine ⟨89469607637260645975093169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59646405091507097316728779 89469607637260645975093169)
              ·
                refine ⟨67102205727945484481319877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89469607637260645975093169 67102205727945484481319877)
                ·
                  refine ⟨12581663573989778340247477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67102205727945484481319877 12581663573989778340247477)
                  ·
                    refine ⟨1179530960061541719398201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12581663573989778340247477 1179530960061541719398201)
                    ·
                      rfl

theorem cell23_6891385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4, 5].length) (baseStart_6891385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891385 prefixEnd_6891385 := by exact prefixLift 6891385
  have htrace : WordTrace (prefixWord ++ tailWord_6891385) baseStart_6891385 baseEnd_6891385 := by
    simpa [prefixWord, tailWord_6891385, baseEnd_6891385] using wordTrace_append hprefix tailTrace_6891385
  have hstable : (prefixWord ++ tailWord_6891385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891385).length < 2 ^ (prefixWord ++ tailWord_6891385).sum := by decide
  have hdescent : baseEnd_6891385 < baseStart_6891385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891412 : List Nat := [2, 4, 2, 1, 1, 2, 1, 2, 1, 2, 5]
def baseStart_6891412 : Nat := 118140960795 + 6891412 * 2 ^ 59
def prefixEnd_6891412 : Nat := 4983230072969 + 3 ^ 40 * 6891412 * 2
def baseEnd_6891412 : Nat := 3538606744162296552556979

theorem tailTrace_6891412 : CollatzResearch.WordTrace tailWord_6891412 prefixEnd_6891412 3538606744162296552556979 := by
  unfold tailWord_6891412
  simp only [CollatzResearch.WordTrace]
  refine ⟨125675222454799379156090245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167566963273065838874786993 125675222454799379156090245)
  ·
    refine ⟨23564104210274883591766921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125675222454799379156090245 23564104210274883591766921)
    ·
      refine ⟨17673078157706162693825191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23564104210274883591766921 17673078157706162693825191)
      ·
        refine ⟨26509617236559244040737787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17673078157706162693825191 26509617236559244040737787)
        ·
          refine ⟨39764425854838866061106681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26509617236559244040737787 39764425854838866061106681)
          ·
            refine ⟨29823319391129149545830011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39764425854838866061106681 29823319391129149545830011)
            ·
              refine ⟨44734979086693724318745017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29823319391129149545830011 44734979086693724318745017)
              ·
                refine ⟨33551234315020293239058763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44734979086693724318745017 33551234315020293239058763)
                ·
                  refine ⟨50326851472530439858588145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33551234315020293239058763 50326851472530439858588145)
                  ·
                    refine ⟨37745138604397829893941109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50326851472530439858588145 37745138604397829893941109)
                    ·
                      refine ⟨3538606744162296552556979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37745138604397829893941109 3538606744162296552556979)
                      ·
                        rfl

theorem cell23_6891412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_6891412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891412 prefixEnd_6891412 := by exact prefixLift 6891412
  have htrace : WordTrace (prefixWord ++ tailWord_6891412) baseStart_6891412 baseEnd_6891412 := by
    simpa [prefixWord, tailWord_6891412, baseEnd_6891412] using wordTrace_append hprefix tailTrace_6891412
  have hstable : (prefixWord ++ tailWord_6891412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891412).length < 2 ^ (prefixWord ++ tailWord_6891412).sum := by decide
  have hdescent : baseEnd_6891412 < baseStart_6891412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891423 : List Nat := [1, 1, 2, 5, 4, 1, 2, 2, 5]
def baseStart_6891423 : Nat := 118140960795 + 6891423 * 2 ^ 59
def prefixEnd_6891423 : Nat := 4983230072969 + 3 ^ 40 * 6891423 * 2
def baseEnd_6891423 : Nat := 393179154716610667724381

theorem tailTrace_6891423 : CollatzResearch.WordTrace tailWord_6891423 prefixEnd_6891423 393179154716610667724381 := by
  unfold tailWord_6891423
  simp only [CollatzResearch.WordTrace]
  refine ⟨251350846112558907190830923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167567230741705938127220615 251350846112558907190830923)
  ·
    refine ⟨377026269168838360786246385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251350846112558907190830923 377026269168838360786246385)
    ·
      refine ⟨282769701876628770589684789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377026269168838360786246385 282769701876628770589684789)
      ·
        refine ⟨26509659550933947242782949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 282769701876628770589684789 26509659550933947242782949)
        ·
          refine ⟨4970561165800115108021803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26509659550933947242782949 4970561165800115108021803)
          ·
            refine ⟨7455841748700172662032705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4970561165800115108021803 7455841748700172662032705)
            ·
              refine ⟨5591881311525129496524529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7455841748700172662032705 5591881311525129496524529)
              ·
                refine ⟨4193910983643847122393397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5591881311525129496524529 4193910983643847122393397)
                ·
                  refine ⟨393179154716610667724381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4193910983643847122393397 393179154716610667724381)
                  ·
                    rfl

theorem cell23_6891423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 2, 5].length) (baseStart_6891423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891423 prefixEnd_6891423 := by exact prefixLift 6891423
  have htrace : WordTrace (prefixWord ++ tailWord_6891423) baseStart_6891423 baseEnd_6891423 := by
    simpa [prefixWord, tailWord_6891423, baseEnd_6891423] using wordTrace_append hprefix tailTrace_6891423
  have hstable : (prefixWord ++ tailWord_6891423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891423).length < 2 ^ (prefixWord ++ tailWord_6891423).sum := by decide
  have hdescent : baseEnd_6891423 < baseStart_6891423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891442 : List Nat := [3, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3]
def baseStart_6891442 : Nat := 118140960795 + 6891442 * 2 ^ 59
def prefixEnd_6891442 : Nat := 4983230072969 + 3 ^ 40 * 6891442 * 2
def baseEnd_6891442 : Nat := 3538622148581931435181841

theorem tailTrace_6891442 : CollatzResearch.WordTrace tailWord_6891442 prefixEnd_6891442 3538622148581931435181841 := by
  unfold tailWord_6891442
  simp only [CollatzResearch.WordTrace]
  refine ⟨62837884774872518358943145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167567692732993382290515053 62837884774872518358943145)
  ·
    refine ⟨47128413581154388769207359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62837884774872518358943145 47128413581154388769207359)
    ·
      refine ⟨70692620371731583153811039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47128413581154388769207359 70692620371731583153811039)
      ·
        refine ⟨106038930557597374730716559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70692620371731583153811039 106038930557597374730716559)
        ·
          refine ⟨159058395836396062096074839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106038930557597374730716559 159058395836396062096074839)
          ·
            refine ⟨238587593754594093144112259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159058395836396062096074839 238587593754594093144112259)
            ·
              refine ⟨357881390631891139716168389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238587593754594093144112259 357881390631891139716168389)
              ·
                refine ⟨67102760743479588696781573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 357881390631891139716168389 67102760743479588696781573)
                ·
                  refine ⟨12581767639402422880646545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67102760743479588696781573 12581767639402422880646545)
                  ·
                    refine ⟨9436325729551817160484909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12581767639402422880646545 9436325729551817160484909)
                    ·
                      refine ⟨3538622148581931435181841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9436325729551817160484909 3538622148581931435181841)
                      ·
                        rfl

theorem cell23_6891442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3].length) (baseStart_6891442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891442 prefixEnd_6891442 := by exact prefixLift 6891442
  have htrace : WordTrace (prefixWord ++ tailWord_6891442) baseStart_6891442 baseEnd_6891442 := by
    simpa [prefixWord, tailWord_6891442, baseEnd_6891442] using wordTrace_append hprefix tailTrace_6891442
  have hstable : (prefixWord ++ tailWord_6891442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891442).length < 2 ^ (prefixWord ++ tailWord_6891442).sum := by decide
  have hdescent : baseEnd_6891442 < baseStart_6891442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891489 : List Nat := [1, 2, 3, 1, 2, 1, 3, 3, 3, 1, 3]
def baseStart_6891489 : Nat := 118140960795 + 6891489 * 2 ^ 59
def prefixEnd_6891489 : Nat := 4983230072969 + 3 ^ 40 * 6891489 * 2
def baseEnd_6891489 : Nat := 3538646282172692751294125

theorem tailTrace_6891489 : CollatzResearch.WordTrace tailWord_6891489 prefixEnd_6891489 3538646282172692751294125 := by
  unfold tailWord_6891489
  simp only [CollatzResearch.WordTrace]
  refine ⟨251353253330319800462733521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167568835553546533641822347 251353253330319800462733521)
  ·
    refine ⟨188514939997739850347050141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251353253330319800462733521 188514939997739850347050141)
    ·
      refine ⟨70693102499152443880143803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188514939997739850347050141 70693102499152443880143803)
      ·
        refine ⟨106039653748728665820215705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70693102499152443880143803 106039653748728665820215705)
        ·
          refine ⟨79529740311546499365161779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106039653748728665820215705 79529740311546499365161779)
          ·
            refine ⟨119294610467319749047742669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79529740311546499365161779 119294610467319749047742669)
            ·
              refine ⟨44735478925244905892903501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119294610467319749047742669 44735478925244905892903501)
              ·
                refine ⟨16775804596966839709838813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44735478925244905892903501 16775804596966839709838813)
                ·
                  refine ⟨6290926723862564891189555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16775804596966839709838813 6290926723862564891189555)
                  ·
                    refine ⟨9436390085793847336784333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6290926723862564891189555 9436390085793847336784333)
                    ·
                      refine ⟨3538646282172692751294125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9436390085793847336784333 3538646282172692751294125)
                      ·
                        rfl

theorem cell23_6891489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 3, 1, 3].length) (baseStart_6891489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891489 prefixEnd_6891489 := by exact prefixLift 6891489
  have htrace : WordTrace (prefixWord ++ tailWord_6891489) baseStart_6891489 baseEnd_6891489 := by
    simpa [prefixWord, tailWord_6891489, baseEnd_6891489] using wordTrace_append hprefix tailTrace_6891489
  have hstable : (prefixWord ++ tailWord_6891489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891489).length < 2 ^ (prefixWord ++ tailWord_6891489).sum := by decide
  have hdescent : baseEnd_6891489 < baseStart_6891489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891512 : List Nat := [2, 1, 2, 1, 1, 3, 2, 3, 3, 1, 4]
def baseStart_6891512 : Nat := 118140960795 + 6891512 * 2 ^ 59
def prefixEnd_6891512 : Nat := 4983230072969 + 3 ^ 40 * 6891512 * 2
def baseEnd_6891512 : Nat := 3538658092227746161306519

theorem tailTrace_6891512 : CollatzResearch.WordTrace tailWord_6891512 prefixEnd_6891512 3538658092227746161306519 := by
  unfold tailWord_6891512
  simp only [CollatzResearch.WordTrace]
  refine ⟨125677046104618237695410395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167569394806157650260547193 125677046104618237695410395)
  ·
    refine ⟨188515569156927356543115593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125677046104618237695410395 188515569156927356543115593)
    ·
      refine ⟨141386676867695517407336695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188515569156927356543115593 141386676867695517407336695)
      ·
        refine ⟨212080015301543276111005043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141386676867695517407336695 212080015301543276111005043)
        ·
          refine ⟨318120022952314914166507565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212080015301543276111005043 318120022952314914166507565)
          ·
            refine ⟨119295008607118092812440337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 318120022952314914166507565 119295008607118092812440337)
            ·
              refine ⟨89471256455338569609330253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119295008607118092812440337 89471256455338569609330253)
              ·
                refine ⟨33551721170751963603498845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89471256455338569609330253 33551721170751963603498845)
                ·
                  refine ⟨12581895439031986351312067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33551721170751963603498845 12581895439031986351312067)
                  ·
                    refine ⟨18872843158547979526968101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12581895439031986351312067 18872843158547979526968101)
                    ·
                      refine ⟨3538658092227746161306519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18872843158547979526968101 3538658092227746161306519)
                      ·
                        rfl

theorem cell23_6891512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 3, 1, 4].length) (baseStart_6891512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891512 prefixEnd_6891512 := by exact prefixLift 6891512
  have htrace : WordTrace (prefixWord ++ tailWord_6891512) baseStart_6891512 baseEnd_6891512 := by
    simpa [prefixWord, tailWord_6891512, baseEnd_6891512] using wordTrace_append hprefix tailTrace_6891512
  have hstable : (prefixWord ++ tailWord_6891512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891512).length < 2 ^ (prefixWord ++ tailWord_6891512).sum := by decide
  have hdescent : baseEnd_6891512 < baseStart_6891512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891549 : List Nat := [1, 4, 2, 2, 2, 1, 2, 2, 1, 1, 5]
def baseStart_6891549 : Nat := 118140960795 + 6891549 * 2 ^ 59
def prefixEnd_6891549 : Nat := 4983230072969 + 3 ^ 40 * 6891549 * 2
def baseEnd_6891549 : Nat := 3538677091011962516543849

theorem tailTrace_6891549 : CollatzResearch.WordTrace tailWord_6891549 prefixEnd_6891549 3538677091011962516543849 := by
  unfold tailWord_6891549
  simp only [CollatzResearch.WordTrace]
  refine ⟨251355441710102430709917701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167570294473401620473278467 251355441710102430709917701)
  ·
    refine ⟨47129145320644205758109569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 251355441710102430709917701 47129145320644205758109569)
    ·
      refine ⟨35346858990483154318582177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47129145320644205758109569 35346858990483154318582177)
      ·
        refine ⟨26510144242862365738936633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35346858990483154318582177 26510144242862365738936633)
        ·
          refine ⟨19882608182146774304202475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26510144242862365738936633 19882608182146774304202475)
          ·
            refine ⟨29823912273220161456303713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19882608182146774304202475 29823912273220161456303713)
            ·
              refine ⟨22367934204915121092227785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29823912273220161456303713 22367934204915121092227785)
              ·
                refine ⟨16775950653686340819170839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22367934204915121092227785 16775950653686340819170839)
                ·
                  refine ⟨25163925980529511228756259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16775950653686340819170839 25163925980529511228756259)
                  ·
                    refine ⟨37745888970794266843134389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25163925980529511228756259 37745888970794266843134389)
                    ·
                      refine ⟨3538677091011962516543849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37745888970794266843134389 3538677091011962516543849)
                      ·
                        rfl

theorem cell23_6891549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_6891549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891549 prefixEnd_6891549 := by exact prefixLift 6891549
  have htrace : WordTrace (prefixWord ++ tailWord_6891549) baseStart_6891549 baseEnd_6891549 := by
    simpa [prefixWord, tailWord_6891549, baseEnd_6891549] using wordTrace_append hprefix tailTrace_6891549
  have hstable : (prefixWord ++ tailWord_6891549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891549).length < 2 ^ (prefixWord ++ tailWord_6891549).sum := by decide
  have hdescent : baseEnd_6891549 < baseStart_6891549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891560 : List Nat := [2, 1, 5, 3, 2, 1, 1, 2, 1, 5]
def baseStart_6891560 : Nat := 118140960795 + 6891560 * 2 ^ 59
def prefixEnd_6891560 : Nat := 4983230072969 + 3 ^ 40 * 6891560 * 2
def baseEnd_6891560 : Nat := 1179560913099720657835433

theorem tailTrace_6891560 : CollatzResearch.WordTrace tailWord_6891560 prefixEnd_6891560 1179560913099720657835433 := by
  unfold tailWord_6891560
  simp only [CollatzResearch.WordTrace]
  refine ⟨125677921456531289794284067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167570561942041719725712089 125677921456531289794284067)
  ·
    refine ⟨188516882184796934691426101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125677921456531289794284067 188516882184796934691426101)
    ·
      refine ⟨17673457704824712627321197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 188516882184796934691426101 17673457704824712627321197)
      ·
        refine ⟨6627546639309267235245449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17673457704824712627321197 6627546639309267235245449)
        ·
          refine ⟨4970659979481950426434087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6627546639309267235245449 4970659979481950426434087)
          ·
            refine ⟨7455989969222925639651131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4970659979481950426434087 7455989969222925639651131)
            ·
              refine ⟨11183984953834388459476697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7455989969222925639651131 11183984953834388459476697)
              ·
                refine ⟨8387988715375791344607523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11183984953834388459476697 8387988715375791344607523)
                ·
                  refine ⟨12581983073063687016911285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8387988715375791344607523 12581983073063687016911285)
                  ·
                    refine ⟨1179560913099720657835433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12581983073063687016911285 1179560913099720657835433)
                    ·
                      rfl

theorem cell23_6891560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_6891560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891560 prefixEnd_6891560 := by exact prefixLift 6891560
  have htrace : WordTrace (prefixWord ++ tailWord_6891560) baseStart_6891560 baseEnd_6891560 := by
    simpa [prefixWord, tailWord_6891560, baseEnd_6891560] using wordTrace_append hprefix tailTrace_6891560
  have hstable : (prefixWord ++ tailWord_6891560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891560).length < 2 ^ (prefixWord ++ tailWord_6891560).sum := by decide
  have hdescent : baseEnd_6891560 < baseStart_6891560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891566 : List Nat := [4, 1, 3, 1, 1, 3, 1, 1, 3, 2, 3]
def baseStart_6891566 : Nat := 118140960795 + 6891566 * 2 ^ 59
def prefixEnd_6891566 : Nat := 4983230072969 + 3 ^ 40 * 6891566 * 2
def baseEnd_6891566 : Nat := 3538685820183088950031271

theorem tailTrace_6891566 : CollatzResearch.WordTrace tailWord_6891566 prefixEnd_6891566 3538685820183088950031271 := by
  unfold tailWord_6891566
  simp only [CollatzResearch.WordTrace]
  refine ⟨31419507718880105326660819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167570707834027228408857701 31419507718880105326660819)
  ·
    refine ⟨47129261578320157989991229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31419507718880105326660819 47129261578320157989991229)
    ·
      refine ⟨17673473091870059246246711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47129261578320157989991229 17673473091870059246246711)
      ·
        refine ⟨26510209637805088869370067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17673473091870059246246711 26510209637805088869370067)
        ·
          refine ⟨39765314456707633304055101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26510209637805088869370067 39765314456707633304055101)
          ·
            refine ⟨14911992921265362489020663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39765314456707633304055101 14911992921265362489020663)
            ·
              refine ⟨22367989381898043733530995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14911992921265362489020663 22367989381898043733530995)
              ·
                refine ⟨33551984072847065600296493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22367989381898043733530995 33551984072847065600296493)
                ·
                  refine ⟨12581994027317649600111185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33551984072847065600296493 12581994027317649600111185)
                  ·
                    refine ⟨9436495520488237200083389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12581994027317649600111185 9436495520488237200083389)
                    ·
                      refine ⟨3538685820183088950031271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9436495520488237200083389 3538685820183088950031271)
                      ·
                        rfl

theorem cell23_6891566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_6891566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891566 prefixEnd_6891566 := by exact prefixLift 6891566
  have htrace : WordTrace (prefixWord ++ tailWord_6891566) baseStart_6891566 baseEnd_6891566 := by
    simpa [prefixWord, tailWord_6891566, baseEnd_6891566] using wordTrace_append hprefix tailTrace_6891566
  have hstable : (prefixWord ++ tailWord_6891566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891566).length < 2 ^ (prefixWord ++ tailWord_6891566).sum := by decide
  have hdescent : baseEnd_6891566 < baseStart_6891566 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891596 : List Nat := [2, 2, 1, 3, 1, 1, 3, 4, 2, 1, 3]
def baseStart_6891596 : Nat := 118140960795 + 6891596 * 2 ^ 59
def prefixEnd_6891596 : Nat := 4983230072969 + 3 ^ 40 * 6891596 * 2
def baseEnd_6891596 : Nat := 3538701224602723832656133

theorem tailTrace_6891596 : CollatzResearch.WordTrace tailWord_6891596 prefixEnd_6891596 3538701224602723832656133 := by
  unfold tailWord_6891596
  simp only [CollatzResearch.WordTrace]
  refine ⟨125678577970466078868439321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167571437293954771824585761 125678577970466078868439321)
  ·
    refine ⟨94258933477849559151329491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125678577970466078868439321 94258933477849559151329491)
    ·
      refine ⟨141388400216774338726994237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94258933477849559151329491 141388400216774338726994237)
      ·
        refine ⟨53020650081290377022622839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141388400216774338726994237 53020650081290377022622839)
        ·
          refine ⟨79530975121935565533934259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53020650081290377022622839 79530975121935565533934259)
          ·
            refine ⟨119296462682903348300901389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79530975121935565533934259 119296462682903348300901389)
            ·
              refine ⟨44736173506088755612838021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119296462682903348300901389 44736173506088755612838021)
              ·
                refine ⟨8388032532391641677407129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44736173506088755612838021 8388032532391641677407129)
                ·
                  refine ⟨6291024399293731258055347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8388032532391641677407129 6291024399293731258055347)
                  ·
                    refine ⟨9436536598940596887083021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6291024399293731258055347 9436536598940596887083021)
                    ·
                      refine ⟨3538701224602723832656133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9436536598940596887083021 3538701224602723832656133)
                      ·
                        rfl

theorem cell23_6891596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_6891596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891596 prefixEnd_6891596 := by exact prefixLift 6891596
  have htrace : WordTrace (prefixWord ++ tailWord_6891596) baseStart_6891596 baseEnd_6891596 := by
    simpa [prefixWord, tailWord_6891596, baseEnd_6891596] using wordTrace_append hprefix tailTrace_6891596
  have hstable : (prefixWord ++ tailWord_6891596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891596).length < 2 ^ (prefixWord ++ tailWord_6891596).sum := by decide
  have hdescent : baseEnd_6891596 < baseStart_6891596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891613 : List Nat := [1, 4, 4, 1, 1, 2, 2, 1, 1, 3, 3]
def baseStart_6891613 : Nat := 118140960795 + 6891613 * 2 ^ 59
def prefixEnd_6891613 : Nat := 4983230072969 + 3 ^ 40 * 6891613 * 2
def baseEnd_6891613 : Nat := 3538709953773850266143555

theorem tailTrace_6891613 : CollatzResearch.WordTrace tailWord_6891613 prefixEnd_6891613 3538709953773850266143555 := by
  unfold tailWord_6891613
  simp only [CollatzResearch.WordTrace]
  refine ⟨251357775981870569640247493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167571850654580379760164995 251357775981870569640247493)
  ·
    refine ⟨47129582996600731807546405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 251357775981870569640247493 47129582996600731807546405)
    ·
      refine ⟨8836796811862637213914951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47129582996600731807546405 8836796811862637213914951)
      ·
        refine ⟨13255195217793955820872427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8836796811862637213914951 13255195217793955820872427)
        ·
          refine ⟨19882792826690933731308641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13255195217793955820872427 19882792826690933731308641)
          ·
            refine ⟨14912094620018200298481481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19882792826690933731308641 14912094620018200298481481)
            ·
              refine ⟨11184070965013650223861111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14912094620018200298481481 11184070965013650223861111)
              ·
                refine ⟨16776106447520475335791667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11184070965013650223861111 16776106447520475335791667)
                ·
                  refine ⟨25164159671280713003687501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16776106447520475335791667 25164159671280713003687501)
                  ·
                    refine ⟨9436559876730267376382813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25164159671280713003687501 9436559876730267376382813)
                    ·
                      refine ⟨3538709953773850266143555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9436559876730267376382813 3538709953773850266143555)
                      ·
                        rfl

theorem cell23_6891613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_6891613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891613 prefixEnd_6891613 := by exact prefixLift 6891613
  have htrace : WordTrace (prefixWord ++ tailWord_6891613) baseStart_6891613 baseEnd_6891613 := by
    simpa [prefixWord, tailWord_6891613, baseEnd_6891613] using wordTrace_append hprefix tailTrace_6891613
  have hstable : (prefixWord ++ tailWord_6891613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891613).length < 2 ^ (prefixWord ++ tailWord_6891613).sum := by decide
  have hdescent : baseEnd_6891613 < baseStart_6891613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891653 : List Nat := [1, 3, 1, 1, 5, 2, 1, 1, 4, 2, 2]
def baseStart_6891653 : Nat := 118140960795 + 6891653 * 2 ^ 59
def prefixEnd_6891653 : Nat := 4983230072969 + 3 ^ 40 * 6891653 * 2
def baseEnd_6891653 : Nat := 3538730493000030109643371

theorem tailTrace_6891653 : CollatzResearch.WordTrace tailWord_6891653 prefixEnd_6891653 3538730493000030109643371 := by
  unfold tailWord_6891653
  simp only [CollatzResearch.WordTrace]
  refine ⟨251359234901725656471703613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167572823267817104314469075 251359234901725656471703613)
  ·
    refine ⟨94259713088147121176888855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251359234901725656471703613 94259713088147121176888855)
    ·
      refine ⟨141389569632220681765333283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94259713088147121176888855 141389569632220681765333283)
      ·
        refine ⟨212084354448331022647999925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141389569632220681765333283 212084354448331022647999925)
        ·
          refine ⟨19882908229531033373249993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 212084354448331022647999925 19882908229531033373249993)
          ·
            refine ⟨14912181172148275029937495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19882908229531033373249993 14912181172148275029937495)
            ·
              refine ⟨22368271758222412544906243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14912181172148275029937495 22368271758222412544906243)
              ·
                refine ⟨33552407637333618817359365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22368271758222412544906243 33552407637333618817359365)
                ·
                  refine ⟨6291076432000053528254881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33552407637333618817359365 6291076432000053528254881)
                  ·
                    refine ⟨4718307324000040146191161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6291076432000053528254881 4718307324000040146191161)
                    ·
                      refine ⟨3538730493000030109643371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4718307324000040146191161 3538730493000030109643371)
                      ·
                        rfl

theorem cell23_6891653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 4, 2, 2].length) (baseStart_6891653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891653 prefixEnd_6891653 := by exact prefixLift 6891653
  have htrace : WordTrace (prefixWord ++ tailWord_6891653) baseStart_6891653 baseEnd_6891653 := by
    simpa [prefixWord, tailWord_6891653, baseEnd_6891653] using wordTrace_append hprefix tailTrace_6891653
  have hstable : (prefixWord ++ tailWord_6891653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891653).length < 2 ^ (prefixWord ++ tailWord_6891653).sum := by decide
  have hdescent : baseEnd_6891653 < baseStart_6891653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891669 : List Nat := [1, 3, 2, 1, 1, 1, 3, 3, 2, 3, 3]
def baseStart_6891669 : Nat := 118140960795 + 6891669 * 2 ^ 59
def prefixEnd_6891669 : Nat := 4983230072969 + 3 ^ 40 * 6891669 * 2
def baseEnd_6891669 : Nat := 3538738708690502047043297

theorem tailTrace_6891669 : CollatzResearch.WordTrace tailWord_6891669 prefixEnd_6891669 3538738708690502047043297 := by
  unfold tailWord_6891669
  simp only [CollatzResearch.WordTrace]
  refine ⟨251359818469667691204286061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167573212313111794136190707 251359818469667691204286061)
  ·
    refine ⟨94259931926125384201607273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251359818469667691204286061 94259931926125384201607273)
    ·
      refine ⟨70694948944594038151205455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94259931926125384201607273 70694948944594038151205455)
      ·
        refine ⟨106042423416891057226808183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70694948944594038151205455 106042423416891057226808183)
        ·
          refine ⟨159063635125336585840212275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106042423416891057226808183 159063635125336585840212275)
          ·
            refine ⟨238595452688004878760318413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159063635125336585840212275 238595452688004878760318413)
            ·
              refine ⟨89473294758001829535119405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 238595452688004878760318413 89473294758001829535119405)
              ·
                refine ⟨33552485534250686075669777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89473294758001829535119405 33552485534250686075669777)
                ·
                  refine ⟨25164364150688014556752333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33552485534250686075669777 25164364150688014556752333)
                  ·
                    refine ⟨9436636556508005458782125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25164364150688014556752333 9436636556508005458782125)
                    ·
                      refine ⟨3538738708690502047043297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9436636556508005458782125 3538738708690502047043297)
                      ·
                        rfl

theorem cell23_6891669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 3, 3].length) (baseStart_6891669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891669 prefixEnd_6891669 := by exact prefixLift 6891669
  have htrace : WordTrace (prefixWord ++ tailWord_6891669) baseStart_6891669 baseEnd_6891669 := by
    simpa [prefixWord, tailWord_6891669, baseEnd_6891669] using wordTrace_append hprefix tailTrace_6891669
  have hstable : (prefixWord ++ tailWord_6891669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891669).length < 2 ^ (prefixWord ++ tailWord_6891669).sum := by decide
  have hdescent : baseEnd_6891669 < baseStart_6891669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891692 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 8]
def baseStart_6891692 : Nat := 118140960795 + 6891692 * 2 ^ 59
def prefixEnd_6891692 : Nat := 4983230072969 + 3 ^ 40 * 6891692 * 2
def baseEnd_6891692 : Nat := 3538750518745555457055691

theorem tailTrace_6891692 : CollatzResearch.WordTrace tailWord_6891692 prefixEnd_6891692 3538750518745555457055691 := by
  unfold tailWord_6891692
  simp only [CollatzResearch.WordTrace]
  refine ⟨125680328674292183066186665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167573771565722910754915553 125680328674292183066186665)
  ·
    refine ⟨94260246505719137299639999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125680328674292183066186665 94260246505719137299639999)
    ·
      refine ⟨141390369758578705949459999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94260246505719137299639999 141390369758578705949459999)
      ·
        refine ⟨212085554637868058924189999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141390369758578705949459999 212085554637868058924189999)
        ·
          refine ⟨318128331956802088386284999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212085554637868058924189999 318128331956802088386284999)
          ·
            refine ⟨477192497935203132579427499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318128331956802088386284999 477192497935203132579427499)
            ·
              refine ⟨715788746902804698869141249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 477192497935203132579427499 715788746902804698869141249)
              ·
                refine ⟨536841560177103524151855937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 715788746902804698869141249 536841560177103524151855937)
                ·
                  refine ⟨402631170132827643113891953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 536841560177103524151855937 402631170132827643113891953)
                  ·
                    refine ⟨301973377599620732335418965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 402631170132827643113891953 301973377599620732335418965)
                    ·
                      refine ⟨3538750518745555457055691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 301973377599620732335418965 3538750518745555457055691)
                      ·
                        rfl

theorem cell23_6891692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_6891692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891692 prefixEnd_6891692 := by exact prefixLift 6891692
  have htrace : WordTrace (prefixWord ++ tailWord_6891692) baseStart_6891692 baseEnd_6891692 := by
    simpa [prefixWord, tailWord_6891692, baseEnd_6891692] using wordTrace_append hprefix tailTrace_6891692
  have hstable : (prefixWord ++ tailWord_6891692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891692).length < 2 ^ (prefixWord ++ tailWord_6891692).sum := by decide
  have hdescent : baseEnd_6891692 < baseStart_6891692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891693 : List Nat := [1, 5, 2, 1, 2, 1, 3, 3, 5]
def baseStart_6891693 : Nat := 118140960795 + 6891693 * 2 ^ 59
def prefixEnd_6891693 : Nat := 4983230072969 + 3 ^ 40 * 6891693 * 2
def baseEnd_6891693 : Nat := 393194559136245550349243

theorem tailTrace_6891693 : CollatzResearch.WordTrace tailWord_6891693 prefixEnd_6891693 393194559136245550349243 := by
  unfold tailWord_6891693
  simp only [CollatzResearch.WordTrace]
  refine ⟨251360693821580743303159733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167573795881053828868773155 251360693821580743303159733)
  ·
    refine ⟨23565065045773194684671225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 251360693821580743303159733 23565065045773194684671225)
    ·
      refine ⟨17673798784329896013503419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23565065045773194684671225 17673798784329896013503419)
      ·
        refine ⟨26510698176494844020255129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17673798784329896013503419 26510698176494844020255129)
        ·
          refine ⟨19883023632371133015191347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26510698176494844020255129 19883023632371133015191347)
          ·
            refine ⟨29824535448556699522787021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19883023632371133015191347 29824535448556699522787021)
            ·
              refine ⟨11184200793208762321045133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29824535448556699522787021 11184200793208762321045133)
              ·
                refine ⟨4194075297453285870391925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11184200793208762321045133 4194075297453285870391925)
                ·
                  refine ⟨393194559136245550349243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4194075297453285870391925 393194559136245550349243)
                  ·
                    rfl

theorem cell23_6891693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_6891693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891693 prefixEnd_6891693 := by exact prefixLift 6891693
  have htrace : WordTrace (prefixWord ++ tailWord_6891693) baseStart_6891693 baseEnd_6891693 := by
    simpa [prefixWord, tailWord_6891693, baseEnd_6891693] using wordTrace_append hprefix tailTrace_6891693
  have hstable : (prefixWord ++ tailWord_6891693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891693).length < 2 ^ (prefixWord ++ tailWord_6891693).sum := by decide
  have hdescent : baseEnd_6891693 < baseStart_6891693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891710 : List Nat := [4, 2, 1, 1, 4, 1, 3, 2, 5]
def baseStart_6891710 : Nat := 118140960795 + 6891710 * 2 ^ 59
def prefixEnd_6891710 : Nat := 4983230072969 + 3 ^ 40 * 6891710 * 2
def baseEnd_6891710 : Nat := 393195529044148487403401

theorem tailTrace_6891710 : CollatzResearch.WordTrace tailWord_6891710 prefixEnd_6891710 393195529044148487403401 := by
  unfold tailWord_6891710
  simp only [CollatzResearch.WordTrace]
  refine ⟨31420164232814894400816073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167574209241679436804352389 31420164232814894400816073)
  ·
    refine ⟨23565123174611170800612055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31420164232814894400816073 23565123174611170800612055)
    ·
      refine ⟨35347684761916756200918083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23565123174611170800612055 35347684761916756200918083)
      ·
        refine ⟨53021527142875134301377125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35347684761916756200918083 53021527142875134301377125)
        ·
          refine ⟨9941536339289087681508211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53021527142875134301377125 9941536339289087681508211)
          ·
            refine ⟨14912304508933631522262317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9941536339289087681508211 14912304508933631522262317)
            ·
              refine ⟨5592114190850111820848369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14912304508933631522262317 5592114190850111820848369)
              ·
                refine ⟨4194085643137583865636277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5592114190850111820848369 4194085643137583865636277)
                ·
                  refine ⟨393195529044148487403401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4194085643137583865636277 393195529044148487403401)
                  ·
                    rfl

theorem cell23_6891710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_6891710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891710 prefixEnd_6891710 := by exact prefixLift 6891710
  have htrace : WordTrace (prefixWord ++ tailWord_6891710) baseStart_6891710 baseEnd_6891710 := by
    simpa [prefixWord, tailWord_6891710, baseEnd_6891710] using wordTrace_append hprefix tailTrace_6891710
  have hstable : (prefixWord ++ tailWord_6891710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891710).length < 2 ^ (prefixWord ++ tailWord_6891710).sum := by decide
  have hdescent : baseEnd_6891710 < baseStart_6891710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891716 : List Nat := [2, 3, 3, 1, 2, 2, 1, 1, 1, 2, 5]
def baseStart_6891716 : Nat := 118140960795 + 6891716 * 2 ^ 59
def prefixEnd_6891716 : Nat := 4983230072969 + 3 ^ 40 * 6891716 * 2
def baseEnd_6891716 : Nat := 3538762842281263363155581

theorem tailTrace_6891716 : CollatzResearch.WordTrace tailWord_6891716 prefixEnd_6891716 3538762842281263363155581 := by
  unfold tailWord_6891716
  simp only [CollatzResearch.WordTrace]
  refine ⟨125680766350248709115623501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167574355133664945487498001 125680766350248709115623501)
  ·
    refine ⟨47130287381343265918358813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125680766350248709115623501 47130287381343265918358813)
    ·
      refine ⟨17673857768003724719384555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47130287381343265918358813 17673857768003724719384555)
      ·
        refine ⟨26510786652005587079076833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17673857768003724719384555 26510786652005587079076833)
        ·
          refine ⟨19883089989004190309307625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26510786652005587079076833 19883089989004190309307625)
          ·
            refine ⟨14912317491753142731980719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19883089989004190309307625 14912317491753142731980719)
            ·
              refine ⟨22368476237629714097971079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14912317491753142731980719 22368476237629714097971079)
              ·
                refine ⟨33552714356444571146956619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22368476237629714097971079 33552714356444571146956619)
                ·
                  refine ⟨50329071534666856720434929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33552714356444571146956619 50329071534666856720434929)
                  ·
                    refine ⟨37746803651000142540326197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50329071534666856720434929 37746803651000142540326197)
                    ·
                      refine ⟨3538762842281263363155581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37746803651000142540326197 3538762842281263363155581)
                      ·
                        rfl

theorem cell23_6891716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_6891716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891716 prefixEnd_6891716 := by exact prefixLift 6891716
  have htrace : WordTrace (prefixWord ++ tailWord_6891716) baseStart_6891716 baseEnd_6891716 := by
    simpa [prefixWord, tailWord_6891716, baseEnd_6891716] using wordTrace_append hprefix tailTrace_6891716
  have hstable : (prefixWord ++ tailWord_6891716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891716).length < 2 ^ (prefixWord ++ tailWord_6891716).sum := by decide
  have hdescent : baseEnd_6891716 < baseStart_6891716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891729 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 3, 4, 3]
def baseStart_6891729 : Nat := 118140960795 + 6891729 * 2 ^ 59
def prefixEnd_6891729 : Nat := 4983230072969 + 3 ^ 40 * 6891729 * 2
def baseEnd_6891729 : Nat := 3538769517529771812293021

theorem tailTrace_6891729 : CollatzResearch.WordTrace tailWord_6891729 prefixEnd_6891729 3538769517529771812293021 := by
  unfold tailWord_6891729
  simp only [CollatzResearch.WordTrace]
  refine ⟨251362006849450321451470241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167574671232966880967646827 251362006849450321451470241)
  ·
    refine ⟨188521505137087741088602681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251362006849450321451470241 188521505137087741088602681)
    ·
      refine ⟨141391128852815805816452011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188521505137087741088602681 141391128852815805816452011)
      ·
        refine ⟨212086693279223708724678017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141391128852815805816452011 212086693279223708724678017)
        ·
          refine ⟨159065019959417781543508513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212086693279223708724678017 159065019959417781543508513)
          ·
            refine ⟨119298764969563336157631385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159065019959417781543508513 119298764969563336157631385)
            ·
              refine ⟨89474073727172502118223539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119298764969563336157631385 89474073727172502118223539)
              ·
                refine ⟨134211110590758753177335309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89474073727172502118223539 134211110590758753177335309)
                ·
                  refine ⟨50329166471534532441500741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134211110590758753177335309 50329166471534532441500741)
                  ·
                    refine ⟨9436718713412724832781389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50329166471534532441500741 9436718713412724832781389)
                    ·
                      refine ⟨3538769517529771812293021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9436718713412724832781389 3538769517529771812293021)
                      ·
                        rfl

theorem cell23_6891729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 4, 3].length) (baseStart_6891729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891729 prefixEnd_6891729 := by exact prefixLift 6891729
  have htrace : WordTrace (prefixWord ++ tailWord_6891729) baseStart_6891729 baseEnd_6891729 := by
    simpa [prefixWord, tailWord_6891729, baseEnd_6891729] using wordTrace_append hprefix tailTrace_6891729
  have hstable : (prefixWord ++ tailWord_6891729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891729).length < 2 ^ (prefixWord ++ tailWord_6891729).sum := by decide
  have hdescent : baseEnd_6891729 < baseStart_6891729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891740 : List Nat := [2, 2, 5, 2, 1, 1, 2, 1, 2, 5]
def baseStart_6891740 : Nat := 118140960795 + 6891740 * 2 ^ 59
def prefixEnd_6891740 : Nat := 4983230072969 + 3 ^ 40 * 6891740 * 2
def baseEnd_6891740 : Nat := 1179591721938990423085157

theorem tailTrace_6891740 : CollatzResearch.WordTrace tailWord_6891740 prefixEnd_6891740 1179591721938990423085157 := by
  unfold tailWord_6891740
  simp only [CollatzResearch.WordTrace]
  refine ⟨125681204026205235165060337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167574938701606980220080449 125681204026205235165060337)
  ·
    refine ⟨94260903019653926373795253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125681204026205235165060337 94260903019653926373795253)
    ·
      refine ⟨8836959658092555597543305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94260903019653926373795253 8836959658092555597543305)
      ·
        refine ⟨6627719743569416698157479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8836959658092555597543305 6627719743569416698157479)
        ·
          refine ⟨9941579615354125047236219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6627719743569416698157479 9941579615354125047236219)
          ·
            refine ⟨14912369423031187570854329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9941579615354125047236219 14912369423031187570854329)
            ·
              refine ⟨11184277067273390678140747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14912369423031187570854329 11184277067273390678140747)
              ·
                refine ⟨16776415600910086017211121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11184277067273390678140747 16776415600910086017211121)
                ·
                  refine ⟨12582311700682564512908341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16776415600910086017211121 12582311700682564512908341)
                  ·
                    refine ⟨1179591721938990423085157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12582311700682564512908341 1179591721938990423085157)
                    ·
                      rfl

theorem cell23_6891740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_6891740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891740 prefixEnd_6891740 := by exact prefixLift 6891740
  have htrace : WordTrace (prefixWord ++ tailWord_6891740) baseStart_6891740 baseEnd_6891740 := by
    simpa [prefixWord, tailWord_6891740, baseEnd_6891740] using wordTrace_append hprefix tailTrace_6891740
  have hstable : (prefixWord ++ tailWord_6891740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891740).length < 2 ^ (prefixWord ++ tailWord_6891740).sum := by decide
  have hdescent : baseEnd_6891740 < baseStart_6891740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891766 : List Nat := [5, 1, 1, 1, 1, 1, 3, 4, 6]
def baseStart_6891766 : Nat := 118140960795 + 6891766 * 2 ^ 59
def prefixEnd_6891766 : Nat := 4983230072969 + 3 ^ 40 * 6891766 * 2
def baseEnd_6891766 : Nat := 393198724034887574170039

theorem tailTrace_6891766 : CollatzResearch.WordTrace tailWord_6891766 prefixEnd_6891766 393198724034887574170039 := by
  unfold tailWord_6891766
  simp only [CollatzResearch.WordTrace]
  refine ⟨15710209771894767298160447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167575570900210851180378101 15710209771894767298160447)
  ·
    refine ⟨23565314657842150947240671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15710209771894767298160447 23565314657842150947240671)
    ·
      refine ⟨35347971986763226420861007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23565314657842150947240671 35347971986763226420861007)
      ·
        refine ⟨53021957980144839631291511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35347971986763226420861007 53021957980144839631291511)
        ·
          refine ⟨79532936970217259446937267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53021957980144839631291511 79532936970217259446937267)
          ·
            refine ⟨119299405455325889170405901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79532936970217259446937267 119299405455325889170405901)
            ·
              refine ⟨44737277045747208438902213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119299405455325889170405901 44737277045747208438902213)
              ·
                refine ⟨8388239446077601582294165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44737277045747208438902213 8388239446077601582294165)
                ·
                  refine ⟨393198724034887574170039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8388239446077601582294165 393198724034887574170039)
                  ·
                    rfl

theorem cell23_6891766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_6891766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891766 prefixEnd_6891766 := by exact prefixLift 6891766
  have htrace : WordTrace (prefixWord ++ tailWord_6891766) baseStart_6891766 baseEnd_6891766 := by
    simpa [prefixWord, tailWord_6891766, baseEnd_6891766] using wordTrace_append hprefix tailTrace_6891766
  have hstable : (prefixWord ++ tailWord_6891766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891766).length < 2 ^ (prefixWord ++ tailWord_6891766).sum := by decide
  have hdescent : baseEnd_6891766 < baseStart_6891766 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891770 : List Nat := [3, 1, 1, 1, 1, 5, 4, 2, 1, 4]
def baseStart_6891770 : Nat := 118140960795 + 6891770 * 2 ^ 59
def prefixEnd_6891770 : Nat := 4983230072969 + 3 ^ 40 * 6891770 * 2
def baseEnd_6891770 : Nat := 1179596856745535383960111

theorem tailTrace_6891770 : CollatzResearch.WordTrace tailWord_6891770 prefixEnd_6891770 1179596856745535383960111 := by
  unfold tailWord_6891770
  simp only [CollatzResearch.WordTrace]
  refine ⟨62840875560575446363428191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167575668161534523635808509 62840875560575446363428191)
  ·
    refine ⟨94261313340863169545142287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62840875560575446363428191 94261313340863169545142287)
    ·
      refine ⟨141391970011294754317713431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94261313340863169545142287 141391970011294754317713431)
      ·
        refine ⟨212087955016942131476570147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141391970011294754317713431 212087955016942131476570147)
        ·
          refine ⟨318131932525413197214855221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212087955016942131476570147 318131932525413197214855221)
          ·
            refine ⟨29824868674257487238892677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 318131932525413197214855221 29824868674257487238892677)
            ·
              refine ⟨5592162876423278857292377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29824868674257487238892677 5592162876423278857292377)
              ·
                refine ⟨4194122157317459142969283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5592162876423278857292377 4194122157317459142969283)
                ·
                  refine ⟨6291183235976188714453925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4194122157317459142969283 6291183235976188714453925)
                  ·
                    refine ⟨1179596856745535383960111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6291183235976188714453925 1179596856745535383960111)
                    ·
                      rfl

theorem cell23_6891770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 2, 1, 4].length) (baseStart_6891770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891770 prefixEnd_6891770 := by exact prefixLift 6891770
  have htrace : WordTrace (prefixWord ++ tailWord_6891770) baseStart_6891770 baseEnd_6891770 := by
    simpa [prefixWord, tailWord_6891770, baseEnd_6891770] using wordTrace_append hprefix tailTrace_6891770
  have hstable : (prefixWord ++ tailWord_6891770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891770).length < 2 ^ (prefixWord ++ tailWord_6891770).sum := by decide
  have hdescent : baseEnd_6891770 < baseStart_6891770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891779 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 5, 5]
def baseStart_6891779 : Nat := 118140960795 + 6891779 * 2 ^ 59
def prefixEnd_6891779 : Nat := 4983230072969 + 3 ^ 40 * 6891779 * 2
def baseEnd_6891779 : Nat := 1179598397187498872222597

theorem tailTrace_6891779 : CollatzResearch.WordTrace tailWord_6891779 prefixEnd_6891779 1179598397187498872222597 := by
  unfold tailWord_6891779
  simp only [CollatzResearch.WordTrace]
  refine ⟨251363830499269179990790391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167575886999512786660526927 251363830499269179990790391)
  ·
    refine ⟨377045745748903769986185587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251363830499269179990790391 377045745748903769986185587)
    ·
      refine ⟨565568618623355654979278381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377045745748903769986185587 565568618623355654979278381)
      ·
        refine ⟨212088231983758370617229393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 565568618623355654979278381 212088231983758370617229393)
        ·
          refine ⟨159066173987818777962922045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212088231983758370617229393 159066173987818777962922045)
          ·
            refine ⟨59649815245432041736095767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159066173987818777962922045 59649815245432041736095767)
            ·
              refine ⟨89474722868148062604143651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59649815245432041736095767 89474722868148062604143651)
              ·
                refine ⟨134212084302222093906215477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89474722868148062604143651 134212084302222093906215477)
                ·
                  refine ⟨12582382903333321303707701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134212084302222093906215477 12582382903333321303707701)
                  ·
                    refine ⟨1179598397187498872222597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12582382903333321303707701 1179598397187498872222597)
                    ·
                      rfl

theorem cell23_6891779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5, 5].length) (baseStart_6891779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891779 prefixEnd_6891779 := by exact prefixLift 6891779
  have htrace : WordTrace (prefixWord ++ tailWord_6891779) baseStart_6891779 baseEnd_6891779 := by
    simpa [prefixWord, tailWord_6891779, baseEnd_6891779] using wordTrace_append hprefix tailTrace_6891779
  have hstable : (prefixWord ++ tailWord_6891779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891779).length < 2 ^ (prefixWord ++ tailWord_6891779).sum := by decide
  have hdescent : baseEnd_6891779 < baseStart_6891779 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891793 : List Nat := [1, 2, 2, 1, 1, 6, 1, 2, 3, 1, 3]
def baseStart_6891793 : Nat := 118140960795 + 6891793 * 2 ^ 59
def prefixEnd_6891793 : Nat := 4983230072969 + 3 ^ 40 * 6891793 * 2
def baseEnd_6891793 : Nat := 3538802380291659561892727

theorem tailTrace_6891793 : CollatzResearch.WordTrace tailWord_6891793 prefixEnd_6891793 3538802380291659561892727 := by
  unfold tailWord_6891793
  simp only [CollatzResearch.WordTrace]
  refine ⟨251364341121218460381800033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167576227414145640254533355 251364341121218460381800033)
  ·
    refine ⟨188523255840913845286350025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251364341121218460381800033 188523255840913845286350025)
    ·
      refine ⟨141392441880685383964762519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188523255840913845286350025 141392441880685383964762519)
      ·
        refine ⟨212088662821028075947143779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141392441880685383964762519 212088662821028075947143779)
        ·
          refine ⟨318132994231542113920715669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212088662821028075947143779 318132994231542113920715669)
          ·
            refine ⟨14912484104603536590033547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 318132994231542113920715669 14912484104603536590033547)
            ·
              refine ⟨22368726156905304885050321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14912484104603536590033547 22368726156905304885050321)
              ·
                refine ⟨16776544617678978663787741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22368726156905304885050321 16776544617678978663787741)
                ·
                  refine ⟨6291204231629616998920403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16776544617678978663787741 6291204231629616998920403)
                  ·
                    refine ⟨9436806347444425498380605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6291204231629616998920403 9436806347444425498380605)
                    ·
                      refine ⟨3538802380291659561892727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9436806347444425498380605 3538802380291659561892727)
                      ·
                        rfl

theorem cell23_6891793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 3, 1, 3].length) (baseStart_6891793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891793 prefixEnd_6891793 := by exact prefixLift 6891793
  have htrace : WordTrace (prefixWord ++ tailWord_6891793) baseStart_6891793 baseEnd_6891793 := by
    simpa [prefixWord, tailWord_6891793, baseEnd_6891793] using wordTrace_append hprefix tailTrace_6891793
  have hstable : (prefixWord ++ tailWord_6891793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891793).length < 2 ^ (prefixWord ++ tailWord_6891793).sum := by decide
  have hdescent : baseEnd_6891793 < baseStart_6891793 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891803 : List Nat := [1, 1, 1, 1, 1, 1, 9, 1, 2, 3, 2]
def baseStart_6891803 : Nat := 118140960795 + 6891803 * 2 ^ 59
def prefixEnd_6891803 : Nat := 4983230072969 + 3 ^ 40 * 6891803 * 2
def baseEnd_6891803 : Nat := 3538807515098204522767681

theorem tailTrace_6891803 : CollatzResearch.WordTrace tailWord_6891803 prefixEnd_6891803 3538807515098204522767681 := by
  unfold tailWord_6891803
  simp only [CollatzResearch.WordTrace]
  refine ⟨251364705851182232089664063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167576470567454821393109375 251364705851182232089664063)
  ·
    refine ⟨377047058776773348134496095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251364705851182232089664063 377047058776773348134496095)
    ·
      refine ⟨565570588165160022201744143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377047058776773348134496095 565570588165160022201744143)
      ·
        refine ⟨848355882247740033302616215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565570588165160022201744143 848355882247740033302616215)
        ·
          refine ⟨1272533823371610049953924323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 848355882247740033302616215 1272533823371610049953924323)
          ·
            refine ⟨1908800735057415074930886485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1272533823371610049953924323 1908800735057415074930886485)
            ·
              refine ⟨11184379306977041454673163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1908800735057415074930886485 11184379306977041454673163)
              ·
                refine ⟨16776568960465562182009745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11184379306977041454673163 16776568960465562182009745)
                ·
                  refine ⟨12582426720349171636507309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16776568960465562182009745 12582426720349171636507309)
                  ·
                    refine ⟨4718410020130939363690241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12582426720349171636507309 4718410020130939363690241)
                    ·
                      refine ⟨3538807515098204522767681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4718410020130939363690241 3538807515098204522767681)
                      ·
                        rfl

theorem cell23_6891803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 2, 3, 2].length) (baseStart_6891803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891803 prefixEnd_6891803 := by exact prefixLift 6891803
  have htrace : WordTrace (prefixWord ++ tailWord_6891803) baseStart_6891803 baseEnd_6891803 := by
    simpa [prefixWord, tailWord_6891803, baseEnd_6891803] using wordTrace_append hprefix tailTrace_6891803
  have hstable : (prefixWord ++ tailWord_6891803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891803).length < 2 ^ (prefixWord ++ tailWord_6891803).sum := by decide
  have hdescent : baseEnd_6891803 < baseStart_6891803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891813 : List Nat := [1, 3, 1, 2, 5, 1, 1, 3, 1, 5]
def baseStart_6891813 : Nat := 118140960795 + 6891813 * 2 ^ 59
def prefixEnd_6891813 : Nat := 4983230072969 + 3 ^ 40 * 6891813 * 2
def baseEnd_6891813 : Nat := 1179604216634916494547545

theorem tailTrace_6891813 : CollatzResearch.WordTrace tailWord_6891813 prefixEnd_6891813 1179604216634916494547545 := by
  unfold tailWord_6891813
  simp only [CollatzResearch.WordTrace]
  refine ⟨251365070581146003797528093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167576713720764002531685395 251365070581146003797528093)
  ·
    refine ⟨94261901467929751424073035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251365070581146003797528093 94261901467929751424073035)
    ·
      refine ⟨141392852201894627136109553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94261901467929751424073035 141392852201894627136109553)
      ·
        refine ⟨106044639151420970352082165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141392852201894627136109553 106044639151420970352082165)
        ·
          refine ⟨9941684920445715970507703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106044639151420970352082165 9941684920445715970507703)
          ·
            refine ⟨14912527380668573955761555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9941684920445715970507703 14912527380668573955761555)
            ·
              refine ⟨22368791071002860933642333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14912527380668573955761555 22368791071002860933642333)
              ·
                refine ⟨8388296651626072850115875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22368791071002860933642333 8388296651626072850115875)
                ·
                  refine ⟨12582444977439109275173813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8388296651626072850115875 12582444977439109275173813)
                  ·
                    refine ⟨1179604216634916494547545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12582444977439109275173813 1179604216634916494547545)
                    ·
                      rfl

theorem cell23_6891813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3, 1, 5].length) (baseStart_6891813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891813 prefixEnd_6891813 := by exact prefixLift 6891813
  have htrace : WordTrace (prefixWord ++ tailWord_6891813) baseStart_6891813 baseEnd_6891813 := by
    simpa [prefixWord, tailWord_6891813, baseEnd_6891813] using wordTrace_append hprefix tailTrace_6891813
  have hstable : (prefixWord ++ tailWord_6891813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891813).length < 2 ^ (prefixWord ++ tailWord_6891813).sum := by decide
  have hdescent : baseEnd_6891813 < baseStart_6891813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891836 : List Nat := [2, 2, 2, 2, 1, 2, 3, 2, 1, 1, 5]
def baseStart_6891836 : Nat := 118140960795 + 6891836 * 2 ^ 59
def prefixEnd_6891836 : Nat := 4983230072969 + 3 ^ 40 * 6891836 * 2
def baseEnd_6891836 : Nat := 3538824459959802893655029

theorem tailTrace_6891836 : CollatzResearch.WordTrace tailWord_6891836 prefixEnd_6891836 3538824459959802893655029 := by
  unfold tailWord_6891836
  simp only [CollatzResearch.WordTrace]
  refine ⟨125682954730031339362807681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167577272973375119150410241 125682954730031339362807681)
  ·
    refine ⟨94262216047523504522105761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125682954730031339362807681 94262216047523504522105761)
    ·
      refine ⟨70696662035642628391579321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94262216047523504522105761 70696662035642628391579321)
      ·
        refine ⟨53022496526731971293684491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70696662035642628391579321 53022496526731971293684491)
        ·
          refine ⟨79533744790097956940526737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53022496526731971293684491 79533744790097956940526737)
          ·
            refine ⟨59650308592573467705395053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79533744790097956940526737 59650308592573467705395053)
            ·
              refine ⟨22368865722215050389523145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59650308592573467705395053 22368865722215050389523145)
              ·
                refine ⟨16776649291661287792142359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22368865722215050389523145 16776649291661287792142359)
                ·
                  refine ⟨25164973937491931688213539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16776649291661287792142359 25164973937491931688213539)
                  ·
                    refine ⟨37747460906237897532320309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25164973937491931688213539 37747460906237897532320309)
                    ·
                      refine ⟨3538824459959802893655029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37747460906237897532320309 3538824459959802893655029)
                      ·
                        rfl

theorem cell23_6891836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_6891836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891836 prefixEnd_6891836 := by exact prefixLift 6891836
  have htrace : WordTrace (prefixWord ++ tailWord_6891836) baseStart_6891836 baseEnd_6891836 := by
    simpa [prefixWord, tailWord_6891836, baseEnd_6891836] using wordTrace_append hprefix tailTrace_6891836
  have hstable : (prefixWord ++ tailWord_6891836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891836).length < 2 ^ (prefixWord ++ tailWord_6891836).sum := by decide
  have hdescent : baseEnd_6891836 < baseStart_6891836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891839 : List Nat := [1, 1, 2, 2, 4, 1, 2, 10]
def baseStart_6891839 : Nat := 118140960795 + 6891839 * 2 ^ 59
def prefixEnd_6891839 : Nat := 4983230072969 + 3 ^ 40 * 6891839 * 2
def baseEnd_6891839 : Nat := 131067629644509865996945

theorem tailTrace_6891839 : CollatzResearch.WordTrace tailWord_6891839 prefixEnd_6891839 131067629644509865996945 := by
  unfold tailWord_6891839
  simp only [CollatzResearch.WordTrace]
  refine ⟨251366018879051810237974571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167577345919367873491983047 251366018879051810237974571)
  ·
    refine ⟨377049028318577715356961857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251366018879051810237974571 377049028318577715356961857)
    ·
      refine ⟨282786771238933286517721393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377049028318577715356961857 282786771238933286517721393)
      ·
        refine ⟨212090078429199964888291045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282786771238933286517721393 212090078429199964888291045)
        ·
          refine ⟨39766889705474993416554571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212090078429199964888291045 39766889705474993416554571)
          ·
            refine ⟨59650334558212490124831857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39766889705474993416554571 59650334558212490124831857)
            ·
              refine ⟨44737750918659367593623893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59650334558212490124831857 44737750918659367593623893)
              ·
                refine ⟨131067629644509865996945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 44737750918659367593623893 131067629644509865996945)
                ·
                  rfl

theorem cell23_6891839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 10].length) (baseStart_6891839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891839 prefixEnd_6891839 := by exact prefixLift 6891839
  have htrace : WordTrace (prefixWord ++ tailWord_6891839) baseStart_6891839 baseEnd_6891839 := by
    simpa [prefixWord, tailWord_6891839, baseEnd_6891839] using wordTrace_append hprefix tailTrace_6891839
  have hstable : (prefixWord ++ tailWord_6891839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891839).length < 2 ^ (prefixWord ++ tailWord_6891839).sum := by decide
  have hdescent : baseEnd_6891839 < baseStart_6891839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891856 : List Nat := [2, 1, 1, 1, 1, 6, 4, 7]
def baseStart_6891856 : Nat := 118140960795 + 6891856 * 2 ^ 59
def prefixEnd_6891856 : Nat := 4983230072969 + 3 ^ 40 * 6891856 * 2
def baseEnd_6891856 : Nat := 131067952947144178348331

theorem tailTrace_6891856 : CollatzResearch.WordTrace tailWord_6891856 prefixEnd_6891856 131067952947144178348331 := by
  unfold tailWord_6891856
  simp only [CollatzResearch.WordTrace]
  refine ⟨125683319459995111070671711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167577759279993481427562281 125683319459995111070671711)
  ·
    refine ⟨188524979189992666606007567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125683319459995111070671711 188524979189992666606007567)
    ·
      refine ⟨282787468784988999909011351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188524979189992666606007567 282787468784988999909011351)
      ·
        refine ⟨424181203177483499863517027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282787468784988999909011351 424181203177483499863517027)
        ·
          refine ⟨636271804766225249795275541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424181203177483499863517027 636271804766225249795275541)
          ·
            refine ⟨29825240848416808584153541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 636271804766225249795275541 29825240848416808584153541)
            ·
              refine ⟨5592232659078151609528789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29825240848416808584153541 5592232659078151609528789)
              ·
                refine ⟨131067952947144178348331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5592232659078151609528789 131067952947144178348331)
                ·
                  rfl

theorem cell23_6891856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 7].length) (baseStart_6891856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891856 prefixEnd_6891856 := by exact prefixLift 6891856
  have htrace : WordTrace (prefixWord ++ tailWord_6891856) baseStart_6891856 baseEnd_6891856 := by
    simpa [prefixWord, tailWord_6891856, baseEnd_6891856] using wordTrace_append hprefix tailTrace_6891856
  have hstable : (prefixWord ++ tailWord_6891856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891856).length < 2 ^ (prefixWord ++ tailWord_6891856).sum := by decide
  have hdescent : baseEnd_6891856 < baseStart_6891856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891866 : List Nat := [3, 1, 1, 2, 1, 2, 1, 3, 3, 3, 3]
def baseStart_6891866 : Nat := 118140960795 + 6891866 * 2 ^ 59
def prefixEnd_6891866 : Nat := 4983230072969 + 3 ^ 40 * 6891866 * 2
def baseEnd_6891866 : Nat := 3538839864379437776279891

theorem tailTrace_6891866 : CollatzResearch.WordTrace tailWord_6891866 prefixEnd_6891866 3538839864379437776279891 := by
  unfold tailWord_6891866
  simp only [CollatzResearch.WordTrace]
  refine ⟨62841750912488498462301863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167578002433302662566138301 62841750912488498462301863)
  ·
    refine ⟨94262626368732747693452795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62841750912488498462301863 94262626368732747693452795)
    ·
      refine ⟨141393939553099121540179193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94262626368732747693452795 141393939553099121540179193)
      ·
        refine ⟨106045454664824341155134395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141393939553099121540179193 106045454664824341155134395)
        ·
          refine ⟨159068181997236511732701593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106045454664824341155134395 159068181997236511732701593)
          ·
            refine ⟨119301136497927383799526195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159068181997236511732701593 119301136497927383799526195)
            ·
              refine ⟨178951704746891075699289293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119301136497927383799526195 178951704746891075699289293)
              ·
                refine ⟨67106889280084153387233485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178951704746891075699289293 67106889280084153387233485)
                ·
                  refine ⟨25165083480031557520212557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67106889280084153387233485 25165083480031557520212557)
                  ·
                    refine ⟨9436906305011834070079709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25165083480031557520212557 9436906305011834070079709)
                    ·
                      refine ⟨3538839864379437776279891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9436906305011834070079709 3538839864379437776279891)
                      ·
                        rfl

theorem cell23_6891866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 3, 3, 3].length) (baseStart_6891866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891866 prefixEnd_6891866 := by exact prefixLift 6891866
  have htrace : WordTrace (prefixWord ++ tailWord_6891866) baseStart_6891866 baseEnd_6891866 := by
    simpa [prefixWord, tailWord_6891866, baseEnd_6891866] using wordTrace_append hprefix tailTrace_6891866
  have hstable : (prefixWord ++ tailWord_6891866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891866).length < 2 ^ (prefixWord ++ tailWord_6891866).sum := by decide
  have hdescent : baseEnd_6891866 < baseStart_6891866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891884 : List Nat := [2, 2, 1, 1, 7, 1, 1, 1, 3, 2, 2]
def baseStart_6891884 : Nat := 118140960795 + 6891884 * 2 ^ 59
def prefixEnd_6891884 : Nat := 4983230072969 + 3 ^ 40 * 6891884 * 2
def baseEnd_6891884 : Nat := 3538849107031218705854809

theorem tailTrace_6891884 : CollatzResearch.WordTrace tailWord_6891884 prefixEnd_6891884 3538849107031218705854809 := by
  unfold tailWord_6891884
  simp only [CollatzResearch.WordTrace]
  refine ⟨125683830081944391461681353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167578440109259188615575137 125683830081944391461681353)
  ·
    refine ⟨94262872561458293596261015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125683830081944391461681353 94262872561458293596261015)
    ·
      refine ⟨141394308842187440394391523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94262872561458293596261015 141394308842187440394391523)
      ·
        refine ⟨212091463263281160591587285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141394308842187440394391523 212091463263281160591587285)
        ·
          refine ⟨4970893670233152201365327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 212091463263281160591587285 4970893670233152201365327)
          ·
            refine ⟨7456340505349728302047991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4970893670233152201365327 7456340505349728302047991)
            ·
              refine ⟨11184510758024592453071987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7456340505349728302047991 11184510758024592453071987)
              ·
                refine ⟨16776766137036888679607981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11184510758024592453071987 16776766137036888679607981)
                ·
                  refine ⟨6291287301388833254852993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16776766137036888679607981 6291287301388833254852993)
                  ·
                    refine ⟨4718465476041624941139745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6291287301388833254852993 4718465476041624941139745)
                    ·
                      refine ⟨3538849107031218705854809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4718465476041624941139745 3538849107031218705854809)
                      ·
                        rfl

theorem cell23_6891884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 3, 2, 2].length) (baseStart_6891884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891884 prefixEnd_6891884 := by exact prefixLift 6891884
  have htrace : WordTrace (prefixWord ++ tailWord_6891884) baseStart_6891884 baseEnd_6891884 := by
    simpa [prefixWord, tailWord_6891884, baseEnd_6891884] using wordTrace_append hprefix tailTrace_6891884
  have hstable : (prefixWord ++ tailWord_6891884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891884).length < 2 ^ (prefixWord ++ tailWord_6891884).sum := by decide
  have hdescent : baseEnd_6891884 < baseStart_6891884 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891934 : List Nat := [4, 3, 1, 2, 1, 2, 2, 2, 2, 1, 3]
def baseStart_6891934 : Nat := 118140960795 + 6891934 * 2 ^ 59
def prefixEnd_6891934 : Nat := 4983230072969 + 3 ^ 40 * 6891934 * 2
def baseEnd_6891934 : Nat := 3538874781063943510229579

theorem tailTrace_6891934 : CollatzResearch.WordTrace tailWord_6891934 prefixEnd_6891934 3538874781063943510229579 := by
  unfold tailWord_6891934
  simp only [CollatzResearch.WordTrace]
  refine ⟨31421185476713455182835357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167579655875805094308455237 31421185476713455182835357)
  ·
    refine ⟨11782944553767545693563259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31421185476713455182835357 11782944553767545693563259)
    ·
      refine ⟨17674416830651318540344889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11782944553767545693563259 17674416830651318540344889)
      ·
        refine ⟨13255812622988488905258667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17674416830651318540344889 13255812622988488905258667)
        ·
          refine ⟨19883718934482733357888001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13255812622988488905258667 19883718934482733357888001)
          ·
            refine ⟨14912789200862050018416001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19883718934482733357888001 14912789200862050018416001)
            ·
              refine ⟨11184591900646537513812001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14912789200862050018416001 11184591900646537513812001)
              ·
                refine ⟨8388443925484903135359001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11184591900646537513812001 8388443925484903135359001)
                ·
                  refine ⟨6291332944113677351519251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8388443925484903135359001 6291332944113677351519251)
                  ·
                    refine ⟨9436999416170516027278877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6291332944113677351519251 9436999416170516027278877)
                    ·
                      refine ⟨3538874781063943510229579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9436999416170516027278877 3538874781063943510229579)
                      ·
                        rfl

theorem cell23_6891934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_6891934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891934 prefixEnd_6891934 := by exact prefixLift 6891934
  have htrace : WordTrace (prefixWord ++ tailWord_6891934) baseStart_6891934 baseEnd_6891934 := by
    simpa [prefixWord, tailWord_6891934, baseEnd_6891934] using wordTrace_append hprefix tailTrace_6891934
  have hstable : (prefixWord ++ tailWord_6891934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891934).length < 2 ^ (prefixWord ++ tailWord_6891934).sum := by decide
  have hdescent : baseEnd_6891934 < baseStart_6891934 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891940 : List Nat := [2, 3, 1, 2, 1, 1, 2, 3, 4, 2, 2]
def baseStart_6891940 : Nat := 118140960795 + 6891940 * 2 ^ 59
def prefixEnd_6891940 : Nat := 4983230072969 + 3 ^ 40 * 6891940 * 2
def baseEnd_6891940 : Nat := 3538877861947870486754551

theorem tailTrace_6891940 : CollatzResearch.WordTrace tailWord_6891940 prefixEnd_6891940 3538877861947870486754551 := by
  unfold tailWord_6891940
  simp only [CollatzResearch.WordTrace]
  refine ⟨125684851325842952243700637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167579801767790602991600849 125684851325842952243700637)
  ·
    refine ⟨47131819247191107091387739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125684851325842952243700637 47131819247191107091387739)
    ·
      refine ⟨70697728870786660637081609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47131819247191107091387739 70697728870786660637081609)
      ·
        refine ⟨53023296653089995477811207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70697728870786660637081609 53023296653089995477811207)
        ·
          refine ⟨79534944979634993216716811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53023296653089995477811207 79534944979634993216716811)
          ·
            refine ⟨119302417469452489825075217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79534944979634993216716811 119302417469452489825075217)
            ·
              refine ⟨89476813102089367368806413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119302417469452489825075217 89476813102089367368806413)
              ·
                refine ⟨33553804913283512763302405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89476813102089367368806413 33553804913283512763302405)
                ·
                  refine ⟨6291338421240658643119201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33553804913283512763302405 6291338421240658643119201)
                  ·
                    refine ⟨4718503815930493982339401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6291338421240658643119201 4718503815930493982339401)
                    ·
                      refine ⟨3538877861947870486754551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4718503815930493982339401 3538877861947870486754551)
                      ·
                        rfl

theorem cell23_6891940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 4, 2, 2].length) (baseStart_6891940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891940 prefixEnd_6891940 := by exact prefixLift 6891940
  have htrace : WordTrace (prefixWord ++ tailWord_6891940) baseStart_6891940 baseEnd_6891940 := by
    simpa [prefixWord, tailWord_6891940, baseEnd_6891940] using wordTrace_append hprefix tailTrace_6891940
  have hstable : (prefixWord ++ tailWord_6891940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891940).length < 2 ^ (prefixWord ++ tailWord_6891940).sum := by decide
  have hdescent : baseEnd_6891940 < baseStart_6891940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891943 : List Nat := [1, 1, 6, 1, 1, 2, 1, 1, 2, 4, 3]
def baseStart_6891943 : Nat := 118140960795 + 6891943 * 2 ^ 59
def prefixEnd_6891943 : Nat := 4983230072969 + 3 ^ 40 * 6891943 * 2
def baseEnd_6891943 : Nat := 3538879402389833975017037

theorem tailTrace_6891943 : CollatzResearch.WordTrace tailWord_6891943 prefixEnd_6891943 3538879402389833975017037 := by
  unfold tailWord_6891943
  simp only [CollatzResearch.WordTrace]
  refine ⟨251369812070675035999760483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167579874713783357333173655 251369812070675035999760483)
  ·
    refine ⟨377054718106012553999640725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251369812070675035999760483 377054718106012553999640725)
    ·
      refine ⟨17674439911219338468733159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 377054718106012553999640725 17674439911219338468733159)
      ·
        refine ⟨26511659866829007703099739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17674439911219338468733159 26511659866829007703099739)
        ·
          refine ⟨39767489800243511554649609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26511659866829007703099739 39767489800243511554649609)
          ·
            refine ⟨29825617350182633665987207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39767489800243511554649609 29825617350182633665987207)
            ·
              refine ⟨44738426025273950498980811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29825617350182633665987207 44738426025273950498980811)
              ·
                refine ⟨67107639037910925748471217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44738426025273950498980811 67107639037910925748471217)
                ·
                  refine ⟨50330729278433194311353413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67107639037910925748471217 50330729278433194311353413)
                  ·
                    refine ⟨9437011739706223933378765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50330729278433194311353413 9437011739706223933378765)
                    ·
                      refine ⟨3538879402389833975017037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9437011739706223933378765 3538879402389833975017037)
                      ·
                        rfl

theorem cell23_6891943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_6891943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891943 prefixEnd_6891943 := by exact prefixLift 6891943
  have htrace : WordTrace (prefixWord ++ tailWord_6891943) baseStart_6891943 baseEnd_6891943 := by
    simpa [prefixWord, tailWord_6891943, baseEnd_6891943] using wordTrace_append hprefix tailTrace_6891943
  have hstable : (prefixWord ++ tailWord_6891943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891943).length < 2 ^ (prefixWord ++ tailWord_6891943).sum := by decide
  have hdescent : baseEnd_6891943 < baseStart_6891943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891953 : List Nat := [1, 2, 2, 4, 1, 3, 1, 1, 2, 2, 4]
def baseStart_6891953 : Nat := 118140960795 + 6891953 * 2 ^ 59
def prefixEnd_6891953 : Nat := 4983230072969 + 3 ^ 40 * 6891953 * 2
def baseEnd_6891953 : Nat := 3538884537196378935891991

theorem tailTrace_6891953 : CollatzResearch.WordTrace tailWord_6891953 prefixEnd_6891953 3538884537196378935891991 := by
  unfold tailWord_6891953
  simp only [CollatzResearch.WordTrace]
  refine ⟨251370176800638807707624513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167580117867092538471749675 251370176800638807707624513)
  ·
    refine ⟨188527632600479105780718385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251370176800638807707624513 188527632600479105780718385)
    ·
      refine ⟨141395724450359329335538789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188527632600479105780718385 141395724450359329335538789)
      ·
        refine ⟨26511698334442374250413523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141395724450359329335538789 26511698334442374250413523)
        ·
          refine ⟨39767547501663561375620285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26511698334442374250413523 39767547501663561375620285)
          ·
            refine ⟨14912830313123835515857607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39767547501663561375620285 14912830313123835515857607)
            ·
              refine ⟨22369245469685753273786411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14912830313123835515857607 22369245469685753273786411)
              ·
                refine ⟨33553868204528629910679617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22369245469685753273786411 33553868204528629910679617)
                ·
                  refine ⟨25165401153396472433009713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33553868204528629910679617 25165401153396472433009713)
                  ·
                    refine ⟨18874050865047354324757285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25165401153396472433009713 18874050865047354324757285)
                    ·
                      refine ⟨3538884537196378935891991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18874050865047354324757285 3538884537196378935891991)
                      ·
                        rfl

theorem cell23_6891953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_6891953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891953 prefixEnd_6891953 := by exact prefixLift 6891953
  have htrace : WordTrace (prefixWord ++ tailWord_6891953) baseStart_6891953 baseEnd_6891953 := by
    simpa [prefixWord, tailWord_6891953, baseEnd_6891953] using wordTrace_append hprefix tailTrace_6891953
  have hstable : (prefixWord ++ tailWord_6891953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891953).length < 2 ^ (prefixWord ++ tailWord_6891953).sum := by decide
  have hdescent : baseEnd_6891953 < baseStart_6891953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891957 : List Nat := [1, 3, 3, 2, 3, 1, 2, 1, 1, 4, 2]
def baseStart_6891957 : Nat := 118140960795 + 6891957 * 2 ^ 59
def prefixEnd_6891957 : Nat := 4983230072969 + 3 ^ 40 * 6891957 * 2
def baseEnd_6891957 : Nat := 3538886591118996920241973

theorem tailTrace_6891957 : CollatzResearch.WordTrace tailWord_6891957 prefixEnd_6891957 3538886591118996920241973 := by
  unfold tailWord_6891957
  simp only [CollatzResearch.WordTrace]
  refine ⟨251370322692624316390770125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167580215128416210927180083 251370322692624316390770125)
  ·
    refine ⟨94263871009734118646538797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251370322692624316390770125 94263871009734118646538797)
    ·
      refine ⟨35348951628650294492452049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94263871009734118646538797 35348951628650294492452049)
      ·
        refine ⟨26511713721487720869339037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35348951628650294492452049 26511713721487720869339037)
        ·
          refine ⟨9941892645557895326002139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26511713721487720869339037 9941892645557895326002139)
          ·
            refine ⟨14912838968336842989003209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9941892645557895326002139 14912838968336842989003209)
            ·
              refine ⟨11184629226252632241752407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14912838968336842989003209 11184629226252632241752407)
              ·
                refine ⟨16776943839378948362628611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11184629226252632241752407 16776943839378948362628611)
                ·
                  refine ⟨25165415759068422543942917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16776943839378948362628611 25165415759068422543942917)
                  ·
                    refine ⟨4718515454825329226989297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25165415759068422543942917 4718515454825329226989297)
                    ·
                      refine ⟨3538886591118996920241973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4718515454825329226989297 3538886591118996920241973)
                      ·
                        rfl

theorem cell23_6891957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_6891957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891957 prefixEnd_6891957 := by exact prefixLift 6891957
  have htrace : WordTrace (prefixWord ++ tailWord_6891957) baseStart_6891957 baseEnd_6891957 := by
    simpa [prefixWord, tailWord_6891957, baseEnd_6891957] using wordTrace_append hprefix tailTrace_6891957
  have hstable : (prefixWord ++ tailWord_6891957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891957).length < 2 ^ (prefixWord ++ tailWord_6891957).sum := by decide
  have hdescent : baseEnd_6891957 < baseStart_6891957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6891990 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3]
def baseStart_6891990 : Nat := 118140960795 + 6891990 * 2 ^ 59
def prefixEnd_6891990 : Nat := 4983230072969 + 3 ^ 40 * 6891990 * 2
def baseEnd_6891990 : Nat := 3538903535980595291129321

theorem tailTrace_6891990 : CollatzResearch.WordTrace tailWord_6891990 prefixEnd_6891990 3538903535980595291129321 := by
  unfold tailWord_6891990
  simp only [CollatzResearch.WordTrace]
  refine ⟨15710720393844047689170089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167581017534336508684480949 15710720393844047689170089)
  ·
    refine ⟨11783040295383035766877567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15710720393844047689170089 11783040295383035766877567)
    ·
      refine ⟨17674560443074553650316351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11783040295383035766877567 17674560443074553650316351)
      ·
        refine ⟨26511840664611830475474527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17674560443074553650316351 26511840664611830475474527)
        ·
          refine ⟨39767760996917745713211791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26511840664611830475474527 39767760996917745713211791)
          ·
            refine ⟨59651641495376618569817687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39767760996917745713211791 59651641495376618569817687)
            ·
              refine ⟨89477462243064927854726531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59651641495376618569817687 89477462243064927854726531)
              ·
                refine ⟨134216193364597391782089797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89477462243064927854726531 134216193364597391782089797)
                ·
                  refine ⟨25165536255862010959141837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134216193364597391782089797 25165536255862010959141837)
                  ·
                    refine ⟨9437076095948254109678189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25165536255862010959141837 9437076095948254109678189)
                    ·
                      refine ⟨3538903535980595291129321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9437076095948254109678189 3538903535980595291129321)
                      ·
                        rfl

theorem cell23_6891990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_6891990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6891990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6891990 prefixEnd_6891990 := by exact prefixLift 6891990
  have htrace : WordTrace (prefixWord ++ tailWord_6891990) baseStart_6891990 baseEnd_6891990 := by
    simpa [prefixWord, tailWord_6891990, baseEnd_6891990] using wordTrace_append hprefix tailTrace_6891990
  have hstable : (prefixWord ++ tailWord_6891990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6891990).length < 2 ^ (prefixWord ++ tailWord_6891990).sum := by decide
  have hdescent : baseEnd_6891990 < baseStart_6891990 := by decide
  rcases family_descends (prefixWord ++ tailWord_6891990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892026 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 1, 3, 6]
def baseStart_6892026 : Nat := 118140960795 + 6892026 * 2 ^ 59
def prefixEnd_6892026 : Nat := 4983230072969 + 3 ^ 40 * 6892026 * 2
def baseEnd_6892026 : Nat := 3538922021284157150279155

theorem tailTrace_6892026 : CollatzResearch.WordTrace tailWord_6892026 prefixEnd_6892026 3538922021284157150279155 := by
  unfold tailWord_6892026
  simp only [CollatzResearch.WordTrace]
  refine ⟨62843209832343585293757983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167581892886249560783354621 62843209832343585293757983)
  ·
    refine ⟨94264814748515377940636975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62843209832343585293757983 94264814748515377940636975)
    ·
      refine ⟨141397222122773066910955463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94264814748515377940636975 141397222122773066910955463)
      ·
        refine ⟨212095833184159600366433195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141397222122773066910955463 212095833184159600366433195)
        ·
          refine ⟨318143749776239400549649793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212095833184159600366433195 318143749776239400549649793)
          ·
            refine ⟨238607812332179550412237345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318143749776239400549649793 238607812332179550412237345)
            ·
              refine ⟨178955859249134662809178009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238607812332179550412237345 178955859249134662809178009)
              ·
                refine ⟨134216894436850997106883507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178955859249134662809178009 134216894436850997106883507)
                ·
                  refine ⟨201325341655276495660325261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134216894436850997106883507 201325341655276495660325261)
                  ·
                    refine ⟨75497003120728685872621973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 201325341655276495660325261 75497003120728685872621973)
                    ·
                      refine ⟨3538922021284157150279155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75497003120728685872621973 3538922021284157150279155)
                      ·
                        rfl

theorem cell23_6892026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_6892026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892026 prefixEnd_6892026 := by exact prefixLift 6892026
  have htrace : WordTrace (prefixWord ++ tailWord_6892026) baseStart_6892026 baseEnd_6892026 := by
    simpa [prefixWord, tailWord_6892026, baseEnd_6892026] using wordTrace_append hprefix tailTrace_6892026
  have hstable : (prefixWord ++ tailWord_6892026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892026).length < 2 ^ (prefixWord ++ tailWord_6892026).sum := by decide
  have hdescent : baseEnd_6892026 < baseStart_6892026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892053 : List Nat := [1, 3, 2, 1, 3, 1, 2, 4, 6]
def baseStart_6892053 : Nat := 118140960795 + 6892053 * 2 ^ 59
def prefixEnd_6892053 : Nat := 4983230072969 + 3 ^ 40 * 6892053 * 2
def baseEnd_6892053 : Nat := 393215098362425393849059

theorem tailTrace_6892053 : CollatzResearch.WordTrace tailWord_6892053 prefixEnd_6892053 393215098362425393849059 := by
  unfold tailWord_6892053
  simp only [CollatzResearch.WordTrace]
  refine ⟨251373824100276524786264813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167582549400184349857509875 251373824100276524786264813)
  ·
    refine ⟨94265184037603696794849305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251373824100276524786264813 94265184037603696794849305)
    ·
      refine ⟨70698888028202772596136979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94265184037603696794849305 70698888028202772596136979)
      ·
        refine ⟨106048332042304158894205469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70698888028202772596136979 106048332042304158894205469)
        ·
          refine ⟨39768124515864059585327051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106048332042304158894205469 39768124515864059585327051)
          ·
            refine ⟨59652186773796089377990577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39768124515864059585327051 59652186773796089377990577)
            ·
              refine ⟨44739140080347067033492933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59652186773796089377990577 44739140080347067033492933)
              ·
                refine ⟨8388588765065075068779925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44739140080347067033492933 8388588765065075068779925)
                ·
                  refine ⟨393215098362425393849059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8388588765065075068779925 393215098362425393849059)
                  ·
                    rfl

theorem cell23_6892053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4, 6].length) (baseStart_6892053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892053 prefixEnd_6892053 := by exact prefixLift 6892053
  have htrace : WordTrace (prefixWord ++ tailWord_6892053) baseStart_6892053 baseEnd_6892053 := by
    simpa [prefixWord, tailWord_6892053, baseEnd_6892053] using wordTrace_append hprefix tailTrace_6892053
  have hstable : (prefixWord ++ tailWord_6892053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892053).length < 2 ^ (prefixWord ++ tailWord_6892053).sum := by decide
  have hdescent : baseEnd_6892053 < baseStart_6892053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892080 : List Nat := [2, 1, 1, 1, 2, 3, 2, 4, 3, 1, 3]
def baseStart_6892080 : Nat := 118140960795 + 6892080 * 2 ^ 59
def prefixEnd_6892080 : Nat := 4983230072969 + 3 ^ 40 * 6892080 * 2
def baseEnd_6892080 : Nat := 3538949749239499939003907

theorem tailTrace_6892080 : CollatzResearch.WordTrace tailWord_6892080 prefixEnd_6892080 3538949749239499939003907 := by
  unfold tailWord_6892080
  simp only [CollatzResearch.WordTrace]
  refine ⟨125687404435589354198748847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167583205914119138931665129 125687404435589354198748847)
  ·
    refine ⟨188531106653384031298123271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125687404435589354198748847 188531106653384031298123271)
    ·
      refine ⟨282796659980076046947184907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188531106653384031298123271 282796659980076046947184907)
      ·
        refine ⟨424194989970114070420777361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282796659980076046947184907 424194989970114070420777361)
        ·
          refine ⟨318146242477585552815583021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 424194989970114070420777361 318146242477585552815583021)
          ·
            refine ⟨119304840929094582305843633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 318146242477585552815583021 119304840929094582305843633)
            ·
              refine ⟨89478630696820936729382725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119304840929094582305843633 89478630696820936729382725)
              ·
                refine ⟨16777243255653925636759261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89478630696820936729382725 16777243255653925636759261)
                ·
                  refine ⟨6291466220870222113784723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16777243255653925636759261 6291466220870222113784723)
                  ·
                    refine ⟨9437199331305333170677085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6291466220870222113784723 9437199331305333170677085)
                    ·
                      refine ⟨3538949749239499939003907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9437199331305333170677085 3538949749239499939003907)
                      ·
                        rfl

theorem cell23_6892080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 3, 1, 3].length) (baseStart_6892080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892080 prefixEnd_6892080 := by exact prefixLift 6892080
  have htrace : WordTrace (prefixWord ++ tailWord_6892080) baseStart_6892080 baseEnd_6892080 := by
    simpa [prefixWord, tailWord_6892080, baseEnd_6892080] using wordTrace_append hprefix tailTrace_6892080
  have hstable : (prefixWord ++ tailWord_6892080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892080).length < 2 ^ (prefixWord ++ tailWord_6892080).sum := by decide
  have hdescent : baseEnd_6892080 < baseStart_6892080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892083 : List Nat := [1, 1, 1, 2, 4, 2, 3, 1, 3, 5]
def baseStart_6892083 : Nat := 118140960795 + 6892083 * 2 ^ 59
def prefixEnd_6892083 : Nat := 4983230072969 + 3 ^ 40 * 6892083 * 2
def baseEnd_6892083 : Nat := 1179650429893821142422131

theorem tailTrace_6892083 : CollatzResearch.WordTrace tailWord_6892083 prefixEnd_6892083 1179650429893821142422131 := by
  unfold tailWord_6892083
  simp only [CollatzResearch.WordTrace]
  refine ⟨251374918290167839909856903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167583278860111893273237935 251374918290167839909856903)
  ·
    refine ⟨377062377435251759864785355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251374918290167839909856903 377062377435251759864785355)
    ·
      refine ⟨565593566152877639797178033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377062377435251759864785355 565593566152877639797178033)
      ·
        refine ⟨424195174614658229847883525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 565593566152877639797178033 424195174614658229847883525)
        ·
          refine ⟨79536595240248418096478161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 424195174614658229847883525 79536595240248418096478161)
          ·
            refine ⟨59652446430186313572358621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79536595240248418096478161 59652446430186313572358621)
            ·
              refine ⟨22369667411319867589634483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59652446430186313572358621 22369667411319867589634483)
              ·
                refine ⟨33554501116979801384451725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22369667411319867589634483 33554501116979801384451725)
                ·
                  refine ⟨12582937918867425519169397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33554501116979801384451725 12582937918867425519169397)
                  ·
                    refine ⟨1179650429893821142422131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12582937918867425519169397 1179650429893821142422131)
                    ·
                      rfl

theorem cell23_6892083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3, 5].length) (baseStart_6892083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892083 prefixEnd_6892083 := by exact prefixLift 6892083
  have htrace : WordTrace (prefixWord ++ tailWord_6892083) baseStart_6892083 baseEnd_6892083 := by
    simpa [prefixWord, tailWord_6892083, baseEnd_6892083] using wordTrace_append hprefix tailTrace_6892083
  have hstable : (prefixWord ++ tailWord_6892083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892083).length < 2 ^ (prefixWord ++ tailWord_6892083).sum := by decide
  have hdescent : baseEnd_6892083 < baseStart_6892083 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892114 : List Nat := [3, 2, 2, 1, 2, 1, 3, 4, 1, 1, 3]
def baseStart_6892114 : Nat := 118140960795 + 6892114 * 2 ^ 59
def prefixEnd_6892114 : Nat := 4983230072969 + 3 ^ 40 * 6892114 * 2
def baseEnd_6892114 : Nat := 3538967207581752805978751

theorem tailTrace_6892114 : CollatzResearch.WordTrace tailWord_6892114 prefixEnd_6892114 3538967207581752805978751 := by
  unfold tailWord_6892114
  simp only [CollatzResearch.WordTrace]
  refine ⟨62844012238263883051058849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167584032635370354802823597 62844012238263883051058849)
  ·
    refine ⟨47133009178697912288294137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62844012238263883051058849 47133009178697912288294137)
    ·
      refine ⟨35349756884023434216220603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47133009178697912288294137 35349756884023434216220603)
      ·
        refine ⟨53024635326035151324330905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35349756884023434216220603 53024635326035151324330905)
        ·
          refine ⟨39768476494526363493248179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53024635326035151324330905 39768476494526363493248179)
          ·
            refine ⟨59652714741789545239872269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39768476494526363493248179 59652714741789545239872269)
            ·
              refine ⟨22369768028171079464952101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59652714741789545239872269 22369768028171079464952101)
              ·
                refine ⟨4194331505282077399678519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22369768028171079464952101 4194331505282077399678519)
                ·
                  refine ⟨6291497257923116099517779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4194331505282077399678519 6291497257923116099517779)
                  ·
                    refine ⟨9437245886884674149276669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6291497257923116099517779 9437245886884674149276669)
                    ·
                      refine ⟨3538967207581752805978751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9437245886884674149276669 3538967207581752805978751)
                      ·
                        rfl

theorem cell23_6892114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 4, 1, 1, 3].length) (baseStart_6892114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892114 prefixEnd_6892114 := by exact prefixLift 6892114
  have htrace : WordTrace (prefixWord ++ tailWord_6892114) baseStart_6892114 baseEnd_6892114 := by
    simpa [prefixWord, tailWord_6892114, baseEnd_6892114] using wordTrace_append hprefix tailTrace_6892114
  have hstable : (prefixWord ++ tailWord_6892114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892114).length < 2 ^ (prefixWord ++ tailWord_6892114).sum := by decide
  have hdescent : baseEnd_6892114 < baseStart_6892114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892140 : List Nat := [2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 3]
def baseStart_6892140 : Nat := 118140960795 + 6892140 * 2 ^ 59
def prefixEnd_6892140 : Nat := 4983230072969 + 3 ^ 40 * 6892140 * 2
def baseEnd_6892140 : Nat := 3538980558078769704253631

theorem tailTrace_6892140 : CollatzResearch.WordTrace tailWord_6892140 prefixEnd_6892140 3538980558078769704253631 := by
  unfold tailWord_6892140
  simp only [CollatzResearch.WordTrace]
  refine ⟨125688498625480669322340937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167584664833974225763121249 125688498625480669322340937)
  ·
    refine ⟨94266373969110501991755703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125688498625480669322340937 94266373969110501991755703)
    ·
      refine ⟨141399560953665752987633555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94266373969110501991755703 141399560953665752987633555)
      ·
        refine ⟨212099341430498629481450333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141399560953665752987633555 212099341430498629481450333)
        ·
          refine ⟨79537253036436986055543875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212099341430498629481450333 79537253036436986055543875)
          ·
            refine ⟨119305879554655479083315813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79537253036436986055543875 119305879554655479083315813)
            ·
              refine ⟨22369852416497902328121715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119305879554655479083315813 22369852416497902328121715)
              ·
                refine ⟨33554778624746853492182573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22369852416497902328121715 33554778624746853492182573)
                ·
                  refine ⟨12583041984280070059568465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33554778624746853492182573 12583041984280070059568465)
                  ·
                    refine ⟨9437281488210052544676349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12583041984280070059568465 9437281488210052544676349)
                    ·
                      refine ⟨3538980558078769704253631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9437281488210052544676349 3538980558078769704253631)
                      ·
                        rfl

theorem cell23_6892140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 3].length) (baseStart_6892140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892140 prefixEnd_6892140 := by exact prefixLift 6892140
  have htrace : WordTrace (prefixWord ++ tailWord_6892140) baseStart_6892140 baseEnd_6892140 := by
    simpa [prefixWord, tailWord_6892140, baseEnd_6892140] using wordTrace_append hprefix tailTrace_6892140
  have hstable : (prefixWord ++ tailWord_6892140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892140).length < 2 ^ (prefixWord ++ tailWord_6892140).sum := by decide
  have hdescent : baseEnd_6892140 < baseStart_6892140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892164 : List Nat := [2, 3, 2, 1, 3, 3, 1, 2, 2, 4]
def baseStart_6892164 : Nat := 118140960795 + 6892164 * 2 ^ 59
def prefixEnd_6892164 : Nat := 4983230072969 + 3 ^ 40 * 6892164 * 2
def baseEnd_6892164 : Nat := 1179664293871492536784507

theorem tailTrace_6892164 : CollatzResearch.WordTrace tailWord_6892164 prefixEnd_6892164 1179664293871492536784507 := by
  unfold tailWord_6892164
  simp only [CollatzResearch.WordTrace]
  refine ⟨125688936301437195371777773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167585248401916260495703697 125688936301437195371777773)
  ·
    refine ⟨47133351113038948264416665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125688936301437195371777773 47133351113038948264416665)
    ·
      refine ⟨35350013334779211198312499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47133351113038948264416665 35350013334779211198312499)
      ·
        refine ⟨53025020002168816797468749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35350013334779211198312499 53025020002168816797468749)
        ·
          refine ⟨19884382500813306299050781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53025020002168816797468749 19884382500813306299050781)
          ·
            refine ⟨7456643437804989862144043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19884382500813306299050781 7456643437804989862144043)
            ·
              refine ⟨11184965156707484793216065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7456643437804989862144043 11184965156707484793216065)
              ·
                refine ⟨8388723867530613594912049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11184965156707484793216065 8388723867530613594912049)
                ·
                  refine ⟨6291542900647960196184037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8388723867530613594912049 6291542900647960196184037)
                  ·
                    refine ⟨1179664293871492536784507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6291542900647960196184037 1179664293871492536784507)
                    ·
                      rfl

theorem cell23_6892164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_6892164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892164 prefixEnd_6892164 := by exact prefixLift 6892164
  have htrace : WordTrace (prefixWord ++ tailWord_6892164) baseStart_6892164 baseEnd_6892164 := by
    simpa [prefixWord, tailWord_6892164, baseEnd_6892164] using wordTrace_append hprefix tailTrace_6892164
  have hstable : (prefixWord ++ tailWord_6892164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892164).length < 2 ^ (prefixWord ++ tailWord_6892164).sum := by decide
  have hdescent : baseEnd_6892164 < baseStart_6892164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892280 : List Nat := [2, 1, 2, 1, 1, 2, 3, 4, 2, 5]
def baseStart_6892280 : Nat := 118140960795 + 6892280 * 2 ^ 59
def prefixEnd_6892280 : Nat := 4983230072969 + 3 ^ 40 * 6892280 * 2
def baseEnd_6892280 : Nat := 1179684148456799718834329

theorem tailTrace_6892280 : CollatzResearch.WordTrace tailWord_6892280 prefixEnd_6892280 1179684148456799718834329 := by
  unfold tailWord_6892280
  simp only [CollatzResearch.WordTrace]
  refine ⟨125691051735227071277389147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167588068980302761703185529 125691051735227071277389147)
  ·
    refine ⟨188536577602840606916083721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125691051735227071277389147 188536577602840606916083721)
    ·
      refine ⟨141402433202130455187062791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188536577602840606916083721 141402433202130455187062791)
      ·
        refine ⟨212103649803195682780594187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141402433202130455187062791 212103649803195682780594187)
        ·
          refine ⟨318155474704793524170891281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212103649803195682780594187 318155474704793524170891281)
          ·
            refine ⟨238616606028595143128168461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318155474704793524170891281 238616606028595143128168461)
            ·
              refine ⟨89481227260723178673063173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 238616606028595143128168461 89481227260723178673063173)
              ·
                refine ⟨16777730111385596001199345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89481227260723178673063173 16777730111385596001199345)
                ·
                  refine ⟨12583297583539197000899509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16777730111385596001199345 12583297583539197000899509)
                  ·
                    refine ⟨1179684148456799718834329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12583297583539197000899509 1179684148456799718834329)
                    ·
                      rfl

theorem cell23_6892280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 2, 5].length) (baseStart_6892280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892280 prefixEnd_6892280 := by exact prefixLift 6892280
  have htrace : WordTrace (prefixWord ++ tailWord_6892280) baseStart_6892280 baseEnd_6892280 := by
    simpa [prefixWord, tailWord_6892280, baseEnd_6892280] using wordTrace_append hprefix tailTrace_6892280
  have hstable : (prefixWord ++ tailWord_6892280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892280).length < 2 ^ (prefixWord ++ tailWord_6892280).sum := by decide
  have hdescent : baseEnd_6892280 < baseStart_6892280 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892284 : List Nat := [2, 2, 2, 1, 3, 2, 4, 2, 5]
def baseStart_6892284 : Nat := 118140960795 + 6892284 * 2 ^ 59
def prefixEnd_6892284 : Nat := 4983230072969 + 3 ^ 40 * 6892284 * 2
def baseEnd_6892284 : Nat := 393228277699224126761441

theorem tailTrace_6892284 : CollatzResearch.WordTrace tailWord_6892284 prefixEnd_6892284 393228277699224126761441 := by
  unfold tailWord_6892284
  simp only [CollatzResearch.WordTrace]
  refine ⟨125691124681219825618961953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167588166241626434158615937 125691124681219825618961953)
  ·
    refine ⟨94268343510914869214221465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125691124681219825618961953 94268343510914869214221465)
    ·
      refine ⟨70701257633186151910666099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94268343510914869214221465 70701257633186151910666099)
      ·
        refine ⟨106051886449779227865999149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70701257633186151910666099 106051886449779227865999149)
        ·
          refine ⟨39769457418667210449749681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106051886449779227865999149 39769457418667210449749681)
          ·
            refine ⟨29827093064000407837312261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39769457418667210449749681 29827093064000407837312261)
            ·
              refine ⟨5592579949500076469496049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29827093064000407837312261 5592579949500076469496049)
              ·
                refine ⟨4194434962125057352122037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5592579949500076469496049 4194434962125057352122037)
                ·
                  refine ⟨393228277699224126761441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4194434962125057352122037 393228277699224126761441)
                  ·
                    rfl

theorem cell23_6892284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 2, 5].length) (baseStart_6892284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892284 prefixEnd_6892284 := by exact prefixLift 6892284
  have htrace : WordTrace (prefixWord ++ tailWord_6892284) baseStart_6892284 baseEnd_6892284 := by
    simpa [prefixWord, tailWord_6892284, baseEnd_6892284] using wordTrace_append hprefix tailTrace_6892284
  have hstable : (prefixWord ++ tailWord_6892284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892284).length < 2 ^ (prefixWord ++ tailWord_6892284).sum := by decide
  have hdescent : baseEnd_6892284 < baseStart_6892284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892300 : List Nat := [2, 2, 1, 2, 2, 1, 1, 4, 1, 3, 4]
def baseStart_6892300 : Nat := 118140960795 + 6892300 * 2 ^ 59
def prefixEnd_6892300 : Nat := 4983230072969 + 3 ^ 40 * 6892300 * 2
def baseEnd_6892300 : Nat := 3539062714983489078252895

theorem tailTrace_6892300 : CollatzResearch.WordTrace tailWord_6892300 prefixEnd_6892300 3539062714983489078252895 := by
  unfold tailWord_6892300
  simp only [CollatzResearch.WordTrace]
  refine ⟨125691416465190842985253177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167588555286921123980337569 125691416465190842985253177)
  ·
    refine ⟨94268562348893132238939883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125691416465190842985253177 94268562348893132238939883)
    ·
      refine ⟨141402843523339698358409825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94268562348893132238939883 141402843523339698358409825)
      ·
        refine ⟨106052132642504773768807369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141402843523339698358409825 106052132642504773768807369)
        ·
          refine ⟨79539099481878580326605527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106052132642504773768807369 79539099481878580326605527)
          ·
            refine ⟨119308649222817870489908291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79539099481878580326605527 119308649222817870489908291)
            ·
              refine ⟨178962973834226805734862437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119308649222817870489908291 178962973834226805734862437)
              ·
                refine ⟨33555557593917526075286707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 178962973834226805734862437 33555557593917526075286707)
                ·
                  refine ⟨50333336390876289112930061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33555557593917526075286707 50333336390876289112930061)
                  ·
                    refine ⟨18875001146578608417348773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50333336390876289112930061 18875001146578608417348773)
                    ·
                      refine ⟨3539062714983489078252895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18875001146578608417348773 3539062714983489078252895)
                      ·
                        rfl

theorem cell23_6892300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_6892300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892300 prefixEnd_6892300 := by exact prefixLift 6892300
  have htrace : WordTrace (prefixWord ++ tailWord_6892300) baseStart_6892300 baseEnd_6892300 := by
    simpa [prefixWord, tailWord_6892300, baseEnd_6892300] using wordTrace_append hprefix tailTrace_6892300
  have hstable : (prefixWord ++ tailWord_6892300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892300).length < 2 ^ (prefixWord ++ tailWord_6892300).sum := by decide
  have hdescent : baseEnd_6892300 < baseStart_6892300 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892337 : List Nat := [1, 2, 2, 3, 2, 1, 2, 1, 4, 2, 3]
def baseStart_6892337 : Nat := 118140960795 + 6892337 * 2 ^ 59
def prefixEnd_6892337 : Nat := 4983230072969 + 3 ^ 40 * 6892337 * 2
def baseEnd_6892337 : Nat := 3539081713767705433490225

theorem tailTrace_6892337 : CollatzResearch.WordTrace tailWord_6892337 prefixEnd_6892337 3539081713767705433490225 := by
  unfold tailWord_6892337
  simp only [CollatzResearch.WordTrace]
  refine ⟨251384182431247641289603265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167589454954165094193068843 251384182431247641289603265)
  ·
    refine ⟨188538136823435730967202449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251384182431247641289603265 188538136823435730967202449)
    ·
      refine ⟨141403602617576798225401837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188538136823435730967202449 141403602617576798225401837)
      ·
        refine ⟨53026350981591299334525689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141403602617576798225401837 53026350981591299334525689)
        ·
          refine ⟨39769763236193474500894267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53026350981591299334525689 39769763236193474500894267)
          ·
            refine ⟨59654644854290211751341401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39769763236193474500894267 59654644854290211751341401)
            ·
              refine ⟨44740983640717658813506051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59654644854290211751341401 44740983640717658813506051)
              ·
                refine ⟨67111475461076488220259077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44740983640717658813506051 67111475461076488220259077)
                ·
                  refine ⟨12583401648951841541298577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67111475461076488220259077 12583401648951841541298577)
                  ·
                    refine ⟨9437551236713881155973933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12583401648951841541298577 9437551236713881155973933)
                    ·
                      refine ⟨3539081713767705433490225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9437551236713881155973933 3539081713767705433490225)
                      ·
                        rfl

theorem cell23_6892337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_6892337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892337 prefixEnd_6892337 := by exact prefixLift 6892337
  have htrace : WordTrace (prefixWord ++ tailWord_6892337) baseStart_6892337 baseEnd_6892337 := by
    simpa [prefixWord, tailWord_6892337, baseEnd_6892337] using wordTrace_append hprefix tailTrace_6892337
  have hstable : (prefixWord ++ tailWord_6892337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892337).length < 2 ^ (prefixWord ++ tailWord_6892337).sum := by decide
  have hdescent : baseEnd_6892337 < baseStart_6892337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892344 : List Nat := [2, 1, 2, 1, 3, 2, 1, 6, 1, 4]
def baseStart_6892344 : Nat := 118140960795 + 6892344 * 2 ^ 59
def prefixEnd_6892344 : Nat := 4983230072969 + 3 ^ 40 * 6892344 * 2
def baseEnd_6892344 : Nat := 1179695102710762302034231

theorem tailTrace_6892344 : CollatzResearch.WordTrace tailWord_6892344 prefixEnd_6892344 1179695102710762302034231 := by
  unfold tailWord_6892344
  simp only [CollatzResearch.WordTrace]
  refine ⟨125692218871111140742554043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167589625161481520990072057 125692218871111140742554043)
  ·
    refine ⟨188538328306666711113831065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125692218871111140742554043 188538328306666711113831065)
    ·
      refine ⟨141403746230000033335373299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188538328306666711113831065 141403746230000033335373299)
      ·
        refine ⟨212105619345000050003059949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141403746230000033335373299 212105619345000050003059949)
        ·
          refine ⟨79539607254375018751147481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212105619345000050003059949 79539607254375018751147481)
          ·
            refine ⟨59654705440781264063360611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79539607254375018751147481 59654705440781264063360611)
            ·
              refine ⟨89482058161171896095040917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59654705440781264063360611 89482058161171896095040917)
              ·
                refine ⟨4194471476304932629455043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89482058161171896095040917 4194471476304932629455043)
                ·
                  refine ⟨6291707214457398944182565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4194471476304932629455043 6291707214457398944182565)
                  ·
                    refine ⟨1179695102710762302034231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6291707214457398944182565 1179695102710762302034231)
                    ·
                      rfl

theorem cell23_6892344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 6, 1, 4].length) (baseStart_6892344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892344 prefixEnd_6892344 := by exact prefixLift 6892344
  have htrace : WordTrace (prefixWord ++ tailWord_6892344) baseStart_6892344 baseEnd_6892344 := by
    simpa [prefixWord, tailWord_6892344, baseEnd_6892344] using wordTrace_append hprefix tailTrace_6892344
  have hstable : (prefixWord ++ tailWord_6892344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892344).length < 2 ^ (prefixWord ++ tailWord_6892344).sum := by decide
  have hdescent : baseEnd_6892344 < baseStart_6892344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892360 : List Nat := [2, 1, 3, 1, 1, 3, 1, 2, 1, 2, 6]
def baseStart_6892360 : Nat := 118140960795 + 6892360 * 2 ^ 59
def prefixEnd_6892360 : Nat := 4983230072969 + 3 ^ 40 * 6892360 * 2
def baseEnd_6892360 : Nat := 3539093523822758843502619

theorem tailTrace_6892360 : CollatzResearch.WordTrace tailWord_6892360 prefixEnd_6892360 3539093523822758843502619 := by
  unfold tailWord_6892360
  simp only [CollatzResearch.WordTrace]
  refine ⟨125692510655082158108845267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167590014206776210811793689 125692510655082158108845267)
  ·
    refine ⟨188538765982623237163267901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125692510655082158108845267 188538765982623237163267901)
    ·
      refine ⟨70702037243483713936225463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188538765982623237163267901 70702037243483713936225463)
      ·
        refine ⟨106053055865225570904338195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70702037243483713936225463 106053055865225570904338195)
        ·
          refine ⟨159079583797838356356507293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106053055865225570904338195 159079583797838356356507293)
          ·
            refine ⟨59654843924189383633690235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159079583797838356356507293 59654843924189383633690235)
            ·
              refine ⟨89482265886284075450535353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59654843924189383633690235 89482265886284075450535353)
              ·
                refine ⟨67111699414713056587901515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89482265886284075450535353 67111699414713056587901515)
                ·
                  refine ⟨100667549122069584881852273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67111699414713056587901515 100667549122069584881852273)
                  ·
                    refine ⟨75500661841552188661389205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 100667549122069584881852273 75500661841552188661389205)
                    ·
                      refine ⟨3539093523822758843502619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75500661841552188661389205 3539093523822758843502619)
                      ·
                        rfl

theorem cell23_6892360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_6892360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892360 prefixEnd_6892360 := by exact prefixLift 6892360
  have htrace : WordTrace (prefixWord ++ tailWord_6892360) baseStart_6892360 baseEnd_6892360 := by
    simpa [prefixWord, tailWord_6892360, baseEnd_6892360] using wordTrace_append hprefix tailTrace_6892360
  have hstable : (prefixWord ++ tailWord_6892360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892360).length < 2 ^ (prefixWord ++ tailWord_6892360).sum := by decide
  have hdescent : baseEnd_6892360 < baseStart_6892360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892401 : List Nat := [1, 2, 2, 2, 1, 6, 1, 1, 3, 1, 3]
def baseStart_6892401 : Nat := 118140960795 + 6892401 * 2 ^ 59
def prefixEnd_6892401 : Nat := 4983230072969 + 3 ^ 40 * 6892401 * 2
def baseEnd_6892401 : Nat := 3539114576529593183089931

theorem tailTrace_6892401 : CollatzResearch.WordTrace tailWord_6892401 prefixEnd_6892401 3539114576529593183089931 := by
  unfold tailWord_6892401
  simp only [CollatzResearch.WordTrace]
  refine ⟨251386516703015780219933057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167591011135343853479955371 251386516703015780219933057)
  ·
    refine ⟨188539887527261835164949793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251386516703015780219933057 188539887527261835164949793)
    ·
      refine ⟨141404915645446376373712345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188539887527261835164949793 141404915645446376373712345)
      ·
        refine ⟨106053686734084782280284259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141404915645446376373712345 106053686734084782280284259)
        ·
          refine ⟨159080530101127173420426389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106053686734084782280284259 159080530101127173420426389)
          ·
            refine ⟨7456899848490336254082487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 159080530101127173420426389 7456899848490336254082487)
            ·
              refine ⟨11185349772735504381123731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7456899848490336254082487 11185349772735504381123731)
              ·
                refine ⟨16778024659103256571685597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11185349772735504381123731 16778024659103256571685597)
                ·
                  refine ⟨6291759247163721214382099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16778024659103256571685597 6291759247163721214382099)
                  ·
                    refine ⟨9437638870745581821573149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6291759247163721214382099 9437638870745581821573149)
                    ·
                      refine ⟨3539114576529593183089931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9437638870745581821573149 3539114576529593183089931)
                      ·
                        rfl

theorem cell23_6892401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 3, 1, 3].length) (baseStart_6892401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892401 prefixEnd_6892401 := by exact prefixLift 6892401
  have htrace : WordTrace (prefixWord ++ tailWord_6892401) baseStart_6892401 baseEnd_6892401 := by
    simpa [prefixWord, tailWord_6892401, baseEnd_6892401] using wordTrace_append hprefix tailTrace_6892401
  have hstable : (prefixWord ++ tailWord_6892401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892401).length < 2 ^ (prefixWord ++ tailWord_6892401).sum := by decide
  have hdescent : baseEnd_6892401 < baseStart_6892401 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892424 : List Nat := [2, 1, 3, 3, 2, 2, 1, 1, 3, 1, 4]
def baseStart_6892424 : Nat := 118140960795 + 6892424 * 2 ^ 59
def prefixEnd_6892424 : Nat := 4983230072969 + 3 ^ 40 * 6892424 * 2
def baseEnd_6892424 : Nat := 3539126386584646593102325

theorem tailTrace_6892424 : CollatzResearch.WordTrace tailWord_6892424 prefixEnd_6892424 3539126386584646593102325 := by
  unfold tailWord_6892424
  simp only [CollatzResearch.WordTrace]
  refine ⟨125693677790966227574010163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167591570387954970098680217 125693677790966227574010163)
  ·
    refine ⟨188540516686449341361015245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125693677790966227574010163 188540516686449341361015245)
    ·
      refine ⟨70702693757418503010380717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188540516686449341361015245 70702693757418503010380717)
      ·
        refine ⟨26513510159031938628892769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70702693757418503010380717 26513510159031938628892769)
        ·
          refine ⟨19885132619273953971669577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26513510159031938628892769 19885132619273953971669577)
          ·
            refine ⟨14913849464455465478752183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19885132619273953971669577 14913849464455465478752183)
            ·
              refine ⟨22370774196683198218128275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14913849464455465478752183 22370774196683198218128275)
              ·
                refine ⟨33556161295024797327192413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22370774196683198218128275 33556161295024797327192413)
                ·
                  refine ⟨12583560485634298997697155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33556161295024797327192413 12583560485634298997697155)
                  ·
                    refine ⟨18875340728451448496545733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12583560485634298997697155 18875340728451448496545733)
                    ·
                      refine ⟨3539126386584646593102325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18875340728451448496545733 3539126386584646593102325)
                      ·
                        rfl

theorem cell23_6892424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_6892424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892424 prefixEnd_6892424 := by exact prefixLift 6892424
  have htrace : WordTrace (prefixWord ++ tailWord_6892424) baseStart_6892424 baseEnd_6892424 := by
    simpa [prefixWord, tailWord_6892424, baseEnd_6892424] using wordTrace_append hprefix tailTrace_6892424
  have hstable : (prefixWord ++ tailWord_6892424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892424).length < 2 ^ (prefixWord ++ tailWord_6892424).sum := by decide
  have hdescent : baseEnd_6892424 < baseStart_6892424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892437 : List Nat := [1, 3, 2, 1, 1, 4, 1, 1, 3, 2, 4]
def baseStart_6892437 : Nat := 118140960795 + 6892437 * 2 ^ 59
def prefixEnd_6892437 : Nat := 4983230072969 + 3 ^ 40 * 6892437 * 2
def baseEnd_6892437 : Nat := 3539133061833155042239765

theorem tailTrace_6892437 : CollatzResearch.WordTrace tailWord_6892437 prefixEnd_6892437 3539133061833155042239765 := by
  unfold tailWord_6892437
  simp only [CollatzResearch.WordTrace]
  refine ⟨251387829730885358368243565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167591886487256905578829043 251387829730885358368243565)
  ·
    refine ⟨94270436149082009388091337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251387829730885358368243565 94270436149082009388091337)
    ·
      refine ⟨70702827111811507041068503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94270436149082009388091337 70702827111811507041068503)
      ·
        refine ⟨106054240667717260561602755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70702827111811507041068503 106054240667717260561602755)
        ·
          refine ⟨159081361001575890842404133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106054240667717260561602755 159081361001575890842404133)
          ·
            refine ⟨29827755187795479532950775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159081361001575890842404133 29827755187795479532950775)
            ·
              refine ⟨44741632781693219299426163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29827755187795479532950775 44741632781693219299426163)
              ·
                refine ⟨67112449172539828949139245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44741632781693219299426163 67112449172539828949139245)
                ·
                  refine ⟨25167168439702435855927217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67112449172539828949139245 25167168439702435855927217)
                  ·
                    refine ⟨18875376329776826891945413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25167168439702435855927217 18875376329776826891945413)
                    ·
                      refine ⟨3539133061833155042239765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18875376329776826891945413 3539133061833155042239765)
                      ·
                        rfl

theorem cell23_6892437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_6892437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892437 prefixEnd_6892437 := by exact prefixLift 6892437
  have htrace : WordTrace (prefixWord ++ tailWord_6892437) baseStart_6892437 baseEnd_6892437 := by
    simpa [prefixWord, tailWord_6892437, baseEnd_6892437] using wordTrace_append hprefix tailTrace_6892437
  have hstable : (prefixWord ++ tailWord_6892437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892437).length < 2 ^ (prefixWord ++ tailWord_6892437).sum := by decide
  have hdescent : baseEnd_6892437 < baseStart_6892437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892457 : List Nat := [1, 2, 1, 1, 1, 1, 5, 2, 3, 3, 3]
def baseStart_6892457 : Nat := 118140960795 + 6892457 * 2 ^ 59
def prefixEnd_6892457 : Nat := 4983230072969 + 3 ^ 40 * 6892457 * 2
def baseEnd_6892457 : Nat := 3539143331446244963989673

theorem tailTrace_6892457 : CollatzResearch.WordTrace tailWord_6892457 prefixEnd_6892457 3539143331446244963989673 := by
  unfold tailWord_6892457
  simp only [CollatzResearch.WordTrace]
  refine ⟨251388559190812901783971625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167592372793875267855981083 251388559190812901783971625)
  ·
    refine ⟨188541419393109676337978719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251388559190812901783971625 188541419393109676337978719)
    ·
      refine ⟨282812129089664514506968079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188541419393109676337978719 282812129089664514506968079)
      ·
        refine ⟨424218193634496771760452119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282812129089664514506968079 424218193634496771760452119)
        ·
          refine ⟨636327290451745157640678179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424218193634496771760452119 636327290451745157640678179)
          ·
            refine ⟨954490935677617736461017269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 636327290451745157640678179 954490935677617736461017269)
            ·
              refine ⟨89483525219776662793220369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 954490935677617736461017269 89483525219776662793220369)
              ·
                refine ⟨67112643914832497094915277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89483525219776662793220369 67112643914832497094915277)
                ·
                  refine ⟨25167241468062186410593229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67112643914832497094915277 25167241468062186410593229)
                  ·
                    refine ⟨9437715550523319903972461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25167241468062186410593229 9437715550523319903972461)
                    ·
                      refine ⟨3539143331446244963989673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9437715550523319903972461 3539143331446244963989673)
                      ·
                        rfl

theorem cell23_6892457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 3, 3].length) (baseStart_6892457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892457 prefixEnd_6892457 := by exact prefixLift 6892457
  have htrace : WordTrace (prefixWord ++ tailWord_6892457) baseStart_6892457 baseEnd_6892457 := by
    simpa [prefixWord, tailWord_6892457, baseEnd_6892457] using wordTrace_append hprefix tailTrace_6892457
  have hstable : (prefixWord ++ tailWord_6892457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892457).length < 2 ^ (prefixWord ++ tailWord_6892457).sum := by decide
  have hdescent : baseEnd_6892457 < baseStart_6892457 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892468 : List Nat := [2, 5, 2, 1, 1, 1, 2, 3, 2, 4]
def baseStart_6892468 : Nat := 118140960795 + 6892468 * 2 ^ 59
def prefixEnd_6892468 : Nat := 4983230072969 + 3 ^ 40 * 6892468 * 2
def baseEnd_6892468 : Nat := 1179716326577814806984041

theorem tailTrace_6892468 : CollatzResearch.WordTrace tailWord_6892468 prefixEnd_6892468 1179716326577814806984041 := by
  unfold tailWord_6892468
  simp only [CollatzResearch.WordTrace]
  refine ⟨125694480196886525331311029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167592640262515367108414705 125694480196886525331311029)
  ·
    refine ⟨11783857518458111749810409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125694480196886525331311029 11783857518458111749810409)
    ·
      refine ⟨8837893138843583812357807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11783857518458111749810409 8837893138843583812357807)
      ·
        refine ⟨13256839708265375718536711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8837893138843583812357807 13256839708265375718536711)
        ·
          refine ⟨19885259562398063577805067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13256839708265375718536711 19885259562398063577805067)
          ·
            refine ⟨29827889343597095366707601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19885259562398063577805067 29827889343597095366707601)
            ·
              refine ⟨22370917007697821525030701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29827889343597095366707601 22370917007697821525030701)
              ·
                refine ⟨8389093877886683071886513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22370917007697821525030701 8389093877886683071886513)
                ·
                  refine ⟨6291820408415012303914885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8389093877886683071886513 6291820408415012303914885)
                  ·
                    refine ⟨1179716326577814806984041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6291820408415012303914885 1179716326577814806984041)
                    ·
                      rfl

theorem cell23_6892468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_6892468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892468 prefixEnd_6892468 := by exact prefixLift 6892468
  have htrace : WordTrace (prefixWord ++ tailWord_6892468) baseStart_6892468 baseEnd_6892468 := by
    simpa [prefixWord, tailWord_6892468, baseEnd_6892468] using wordTrace_append hprefix tailTrace_6892468
  have hstable : (prefixWord ++ tailWord_6892468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892468).length < 2 ^ (prefixWord ++ tailWord_6892468).sum := by decide
  have hdescent : baseEnd_6892468 < baseStart_6892468 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892474 : List Nat := [3, 1, 1, 1, 2, 1, 6, 1, 1, 3, 3]
def baseStart_6892474 : Nat := 118140960795 + 6892474 * 2 ^ 59
def prefixEnd_6892474 : Nat := 4983230072969 + 3 ^ 40 * 6892474 * 2
def baseEnd_6892474 : Nat := 3539152060617371397477095

theorem tailTrace_6892474 : CollatzResearch.WordTrace tailWord_6892474 prefixEnd_6892474 3539152060617371397477095 := by
  unfold tailWord_6892474
  simp only [CollatzResearch.WordTrace]
  refine ⟨62847294807937828421835119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167592786154500875791560317 62847294807937828421835119)
  ·
    refine ⟨94270942211906742632752679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62847294807937828421835119 94270942211906742632752679)
    ·
      refine ⟨141406413317860113949129019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94270942211906742632752679 141406413317860113949129019)
      ·
        refine ⟨212109619976790170923693529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141406413317860113949129019 212109619976790170923693529)
        ·
          refine ⟨159082214982592628192770147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212109619976790170923693529 159082214982592628192770147)
          ·
            refine ⟨238623322473888942289155221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159082214982592628192770147 238623322473888942289155221)
            ·
              refine ⟨11185468240963544169804151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 238623322473888942289155221 11185468240963544169804151)
              ·
                refine ⟨16778202361445316254706227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11185468240963544169804151 16778202361445316254706227)
                ·
                  refine ⟨25167303542167974382059341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16778202361445316254706227 25167303542167974382059341)
                  ·
                    refine ⟨9437738828312990393272253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25167303542167974382059341 9437738828312990393272253)
                    ·
                      refine ⟨3539152060617371397477095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9437738828312990393272253 3539152060617371397477095)
                      ·
                        rfl

theorem cell23_6892474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 1, 3, 3].length) (baseStart_6892474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892474 prefixEnd_6892474 := by exact prefixLift 6892474
  have htrace : WordTrace (prefixWord ++ tailWord_6892474) baseStart_6892474 baseEnd_6892474 := by
    simpa [prefixWord, tailWord_6892474, baseEnd_6892474] using wordTrace_append hprefix tailTrace_6892474
  have hstable : (prefixWord ++ tailWord_6892474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892474).length < 2 ^ (prefixWord ++ tailWord_6892474).sum := by decide
  have hdescent : baseEnd_6892474 < baseStart_6892474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892486 : List Nat := [6, 1, 3, 1, 1, 1, 2, 3, 1, 1, 3]
def baseStart_6892486 : Nat := 118140960795 + 6892486 * 2 ^ 59
def prefixEnd_6892486 : Nat := 4983230072969 + 3 ^ 40 * 6892486 * 2
def baseEnd_6892486 : Nat := 3539158222385225350527041

theorem tailTrace_6892486 : CollatzResearch.WordTrace tailWord_6892486 prefixEnd_6892486 3539158222385225350527041 := by
  unfold tailWord_6892486
  simp only [CollatzResearch.WordTrace]
  refine ⟨7855925528365869991774291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 167593077938471893157851541 7855925528365869991774291)
  ·
    refine ⟨11783888292548804987661437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7855925528365869991774291 11783888292548804987661437)
    ·
      refine ⟨4418958109705801870373039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11783888292548804987661437 4418958109705801870373039)
      ·
        refine ⟨6628437164558702805559559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4418958109705801870373039 6628437164558702805559559)
        ·
          refine ⟨9942655746838054208339339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6628437164558702805559559 9942655746838054208339339)
          ·
            refine ⟨14913983620257081312509009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9942655746838054208339339 14913983620257081312509009)
            ·
              refine ⟨11185487715192810984381757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14913983620257081312509009 11185487715192810984381757)
              ·
                refine ⟨4194557893197304119143159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11185487715192810984381757 4194557893197304119143159)
                ·
                  refine ⟨6291836839795956178714739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4194557893197304119143159 6291836839795956178714739)
                  ·
                    refine ⟨9437755259693934268072109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6291836839795956178714739 9437755259693934268072109)
                    ·
                      refine ⟨3539158222385225350527041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9437755259693934268072109 3539158222385225350527041)
                      ·
                        rfl

theorem cell23_6892486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_6892486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892486 prefixEnd_6892486 := by exact prefixLift 6892486
  have htrace : WordTrace (prefixWord ++ tailWord_6892486) baseStart_6892486 baseEnd_6892486 := by
    simpa [prefixWord, tailWord_6892486, baseEnd_6892486] using wordTrace_append hprefix tailTrace_6892486
  have hstable : (prefixWord ++ tailWord_6892486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892486).length < 2 ^ (prefixWord ++ tailWord_6892486).sum := by decide
  have hdescent : baseEnd_6892486 < baseStart_6892486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892532 : List Nat := [2, 6, 2, 1, 1, 2, 2, 7]
def baseStart_6892532 : Nat := 118140960795 + 6892532 * 2 ^ 59
def prefixEnd_6892532 : Nat := 4983230072969 + 3 ^ 40 * 6892532 * 2
def baseEnd_6892532 : Nat := 131080808981308598909327

theorem tailTrace_6892532 : CollatzResearch.WordTrace tailWord_6892532 prefixEnd_6892532 131080808981308598909327 := by
  unfold tailWord_6892532
  simp only [CollatzResearch.WordTrace]
  refine ⟨125695647332770594796475925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167594196443694126395301233 125695647332770594796475925)
  ·
    refine ⟨5891983468723621631084809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 125695647332770594796475925 5891983468723621631084809)
    ·
      refine ⟨4418987601542716223313607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5891983468723621631084809 4418987601542716223313607)
      ·
        refine ⟨6628481402314074334970411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4418987601542716223313607 6628481402314074334970411)
        ·
          refine ⟨9942722103471111502455617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6628481402314074334970411 9942722103471111502455617)
          ·
            refine ⟨7457041577603333626841713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9942722103471111502455617 7457041577603333626841713)
            ·
              refine ⟨5592781183202500220131285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7457041577603333626841713 5592781183202500220131285)
              ·
                refine ⟨131080808981308598909327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5592781183202500220131285 131080808981308598909327)
                ·
                  rfl

theorem cell23_6892532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 7].length) (baseStart_6892532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892532 prefixEnd_6892532 := by exact prefixLift 6892532
  have htrace : WordTrace (prefixWord ++ tailWord_6892532) baseStart_6892532 baseEnd_6892532 := by
    simpa [prefixWord, tailWord_6892532, baseEnd_6892532] using wordTrace_append hprefix tailTrace_6892532
  have hstable : (prefixWord ++ tailWord_6892532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892532).length < 2 ^ (prefixWord ++ tailWord_6892532).sum := by decide
  have hdescent : baseEnd_6892532 < baseStart_6892532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892537 : List Nat := [1, 2, 1, 3, 1, 3, 1, 4, 7]
def baseStart_6892537 : Nat := 118140960795 + 6892537 * 2 ^ 59
def prefixEnd_6892537 : Nat := 4983230072969 + 3 ^ 40 * 6892537 * 2
def baseEnd_6892537 : Nat := 393242712210956072332145

theorem tailTrace_6892537 : CollatzResearch.WordTrace tailWord_6892537 prefixEnd_6892537 393242712210956072332145 := by
  unfold tailWord_6892537
  simp only [CollatzResearch.WordTrace]
  refine ⟨251391477030523075446883865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167594318020348716964589243 251391477030523075446883865)
  ·
    refine ⟨188543607772892306585162899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251391477030523075446883865 188543607772892306585162899)
    ·
      refine ⟨282815411659338459877744349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188543607772892306585162899 282815411659338459877744349)
      ·
        refine ⟨106055779372251922454154131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282815411659338459877744349 106055779372251922454154131)
        ·
          refine ⟨159083669058377883681231197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106055779372251922454154131 159083669058377883681231197)
          ·
            refine ⟨59656375896891706380461699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159083669058377883681231197 59656375896891706380461699)
            ·
              refine ⟨89484563845337559570692549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59656375896891706380461699 89484563845337559570692549)
              ·
                refine ⟨16778355721000792419504853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89484563845337559570692549 16778355721000792419504853)
                ·
                  refine ⟨393242712210956072332145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16778355721000792419504853 393242712210956072332145)
                  ·
                    rfl

theorem cell23_6892537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 7].length) (baseStart_6892537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892537 prefixEnd_6892537 := by exact prefixLift 6892537
  have htrace : WordTrace (prefixWord ++ tailWord_6892537) baseStart_6892537 baseEnd_6892537 := by
    simpa [prefixWord, tailWord_6892537, baseEnd_6892537] using wordTrace_append hprefix tailTrace_6892537
  have hstable : (prefixWord ++ tailWord_6892537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892537).length < 2 ^ (prefixWord ++ tailWord_6892537).sum := by decide
  have hdescent : baseEnd_6892537 < baseStart_6892537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892601 : List Nat := [1, 2, 1, 5, 2, 2, 2, 1, 2, 5]
def baseStart_6892601 : Nat := 118140960795 + 6892601 * 2 ^ 59
def prefixEnd_6892601 : Nat := 4983230072969 + 3 ^ 40 * 6892601 * 2
def baseEnd_6892601 : Nat := 1179739090886830800196337

theorem tailTrace_6892601 : CollatzResearch.WordTrace tailWord_6892601 prefixEnd_6892601 1179739090886830800196337 := by
  unfold tailWord_6892601
  simp only [CollatzResearch.WordTrace]
  refine ⟨251393811302291214377213657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167595874201527476251475771 251393811302291214377213657)
  ·
    refine ⟨188545358476718410782910243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251393811302291214377213657 188545358476718410782910243)
    ·
      refine ⟨282818037715077616174365365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188545358476718410782910243 282818037715077616174365365)
      ·
        refine ⟨26514191035788526516346753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 282818037715077616174365365 26514191035788526516346753)
        ·
          refine ⟨19885643276841394887260065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26514191035788526516346753 19885643276841394887260065)
          ·
            refine ⟨14914232457631046165445049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19885643276841394887260065 14914232457631046165445049)
            ·
              refine ⟨11185674343223284624083787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14914232457631046165445049 11185674343223284624083787)
              ·
                refine ⟨16778511514834926936125681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11185674343223284624083787 16778511514834926936125681)
                ·
                  refine ⟨12583883636126195202094261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16778511514834926936125681 12583883636126195202094261)
                  ·
                    refine ⟨1179739090886830800196337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12583883636126195202094261 1179739090886830800196337)
                    ·
                      rfl

theorem cell23_6892601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 2, 5].length) (baseStart_6892601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892601 prefixEnd_6892601 := by exact prefixLift 6892601
  have htrace : WordTrace (prefixWord ++ tailWord_6892601) baseStart_6892601 baseEnd_6892601 := by
    simpa [prefixWord, tailWord_6892601, baseEnd_6892601] using wordTrace_append hprefix tailTrace_6892601
  have hstable : (prefixWord ++ tailWord_6892601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892601).length < 2 ^ (prefixWord ++ tailWord_6892601).sum := by decide
  have hdescent : baseEnd_6892601 < baseStart_6892601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892665 : List Nat := [1, 2, 1, 3, 5, 1, 2, 3, 1, 4]
def baseStart_6892665 : Nat := 118140960795 + 6892665 * 2 ^ 59
def prefixEnd_6892665 : Nat := 4983230072969 + 3 ^ 40 * 6892665 * 2
def baseEnd_6892665 : Nat := 1179750045140793383396239

theorem tailTrace_6892665 : CollatzResearch.WordTrace tailWord_6892665 prefixEnd_6892665 1179750045140793383396239 := by
  unfold tailWord_6892665
  simp only [CollatzResearch.WordTrace]
  refine ⟨251396145574059353307543449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167597430382706235538362299 251396145574059353307543449)
  ·
    refine ⟨188547109180544514980657587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251396145574059353307543449 188547109180544514980657587)
    ·
      refine ⟨282820663770816772470986381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188547109180544514980657587 282820663770816772470986381)
      ·
        refine ⟨106057748914056289676619893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282820663770816772470986381 106057748914056289676619893)
        ·
          refine ⟨9942913960692777157183115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106057748914056289676619893 9942913960692777157183115)
          ·
            refine ⟨14914370941039165735774673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9942913960692777157183115 14914370941039165735774673)
            ·
              refine ⟨11185778205779374301831005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14914370941039165735774673 11185778205779374301831005)
              ·
                refine ⟨4194666827167265363186627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11185778205779374301831005 4194666827167265363186627)
                ·
                  refine ⟨6292000240750898044779941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4194666827167265363186627 6292000240750898044779941)
                  ·
                    refine ⟨1179750045140793383396239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6292000240750898044779941 1179750045140793383396239)
                    ·
                      rfl

theorem cell23_6892665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 3, 1, 4].length) (baseStart_6892665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892665 prefixEnd_6892665 := by exact prefixLift 6892665
  have htrace : WordTrace (prefixWord ++ tailWord_6892665) baseStart_6892665 baseEnd_6892665 := by
    simpa [prefixWord, tailWord_6892665, baseEnd_6892665] using wordTrace_append hprefix tailTrace_6892665
  have hstable : (prefixWord ++ tailWord_6892665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892665).length < 2 ^ (prefixWord ++ tailWord_6892665).sum := by decide
  have hdescent : baseEnd_6892665 < baseStart_6892665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892698 : List Nat := [3, 1, 1, 5, 1, 1, 1, 2, 1, 5, 2]
def baseStart_6892698 : Nat := 118140960795 + 6892698 * 2 ^ 59
def prefixEnd_6892698 : Nat := 4983230072969 + 3 ^ 40 * 6892698 * 2
def baseEnd_6892698 : Nat := 3539267080283978521076065

theorem tailTrace_6892698 : CollatzResearch.WordTrace tailWord_6892698 prefixEnd_6892698 3539267080283978521076065 := by
  unfold tailWord_6892698
  simp only [CollatzResearch.WordTrace]
  refine ⟨62849337295734949985873687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167598232788626533295663165 62849337295734949985873687)
  ·
    refine ⟨94274005943602424978810531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62849337295734949985873687 94274005943602424978810531)
    ·
      refine ⟨141411008915403637468215797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94274005943602424978810531 141411008915403637468215797)
      ·
        refine ⟨13257282085819091012645231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 141411008915403637468215797 13257282085819091012645231)
        ·
          refine ⟨19885923128728636518967847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13257282085819091012645231 19885923128728636518967847)
          ·
            refine ⟨29828884693092954778451771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19885923128728636518967847 29828884693092954778451771)
            ·
              refine ⟨44743327039639432167677657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29828884693092954778451771 44743327039639432167677657)
              ·
                refine ⟨33557495279729574125758243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44743327039639432167677657 33557495279729574125758243)
                ·
                  refine ⟨50336242919594361188637365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33557495279729574125758243 50336242919594361188637365)
                  ·
                    refine ⟨4719022773711971361434753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50336242919594361188637365 4719022773711971361434753)
                    ·
                      refine ⟨3539267080283978521076065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4719022773711971361434753 3539267080283978521076065)
                      ·
                        rfl

theorem cell23_6892698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_6892698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892698 prefixEnd_6892698 := by exact prefixLift 6892698
  have htrace : WordTrace (prefixWord ++ tailWord_6892698) baseStart_6892698 baseEnd_6892698 := by
    simpa [prefixWord, tailWord_6892698, baseEnd_6892698] using wordTrace_append hprefix tailTrace_6892698
  have hstable : (prefixWord ++ tailWord_6892698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892698).length < 2 ^ (prefixWord ++ tailWord_6892698).sum := by decide
  have hdescent : baseEnd_6892698 < baseStart_6892698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892708 : List Nat := [2, 3, 1, 2, 3, 2, 2, 2, 1, 5]
def baseStart_6892708 : Nat := 118140960795 + 6892708 * 2 ^ 59
def prefixEnd_6892708 : Nat := 4983230072969 + 3 ^ 40 * 6892708 * 2
def baseEnd_6892708 : Nat := 1179757405030174493983673

theorem tailTrace_6892708 : CollatzResearch.WordTrace tailWord_6892708 prefixEnd_6892708 1179757405030174493983673 := by
  unfold tailWord_6892708
  simp only [CollatzResearch.WordTrace]
  refine ⟨125698856956451785825679389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167598475941935714434239185 125698856956451785825679389)
  ·
    refine ⟨47137071358669419684629771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125698856956451785825679389 47137071358669419684629771)
    ·
      refine ⟨70705607038004129526944657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47137071358669419684629771 70705607038004129526944657)
      ·
        refine ⟨53029205278503097145208493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70705607038004129526944657 53029205278503097145208493)
        ·
          refine ⟨19885951979438661429453185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53029205278503097145208493 19885951979438661429453185)
          ·
            refine ⟨14914463984578996072089889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19885951979438661429453185 14914463984578996072089889)
            ·
              refine ⟨11185847988434247054067417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14914463984578996072089889 11185847988434247054067417)
              ·
                refine ⟨8389385991325685290550563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11185847988434247054067417 8389385991325685290550563)
                ·
                  refine ⟨12584078986988527935825845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8389385991325685290550563 12584078986988527935825845)
                  ·
                    refine ⟨1179757405030174493983673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12584078986988527935825845 1179757405030174493983673)
                    ·
                      rfl

theorem cell23_6892708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2, 1, 5].length) (baseStart_6892708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892708 prefixEnd_6892708 := by exact prefixLift 6892708
  have htrace : WordTrace (prefixWord ++ tailWord_6892708) baseStart_6892708 baseEnd_6892708 := by
    simpa [prefixWord, tailWord_6892708, baseEnd_6892708] using wordTrace_append hprefix tailTrace_6892708
  have hstable : (prefixWord ++ tailWord_6892708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892708).length < 2 ^ (prefixWord ++ tailWord_6892708).sum := by decide
  have hdescent : baseEnd_6892708 < baseStart_6892708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892722 : List Nat := [3, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3]
def baseStart_6892722 : Nat := 118140960795 + 6892722 * 2 ^ 59
def prefixEnd_6892722 : Nat := 4983230072969 + 3 ^ 40 * 6892722 * 2
def baseEnd_6892722 : Nat := 3539279403819686427175955

theorem tailTrace_6892722 : CollatzResearch.WordTrace tailWord_6892722 prefixEnd_6892722 3539279403819686427175955 := by
  unfold tailWord_6892722
  simp only [CollatzResearch.WordTrace]
  refine ⟨62849556133713213010592105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167598816356568568028245613 62849556133713213010592105)
  ·
    refine ⟨47137167100284909757944079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62849556133713213010592105 47137167100284909757944079)
    ·
      refine ⟨70705750650427364636916119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47137167100284909757944079 70705750650427364636916119)
      ·
        refine ⟨106058625975641046955374179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70705750650427364636916119 106058625975641046955374179)
        ·
          refine ⟨159087938963461570433061269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106058625975641046955374179 159087938963461570433061269)
          ·
            refine ⟨7457247138912261114049747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 159087938963461570433061269 7457247138912261114049747)
            ·
              refine ⟨11185870708368391671074621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7457247138912261114049747 11185870708368391671074621)
              ·
                refine ⟨4194701515638146876652983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11185870708368391671074621 4194701515638146876652983)
                ·
                  refine ⟨6292052273457220314979475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4194701515638146876652983 6292052273457220314979475)
                  ·
                    refine ⟨9438078410185830472469213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6292052273457220314979475 9438078410185830472469213)
                    ·
                      refine ⟨3539279403819686427175955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9438078410185830472469213 3539279403819686427175955)
                      ·
                        rfl

theorem cell23_6892722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3].length) (baseStart_6892722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892722 prefixEnd_6892722 := by exact prefixLift 6892722
  have htrace : WordTrace (prefixWord ++ tailWord_6892722) baseStart_6892722 baseEnd_6892722 := by
    simpa [prefixWord, tailWord_6892722, baseEnd_6892722] using wordTrace_append hprefix tailTrace_6892722
  have hstable : (prefixWord ++ tailWord_6892722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892722).length < 2 ^ (prefixWord ++ tailWord_6892722).sum := by decide
  have hdescent : baseEnd_6892722 < baseStart_6892722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892761 : List Nat := [1, 2, 1, 2, 3, 1, 1, 5, 1, 3, 3]
def baseStart_6892761 : Nat := 118140960795 + 6892761 * 2 ^ 59
def prefixEnd_6892761 : Nat := 4983230072969 + 3 ^ 40 * 6892761 * 2
def baseEnd_6892761 : Nat := 3539299429565211774588275

theorem tailTrace_6892761 : CollatzResearch.WordTrace tailWord_6892761 prefixEnd_6892761 3539299429565211774588275 := by
  unfold tailWord_6892761
  simp only [CollatzResearch.WordTrace]
  refine ⟨251399646981711561703038137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167599764654474374468692091 251399646981711561703038137)
  ·
    refine ⟨188549735236283671277278603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251399646981711561703038137 188549735236283671277278603)
    ·
      refine ⟨282824602854425506915917905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188549735236283671277278603 282824602854425506915917905)
      ·
        refine ⟨212118452140819130186938429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282824602854425506915917905 212118452140819130186938429)
        ·
          refine ⟨79544419552807173820101911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212118452140819130186938429 79544419552807173820101911)
          ·
            refine ⟨119316629329210760730152867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79544419552807173820101911 119316629329210760730152867)
            ·
              refine ⟨178974943993816141095229301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119316629329210760730152867 178974943993816141095229301)
              ·
                refine ⟨16778900999420263227677747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 178974943993816141095229301 16778900999420263227677747)
                ·
                  refine ⟨25168351499130394841516621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16778900999420263227677747 25168351499130394841516621)
                  ·
                    refine ⟨9438131812173898065568733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25168351499130394841516621 9438131812173898065568733)
                    ·
                      refine ⟨3539299429565211774588275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9438131812173898065568733 3539299429565211774588275)
                      ·
                        rfl

theorem cell23_6892761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 3, 3].length) (baseStart_6892761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892761 prefixEnd_6892761 := by exact prefixLift 6892761
  have htrace : WordTrace (prefixWord ++ tailWord_6892761) baseStart_6892761 baseEnd_6892761 := by
    simpa [prefixWord, tailWord_6892761, baseEnd_6892761] using wordTrace_append hprefix tailTrace_6892761
  have hstable : (prefixWord ++ tailWord_6892761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892761).length < 2 ^ (prefixWord ++ tailWord_6892761).sum := by decide
  have hdescent : baseEnd_6892761 < baseStart_6892761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892765 : List Nat := [1, 4, 3, 2, 2, 1, 1, 1, 3, 2, 3]
def baseStart_6892765 : Nat := 118140960795 + 6892765 * 2 ^ 59
def prefixEnd_6892765 : Nat := 4983230072969 + 3 ^ 40 * 6892765 * 2
def baseEnd_6892765 : Nat := 3539301483487829758938257

theorem tailTrace_6892765 : CollatzResearch.WordTrace tailWord_6892765 prefixEnd_6892765 3539301483487829758938257 := by
  unfold tailWord_6892765
  simp only [CollatzResearch.WordTrace]
  refine ⟨251399792873697070386183749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167599861915798046924122499 251399792873697070386183749)
  ·
    refine ⟨47137461163818200697409453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 251399792873697070386183749 47137461163818200697409453)
    ·
      refine ⟨17676547936431825261528545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47137461163818200697409453 17676547936431825261528545)
      ·
        refine ⟨13257410952323868946146409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17676547936431825261528545 13257410952323868946146409)
        ·
          refine ⟨9943058214242901709609807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13257410952323868946146409 9943058214242901709609807)
          ·
            refine ⟨14914587321364352564414711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9943058214242901709609807 14914587321364352564414711)
            ·
              refine ⟨22371880982046528846622067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14914587321364352564414711 22371880982046528846622067)
              ·
                refine ⟨33557821473069793269933101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22371880982046528846622067 33557821473069793269933101)
                ·
                  refine ⟨12584183052401172476224913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33557821473069793269933101 12584183052401172476224913)
                  ·
                    refine ⟨9438137289300879357168685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12584183052401172476224913 9438137289300879357168685)
                    ·
                      refine ⟨3539301483487829758938257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9438137289300879357168685 3539301483487829758938257)
                      ·
                        rfl

theorem cell23_6892765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_6892765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892765 prefixEnd_6892765 := by exact prefixLift 6892765
  have htrace : WordTrace (prefixWord ++ tailWord_6892765) baseStart_6892765 baseEnd_6892765 := by
    simpa [prefixWord, tailWord_6892765, baseEnd_6892765] using wordTrace_append hprefix tailTrace_6892765
  have hstable : (prefixWord ++ tailWord_6892765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892765).length < 2 ^ (prefixWord ++ tailWord_6892765).sum := by decide
  have hdescent : baseEnd_6892765 < baseStart_6892765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892778 : List Nat := [3, 1, 3, 1, 1, 4, 1, 2, 1, 3, 3]
def baseStart_6892778 : Nat := 118140960795 + 6892778 * 2 ^ 59
def prefixEnd_6892778 : Nat := 4983230072969 + 3 ^ 40 * 6892778 * 2
def baseEnd_6892778 : Nat := 3539308158736338208075697

theorem tailTrace_6892778 : CollatzResearch.WordTrace tailWord_6892778 prefixEnd_6892778 3539308158736338208075697 := by
  unfold tailWord_6892778
  simp only [CollatzResearch.WordTrace]
  refine ⟨62850066755662493401601747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167600178015099982404271325 62850066755662493401601747)
  ·
    refine ⟨94275100133493740102402621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62850066755662493401601747 94275100133493740102402621)
    ·
      refine ⟨35353162550060152538400983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94275100133493740102402621 35353162550060152538400983)
      ·
        refine ⟨53029743825090228807601475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35353162550060152538400983 53029743825090228807601475)
        ·
          refine ⟨79544615737635343211402213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53029743825090228807601475 79544615737635343211402213)
          ·
            refine ⟨14914615450806626852137915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79544615737635343211402213 14914615450806626852137915)
            ·
              refine ⟨22371923176209940278206873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14914615450806626852137915 22371923176209940278206873)
              ·
                refine ⟨16778942382157455208655155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22371923176209940278206873 16778942382157455208655155)
                ·
                  refine ⟨25168413573236182812982733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16778942382157455208655155 25168413573236182812982733)
                  ·
                    refine ⟨9438155089963568554868525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25168413573236182812982733 9438155089963568554868525)
                    ·
                      refine ⟨3539308158736338208075697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9438155089963568554868525 3539308158736338208075697)
                      ·
                        rfl

theorem cell23_6892778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_6892778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892778 prefixEnd_6892778 := by exact prefixLift 6892778
  have htrace : WordTrace (prefixWord ++ tailWord_6892778) baseStart_6892778 baseEnd_6892778 := by
    simpa [prefixWord, tailWord_6892778, baseEnd_6892778] using wordTrace_append hprefix tailTrace_6892778
  have hstable : (prefixWord ++ tailWord_6892778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892778).length < 2 ^ (prefixWord ++ tailWord_6892778).sum := by decide
  have hdescent : baseEnd_6892778 < baseStart_6892778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892796 : List Nat := [2, 2, 2, 1, 5, 2, 2, 2, 1, 2, 2]
def baseStart_6892796 : Nat := 118140960795 + 6892796 * 2 ^ 59
def prefixEnd_6892796 : Nat := 4983230072969 + 3 ^ 40 * 6892796 * 2
def baseEnd_6892796 : Nat := 3539317401388119137650615

theorem tailTrace_6892796 : CollatzResearch.WordTrace tailWord_6892796 prefixEnd_6892796 3539317401388119137650615 := by
  unfold tailWord_6892796
  simp only [CollatzResearch.WordTrace]
  refine ⟨125700461768292381340281121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167600615691056508453708161 125700461768292381340281121)
  ·
    refine ⟨94275346326219286005210841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125700461768292381340281121 94275346326219286005210841)
    ·
      refine ⟨70706509744664464503908131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94275346326219286005210841 70706509744664464503908131)
      ·
        refine ⟨106059764616996696755862197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70706509744664464503908131 106059764616996696755862197)
        ·
          refine ⟨9943102932843440320862081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106059764616996696755862197 9943102932843440320862081)
          ·
            refine ⟨7457327199632580240646561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9943102932843440320862081 7457327199632580240646561)
            ·
              refine ⟨5592995399724435180484921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7457327199632580240646561 5592995399724435180484921)
              ·
                refine ⟨4194746549793326385363691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5592995399724435180484921 4194746549793326385363691)
                ·
                  refine ⟨6292119824689989578045537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4194746549793326385363691 6292119824689989578045537)
                  ·
                    refine ⟨4719089868517492183534153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6292119824689989578045537 4719089868517492183534153)
                    ·
                      refine ⟨3539317401388119137650615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4719089868517492183534153 3539317401388119137650615)
                      ·
                        rfl

theorem cell23_6892796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 2, 1, 2, 2].length) (baseStart_6892796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892796 prefixEnd_6892796 := by exact prefixLift 6892796
  have htrace : WordTrace (prefixWord ++ tailWord_6892796) baseStart_6892796 baseEnd_6892796 := by
    simpa [prefixWord, tailWord_6892796, baseEnd_6892796] using wordTrace_append hprefix tailTrace_6892796
  have hstable : (prefixWord ++ tailWord_6892796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892796).length < 2 ^ (prefixWord ++ tailWord_6892796).sum := by decide
  have hdescent : baseEnd_6892796 < baseStart_6892796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892801 : List Nat := [1, 2, 4, 1, 1, 3, 1, 1, 2, 3, 4]
def baseStart_6892801 : Nat := 118140960795 + 6892801 * 2 ^ 59
def prefixEnd_6892801 : Nat := 4983230072969 + 3 ^ 40 * 6892801 * 2
def baseEnd_6892801 : Nat := 3539319968791391618088091

theorem tailTrace_6892801 : CollatzResearch.WordTrace tailWord_6892801 prefixEnd_6892801 3539319968791391618088091 := by
  unfold tailWord_6892801
  simp only [CollatzResearch.WordTrace]
  refine ⟨251401105901566648534494257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167600737267711099022996171 251401105901566648534494257)
  ·
    refine ⟨188550829426174986400870693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251401105901566648534494257 188550829426174986400870693)
    ·
      refine ⟨35353280517407809950163255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188550829426174986400870693 35353280517407809950163255)
      ·
        refine ⟨53029920776111714925244883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35353280517407809950163255 53029920776111714925244883)
        ·
          refine ⟨79544881164167572387867325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53029920776111714925244883 79544881164167572387867325)
          ·
            refine ⟨29829330436562839645450247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79544881164167572387867325 29829330436562839645450247)
            ·
              refine ⟨44743995654844259468175371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29829330436562839645450247 44743995654844259468175371)
              ·
                refine ⟨67115993482266389202263057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44743995654844259468175371 67115993482266389202263057)
                ·
                  refine ⟨50336995111699791901697293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67115993482266389202263057 50336995111699791901697293)
                  ·
                    refine ⟨18876373166887421963136485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50336995111699791901697293 18876373166887421963136485)
                    ·
                      refine ⟨3539319968791391618088091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18876373166887421963136485 3539319968791391618088091)
                      ·
                        rfl

theorem cell23_6892801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_6892801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892801 prefixEnd_6892801 := by exact prefixLift 6892801
  have htrace : WordTrace (prefixWord ++ tailWord_6892801) baseStart_6892801 baseEnd_6892801 := by
    simpa [prefixWord, tailWord_6892801, baseEnd_6892801] using wordTrace_append hprefix tailTrace_6892801
  have hstable : (prefixWord ++ tailWord_6892801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892801).length < 2 ^ (prefixWord ++ tailWord_6892801).sum := by decide
  have hdescent : baseEnd_6892801 < baseStart_6892801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892811 : List Nat := [1, 1, 1, 1, 5, 4, 1, 1, 2, 6]
def baseStart_6892811 : Nat := 118140960795 + 6892811 * 2 ^ 59
def prefixEnd_6892811 : Nat := 4983230072969 + 3 ^ 40 * 6892811 * 2
def baseEnd_6892811 : Nat := 1179775034532645526321015

theorem tailTrace_6892811 : CollatzResearch.WordTrace tailWord_6892811 prefixEnd_6892811 1179775034532645526321015 := by
  unfold tailWord_6892811
  simp only [CollatzResearch.WordTrace]
  refine ⟨251401470631530420242358287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167600980421020280161572191 251401470631530420242358287)
  ·
    refine ⟨377102205947295630363537431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251401470631530420242358287 377102205947295630363537431)
    ·
      refine ⟨565653308920943445545306147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377102205947295630363537431 565653308920943445545306147)
      ·
        refine ⟨848479963381415168317959221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565653308920943445545306147 848479963381415168317959221)
        ·
          refine ⟨79544996567007672029808677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 848479963381415168317959221 79544996567007672029808677)
          ·
            refine ⟨14914686856313938505589127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79544996567007672029808677 14914686856313938505589127)
            ·
              refine ⟨22372030284470907758383691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14914686856313938505589127 22372030284470907758383691)
              ·
                refine ⟨33558045426706361637575537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22372030284470907758383691 33558045426706361637575537)
                ·
                  refine ⟨25168534070029771228181653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33558045426706361637575537 25168534070029771228181653)
                  ·
                    refine ⟨1179775034532645526321015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25168534070029771228181653 1179775034532645526321015)
                    ·
                      rfl

theorem cell23_6892811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 6].length) (baseStart_6892811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892811 prefixEnd_6892811 := by exact prefixLift 6892811
  have htrace : WordTrace (prefixWord ++ tailWord_6892811) baseStart_6892811 baseEnd_6892811 := by
    simpa [prefixWord, tailWord_6892811, baseEnd_6892811] using wordTrace_append hprefix tailTrace_6892811
  have hstable : (prefixWord ++ tailWord_6892811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892811).length < 2 ^ (prefixWord ++ tailWord_6892811).sum := by decide
  have hdescent : baseEnd_6892811 < baseStart_6892811 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892821 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 4, 4, 3]
def baseStart_6892821 : Nat := 118140960795 + 6892821 * 2 ^ 59
def prefixEnd_6892821 : Nat := 4983230072969 + 3 ^ 40 * 6892821 * 2
def baseEnd_6892821 : Nat := 3539330238404481539837999

theorem tailTrace_6892821 : CollatzResearch.WordTrace tailWord_6892821 prefixEnd_6892821 3539330238404481539837999 := by
  unfold tailWord_6892821
  simp only [CollatzResearch.WordTrace]
  refine ⟨251401835361494191950222317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167601223574329461300148211 251401835361494191950222317)
  ·
    refine ⟨94275688260560321981333369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251401835361494191950222317 94275688260560321981333369)
    ·
      refine ⟨70706766195420241486000027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94275688260560321981333369 70706766195420241486000027)
      ·
        refine ⟨106060149293130362229000041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70706766195420241486000027 106060149293130362229000041)
        ·
          refine ⟨79545111969847771671750031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106060149293130362229000041 79545111969847771671750031)
          ·
            refine ⟨119317667954771657507625047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79545111969847771671750031 119317667954771657507625047)
            ·
              refine ⟨178976501932157486261437571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119317667954771657507625047 178976501932157486261437571)
              ·
                refine ⟨268464752898236229392156357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178976501932157486261437571 268464752898236229392156357)
                ·
                  refine ⟨50337141168419293011029317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 268464752898236229392156357 50337141168419293011029317)
                  ·
                    refine ⟨9438213969078617439567997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50337141168419293011029317 9438213969078617439567997)
                    ·
                      refine ⟨3539330238404481539837999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9438213969078617439567997 3539330238404481539837999)
                      ·
                        rfl

theorem cell23_6892821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 4, 3].length) (baseStart_6892821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892821 prefixEnd_6892821 := by exact prefixLift 6892821
  have htrace : WordTrace (prefixWord ++ tailWord_6892821) baseStart_6892821 baseEnd_6892821 := by
    simpa [prefixWord, tailWord_6892821, baseEnd_6892821] using wordTrace_append hprefix tailTrace_6892821
  have hstable : (prefixWord ++ tailWord_6892821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892821).length < 2 ^ (prefixWord ++ tailWord_6892821).sum := by decide
  have hdescent : baseEnd_6892821 < baseStart_6892821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892852 : List Nat := [2, 5, 1, 1, 1, 1, 3, 1, 4, 2, 2]
def baseStart_6892852 : Nat := 118140960795 + 6892852 * 2 ^ 59
def prefixEnd_6892852 : Nat := 4983230072969 + 3 ^ 40 * 6892852 * 2
def baseEnd_6892852 : Nat := 3539346156304770918550357

theorem tailTrace_6892852 : CollatzResearch.WordTrace tailWord_6892852 prefixEnd_6892852 3539346156304770918550357 := by
  unfold tailWord_6892852
  simp only [CollatzResearch.WordTrace]
  refine ⟨125701483012190942122300405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167601977349587922829733873 125701483012190942122300405)
  ·
    refine ⟨11784514032392900823965663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125701483012190942122300405 11784514032392900823965663)
    ·
      refine ⟨17676771048589351235948495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11784514032392900823965663 17676771048589351235948495)
      ·
        refine ⟨26515156572884026853922743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17676771048589351235948495 26515156572884026853922743)
        ·
          refine ⟨39772734859326040280884115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26515156572884026853922743 39772734859326040280884115)
          ·
            refine ⟨59659102288989060421326173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39772734859326040280884115 59659102288989060421326173)
            ·
              refine ⟨22372163358370897657997315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59659102288989060421326173 22372163358370897657997315)
              ·
                refine ⟨33558245037556346486995973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22372163358370897657997315 33558245037556346486995973)
                ·
                  refine ⟨6292170944541814966311745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33558245037556346486995973 6292170944541814966311745)
                  ·
                    refine ⟨4719128208406361224733809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6292170944541814966311745 4719128208406361224733809)
                    ·
                      refine ⟨3539346156304770918550357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4719128208406361224733809 3539346156304770918550357)
                      ·
                        rfl

theorem cell23_6892852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_6892852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892852 prefixEnd_6892852 := by exact prefixLift 6892852
  have htrace : WordTrace (prefixWord ++ tailWord_6892852) baseStart_6892852 baseEnd_6892852 := by
    simpa [prefixWord, tailWord_6892852, baseEnd_6892852] using wordTrace_append hprefix tailTrace_6892852
  have hstable : (prefixWord ++ tailWord_6892852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892852).length < 2 ^ (prefixWord ++ tailWord_6892852).sum := by decide
  have hdescent : baseEnd_6892852 < baseStart_6892852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892858 : List Nat := [3, 1, 1, 1, 4, 1, 1, 6, 5]
def baseStart_6892858 : Nat := 118140960795 + 6892858 * 2 ^ 59
def prefixEnd_6892858 : Nat := 4983230072969 + 3 ^ 40 * 6892858 * 2
def baseEnd_6892858 : Nat := 393261026354299766119481

theorem tailTrace_6892858 : CollatzResearch.WordTrace tailWord_6892858 prefixEnd_6892858 393261026354299766119481 := by
  unfold tailWord_6892858
  simp only [CollatzResearch.WordTrace]
  refine ⟨62850796215590036817329807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167602123241573431512879485 62850796215590036817329807)
  ·
    refine ⟨94276194323385055225994711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62850796215590036817329807 94276194323385055225994711)
    ·
      refine ⟨141414291485077582838992067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94276194323385055225994711 141414291485077582838992067)
      ·
        refine ⟨212121437227616374258488101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141414291485077582838992067 212121437227616374258488101)
        ·
          refine ⟨39772769480178070173466519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212121437227616374258488101 39772769480178070173466519)
          ·
            refine ⟨59659154220267105260199779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39772769480178070173466519 59659154220267105260199779)
            ·
              refine ⟨89488731330400657890299669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59659154220267105260199779 89488731330400657890299669)
              ·
                refine ⟨4194784281112530838607797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89488731330400657890299669 4194784281112530838607797)
                ·
                  refine ⟨393261026354299766119481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4194784281112530838607797 393261026354299766119481)
                  ·
                    rfl

theorem cell23_6892858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 6, 5].length) (baseStart_6892858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892858 prefixEnd_6892858 := by exact prefixLift 6892858
  have htrace : WordTrace (prefixWord ++ tailWord_6892858) baseStart_6892858 baseEnd_6892858 := by
    simpa [prefixWord, tailWord_6892858, baseEnd_6892858] using wordTrace_append hprefix tailTrace_6892858
  have hstable : (prefixWord ++ tailWord_6892858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892858).length < 2 ^ (prefixWord ++ tailWord_6892858).sum := by decide
  have hdescent : baseEnd_6892858 < baseStart_6892858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892871 : List Nat := [1, 1, 4, 1, 2, 3, 1, 2, 1, 7]
def baseStart_6892871 : Nat := 118140960795 + 6892871 * 2 ^ 59
def prefixEnd_6892871 : Nat := 4983230072969 + 3 ^ 40 * 6892871 * 2
def baseEnd_6892871 : Nat := 1179785304145735448070923

theorem tailTrace_6892871 : CollatzResearch.WordTrace tailWord_6892871 prefixEnd_6892871 1179785304145735448070923 := by
  unfold tailWord_6892871
  simp only [CollatzResearch.WordTrace]
  refine ⟨251403659011313050489542467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167602439340875366993028311 251403659011313050489542467)
  ·
    refine ⟨377105488516969575734313701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251403659011313050489542467 377105488516969575734313701)
    ·
      refine ⟨70707279096931795450183819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 377105488516969575734313701 70707279096931795450183819)
      ·
        refine ⟨106060918645397693175275729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70707279096931795450183819 106060918645397693175275729)
        ·
          refine ⟨79545688984048269881456797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106060918645397693175275729 79545688984048269881456797)
          ·
            refine ⟨29829633369018101205546299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79545688984048269881456797 29829633369018101205546299)
            ·
              refine ⟨44744450053527151808319449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29829633369018101205546299 44744450053527151808319449)
              ·
                refine ⟨33558337540145363856239587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44744450053527151808319449 33558337540145363856239587)
                ·
                  refine ⟨50337506310218045784359381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33558337540145363856239587 50337506310218045784359381)
                  ·
                    refine ⟨1179785304145735448070923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50337506310218045784359381 1179785304145735448070923)
                    ·
                      rfl

theorem cell23_6892871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_6892871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892871 prefixEnd_6892871 := by exact prefixLift 6892871
  have htrace : WordTrace (prefixWord ++ tailWord_6892871) baseStart_6892871 baseEnd_6892871 := by
    simpa [prefixWord, tailWord_6892871, baseEnd_6892871] using wordTrace_append hprefix tailTrace_6892871
  have hstable : (prefixWord ++ tailWord_6892871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892871).length < 2 ^ (prefixWord ++ tailWord_6892871).sum := by decide
  have hdescent : baseEnd_6892871 < baseStart_6892871 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892898 : List Nat := [3, 3, 2, 1, 1, 1, 2, 2, 1, 2, 5]
def baseStart_6892898 : Nat := 118140960795 + 6892898 * 2 ^ 59
def prefixEnd_6892898 : Nat := 4983230072969 + 3 ^ 40 * 6892898 * 2
def baseEnd_6892898 : Nat := 3539369776414877738575145

theorem tailTrace_6892898 : CollatzResearch.WordTrace tailWord_6892898 prefixEnd_6892898 3539369776414877738575145 := by
  unfold tailWord_6892898
  simp only [CollatzResearch.WordTrace]
  refine ⟨62851160945553808525193837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167603095854810156067183565 62851160945553808525193837)
  ·
    refine ⟨23569185354582678196947689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62851160945553808525193837 23569185354582678196947689)
    ·
      refine ⟨17676889015937008647710767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23569185354582678196947689 17676889015937008647710767)
      ·
        refine ⟨26515333523905512971566151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17676889015937008647710767 26515333523905512971566151)
        ·
          refine ⟨39773000285858269457349227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26515333523905512971566151 39773000285858269457349227)
          ·
            refine ⟨59659500428787404186023841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39773000285858269457349227 59659500428787404186023841)
            ·
              refine ⟨44744625321590553139517881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59659500428787404186023841 44744625321590553139517881)
              ·
                refine ⟨33558468991192914854638411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44744625321590553139517881 33558468991192914854638411)
                ·
                  refine ⟨50337703486789372281957617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33558468991192914854638411 50337703486789372281957617)
                  ·
                    refine ⟨37753277615092029211468213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50337703486789372281957617 37753277615092029211468213)
                    ·
                      refine ⟨3539369776414877738575145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37753277615092029211468213 3539369776414877738575145)
                      ·
                        rfl

theorem cell23_6892898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_6892898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892898 prefixEnd_6892898 := by exact prefixLift 6892898
  have htrace : WordTrace (prefixWord ++ tailWord_6892898) baseStart_6892898 baseEnd_6892898 := by
    simpa [prefixWord, tailWord_6892898, baseEnd_6892898] using wordTrace_append hprefix tailTrace_6892898
  have hstable : (prefixWord ++ tailWord_6892898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892898).length < 2 ^ (prefixWord ++ tailWord_6892898).sum := by decide
  have hdescent : baseEnd_6892898 < baseStart_6892898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892908 : List Nat := [2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 4]
def baseStart_6892908 : Nat := 118140960795 + 6892908 * 2 ^ 59
def prefixEnd_6892908 : Nat := 4983230072969 + 3 ^ 40 * 6892908 * 2
def baseEnd_6892908 : Nat := 3539374911221422699450099

theorem tailTrace_6892908 : CollatzResearch.WordTrace tailWord_6892908 prefixEnd_6892908 3539374911221422699450099 := by
  unfold tailWord_6892908
  simp only [CollatzResearch.WordTrace]
  refine ⟨125702504256089502904319689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167603339008119337205759585 125702504256089502904319689)
  ·
    refine ⟨94276878192067127178239767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125702504256089502904319689 94276878192067127178239767)
    ·
      refine ⟨141415317288100690767359651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94276878192067127178239767 141415317288100690767359651)
      ·
        refine ⟨212122975932151036151039477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141415317288100690767359651 212122975932151036151039477)
        ·
          refine ⟨19886528993639159639159951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 212122975932151036151039477 19886528993639159639159951)
          ·
            refine ⟨29829793490458739458739927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19886528993639159639159951 29829793490458739458739927)
            ·
              refine ⟨44744690235688109188109891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29829793490458739458739927 44744690235688109188109891)
              ·
                refine ⟨67117035353532163782164837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44744690235688109188109891 67117035353532163782164837)
                ·
                  refine ⟨12584444128787280709155907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67117035353532163782164837 12584444128787280709155907)
                  ·
                    refine ⟨18876666193180921063733861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12584444128787280709155907 18876666193180921063733861)
                    ·
                      refine ⟨3539374911221422699450099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18876666193180921063733861 3539374911221422699450099)
                      ·
                        rfl

theorem cell23_6892908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 4].length) (baseStart_6892908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892908 prefixEnd_6892908 := by exact prefixLift 6892908
  have htrace : WordTrace (prefixWord ++ tailWord_6892908) baseStart_6892908 baseEnd_6892908 := by
    simpa [prefixWord, tailWord_6892908, baseEnd_6892908] using wordTrace_append hprefix tailTrace_6892908
  have hstable : (prefixWord ++ tailWord_6892908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892908).length < 2 ^ (prefixWord ++ tailWord_6892908).sum := by decide
  have hdescent : baseEnd_6892908 < baseStart_6892908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892921 : List Nat := [1, 2, 1, 3, 2, 1, 2, 2, 2, 1, 6]
def baseStart_6892921 : Nat := 118140960795 + 6892921 * 2 ^ 59
def prefixEnd_6892921 : Nat := 4983230072969 + 3 ^ 40 * 6892921 * 2
def baseEnd_6892921 : Nat := 3539381586469931148587539

theorem tailTrace_6892921 : CollatzResearch.WordTrace tailWord_6892921 prefixEnd_6892921 3539381586469931148587539 := by
  unfold tailWord_6892921
  simp only [CollatzResearch.WordTrace]
  refine ⟨251405482661131909028862617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167603655107421272685908411 251405482661131909028862617)
  ·
    refine ⟨188554111995848931771646963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251405482661131909028862617 188554111995848931771646963)
    ·
      refine ⟨282831167993773397657470445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188554111995848931771646963 282831167993773397657470445)
      ·
        refine ⟨106061687997665024121551417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282831167993773397657470445 106061687997665024121551417)
        ·
          refine ⟨79546265998248768091163563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106061687997665024121551417 79546265998248768091163563)
          ·
            refine ⟨119319398997373152136745345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79546265998248768091163563 119319398997373152136745345)
            ·
              refine ⟨89489549248029864102559009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119319398997373152136745345 89489549248029864102559009)
              ·
                refine ⟨67117161936022398076919257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89489549248029864102559009 67117161936022398076919257)
                ·
                  refine ⟨50337871452016798557689443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67117161936022398076919257 50337871452016798557689443)
                  ·
                    refine ⟨75506807178025197836534165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50337871452016798557689443 75506807178025197836534165)
                    ·
                      refine ⟨3539381586469931148587539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75506807178025197836534165 3539381586469931148587539)
                      ·
                        rfl

theorem cell23_6892921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_6892921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892921 prefixEnd_6892921 := by exact prefixLift 6892921
  have htrace : WordTrace (prefixWord ++ tailWord_6892921) baseStart_6892921 baseEnd_6892921 := by
    simpa [prefixWord, tailWord_6892921, baseEnd_6892921] using wordTrace_append hprefix tailTrace_6892921
  have hstable : (prefixWord ++ tailWord_6892921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892921).length < 2 ^ (prefixWord ++ tailWord_6892921).sum := by decide
  have hdescent : baseEnd_6892921 < baseStart_6892921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892942 : List Nat := [4, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4]
def baseStart_6892942 : Nat := 118140960795 + 6892942 * 2 ^ 59
def prefixEnd_6892942 : Nat := 4983230072969 + 3 ^ 40 * 6892942 * 2
def baseEnd_6892942 : Nat := 3539392369563675566424943

theorem tailTrace_6892942 : CollatzResearch.WordTrace tailWord_6892942 prefixEnd_6892942 3539392369563675566424943 := by
  unfold tailWord_6892942
  simp only [CollatzResearch.WordTrace]
  refine ⟨31425781074256978701922135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167604165729370553076918053 31425781074256978701922135)
  ·
    refine ⟨47138671611385468052883203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31425781074256978701922135 47138671611385468052883203)
    ·
      refine ⟨70708007417078202079324805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47138671611385468052883203 70708007417078202079324805)
      ·
        refine ⟨13257751390702162889873401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70708007417078202079324805 13257751390702162889873401)
        ·
          refine ⟨9943313543026622167405051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13257751390702162889873401 9943313543026622167405051)
          ·
            refine ⟨14914970314539933251107577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9943313543026622167405051 14914970314539933251107577)
            ·
              refine ⟨11186227735904949938330683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14914970314539933251107577 11186227735904949938330683)
              ·
                refine ⟨16779341603857424907496025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11186227735904949938330683 16779341603857424907496025)
                ·
                  refine ⟨12584506202893068680622019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16779341603857424907496025 12584506202893068680622019)
                  ·
                    refine ⟨18876759304339603020933029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12584506202893068680622019 18876759304339603020933029)
                    ·
                      refine ⟨3539392369563675566424943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18876759304339603020933029 3539392369563675566424943)
                      ·
                        rfl

theorem cell23_6892942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_6892942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892942 prefixEnd_6892942 := by exact prefixLift 6892942
  have htrace : WordTrace (prefixWord ++ tailWord_6892942) baseStart_6892942 baseEnd_6892942 := by
    simpa [prefixWord, tailWord_6892942, baseEnd_6892942] using wordTrace_append hprefix tailTrace_6892942
  have hstable : (prefixWord ++ tailWord_6892942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892942).length < 2 ^ (prefixWord ++ tailWord_6892942).sum := by decide
  have hdescent : baseEnd_6892942 < baseStart_6892942 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6892951 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 8]
def baseStart_6892951 : Nat := 118140960795 + 6892951 * 2 ^ 59
def prefixEnd_6892951 : Nat := 4983230072969 + 3 ^ 40 * 6892951 * 2
def baseEnd_6892951 : Nat := 3539396990889566031212401

theorem tailTrace_6892951 : CollatzResearch.WordTrace tailWord_6892951 prefixEnd_6892951 3539396990889566031212401 := by
  unfold tailWord_6892951
  simp only [CollatzResearch.WordTrace]
  refine ⟨251406576851023224152454707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167604384567348816101636471 251406576851023224152454707)
  ·
    refine ⟨377109865276534836228682061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251406576851023224152454707 377109865276534836228682061)
    ·
      refine ⟨141416199478700563585755773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377109865276534836228682061 141416199478700563585755773)
      ·
        refine ⟨53031074804512711344658415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141416199478700563585755773 53031074804512711344658415)
        ·
          refine ⟨79546612206769067016987623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53031074804512711344658415 79546612206769067016987623)
          ·
            refine ⟨119319918310153600525481435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79546612206769067016987623 119319918310153600525481435)
            ·
              refine ⟨178979877465230400788222153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119319918310153600525481435 178979877465230400788222153)
              ·
                refine ⟨134234908098922800591166615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178979877465230400788222153 134234908098922800591166615)
                ·
                  refine ⟨201352362148384200886749923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134234908098922800591166615 201352362148384200886749923)
                  ·
                    refine ⟨302028543222576301330124885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 201352362148384200886749923 302028543222576301330124885)
                    ·
                      refine ⟨3539396990889566031212401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 302028543222576301330124885 3539396990889566031212401)
                      ·
                        rfl

theorem cell23_6892951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_6892951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6892951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6892951 prefixEnd_6892951 := by exact prefixLift 6892951
  have htrace : WordTrace (prefixWord ++ tailWord_6892951) baseStart_6892951 baseEnd_6892951 := by
    simpa [prefixWord, tailWord_6892951, baseEnd_6892951] using wordTrace_append hprefix tailTrace_6892951
  have hstable : (prefixWord ++ tailWord_6892951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6892951).length < 2 ^ (prefixWord ++ tailWord_6892951).sum := by decide
  have hdescent : baseEnd_6892951 < baseStart_6892951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6892951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893002 : List Nat := [3, 1, 2, 1, 2, 3, 3, 1, 2, 3, 2]
def baseStart_6893002 : Nat := 118140960795 + 6893002 * 2 ^ 59
def prefixEnd_6893002 : Nat := 4983230072969 + 3 ^ 40 * 6893002 * 2
def baseEnd_6893002 : Nat := 3539423178402945331674667

theorem tailTrace_6893002 : CollatzResearch.WordTrace tailWord_6893002 prefixEnd_6893002 3539423178402945331674667 := by
  unfold tailWord_6893002
  simp only [CollatzResearch.WordTrace]
  refine ⟨62852109243459614965640315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167605624649225639908374173 62852109243459614965640315)
  ·
    refine ⟨94278163865189422448460473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62852109243459614965640315 94278163865189422448460473)
    ·
      refine ⟨70708622898892066836345355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94278163865189422448460473 70708622898892066836345355)
      ·
        refine ⟨106062934348338100254518033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70708622898892066836345355 106062934348338100254518033)
        ·
          refine ⟨79547200761253575190888525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106062934348338100254518033 79547200761253575190888525)
          ·
            refine ⟨29830200285470090696583197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79547200761253575190888525 29830200285470090696583197)
            ·
              refine ⟨11186325107051284011218699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29830200285470090696583197 11186325107051284011218699)
              ·
                refine ⟨16779487660576926016828049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11186325107051284011218699 16779487660576926016828049)
                ·
                  refine ⟨12584615745432694512621037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16779487660576926016828049 12584615745432694512621037)
                  ·
                    refine ⟨4719230904537260442232889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12584615745432694512621037 4719230904537260442232889)
                    ·
                      refine ⟨3539423178402945331674667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4719230904537260442232889 3539423178402945331674667)
                      ·
                        rfl

theorem cell23_6893002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 2, 3, 2].length) (baseStart_6893002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893002 prefixEnd_6893002 := by exact prefixLift 6893002
  have htrace : WordTrace (prefixWord ++ tailWord_6893002) baseStart_6893002 baseEnd_6893002 := by
    simpa [prefixWord, tailWord_6893002, baseEnd_6893002] using wordTrace_append hprefix tailTrace_6893002
  have hstable : (prefixWord ++ tailWord_6893002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893002).length < 2 ^ (prefixWord ++ tailWord_6893002).sum := by decide
  have hdescent : baseEnd_6893002 < baseStart_6893002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893008 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 6, 4]
def baseStart_6893008 : Nat := 118140960795 + 6893008 * 2 ^ 59
def prefixEnd_6893008 : Nat := 4983230072969 + 3 ^ 40 * 6893008 * 2
def baseEnd_6893008 : Nat := 1179808753095624102733213

theorem tailTrace_6893008 : CollatzResearch.WordTrace tailWord_6893008 prefixEnd_6893008 1179808753095624102733213 := by
  unfold tailWord_6893008
  simp only [CollatzResearch.WordTrace]
  refine ⟨125704327905908361443639839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167605770541211148591519785 125704327905908361443639839)
  ·
    refine ⟨188556491858862542165459759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125704327905908361443639839 188556491858862542165459759)
    ·
      refine ⟨282834737788293813248189639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188556491858862542165459759 282834737788293813248189639)
      ·
        refine ⟨424252106682440719872284459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282834737788293813248189639 424252106682440719872284459)
        ·
          refine ⟨636378160023661079808426689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424252106682440719872284459 636378160023661079808426689)
          ·
            refine ⟨477283620017745809856320017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 636378160023661079808426689 477283620017745809856320017)
            ·
              refine ⟨357962715013309357392240013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 477283620017745809856320017 357962715013309357392240013)
              ·
                refine ⟨134236018129991009022090005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 357962715013309357392240013 134236018129991009022090005)
                ·
                  refine ⟨6292313349843328547910469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 134236018129991009022090005 6292313349843328547910469)
                  ·
                    refine ⟨1179808753095624102733213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6292313349843328547910469 1179808753095624102733213)
                    ·
                      rfl

theorem cell23_6893008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 6, 4].length) (baseStart_6893008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893008 prefixEnd_6893008 := by exact prefixLift 6893008
  have htrace : WordTrace (prefixWord ++ tailWord_6893008) baseStart_6893008 baseEnd_6893008 := by
    simpa [prefixWord, tailWord_6893008, baseEnd_6893008] using wordTrace_append hprefix tailTrace_6893008
  have hstable : (prefixWord ++ tailWord_6893008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893008).length < 2 ^ (prefixWord ++ tailWord_6893008).sum := by decide
  have hdescent : baseEnd_6893008 < baseStart_6893008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893012 : List Nat := [2, 4, 1, 2, 3, 1, 1, 3, 1, 5]
def baseStart_6893012 : Nat := 118140960795 + 6893012 * 2 ^ 59
def prefixEnd_6893012 : Nat := 4983230072969 + 3 ^ 40 * 6893012 * 2
def baseEnd_6893012 : Nat := 1179809437736496764183207

theorem tailTrace_6893012 : CollatzResearch.WordTrace tailWord_6893012 prefixEnd_6893012 1179809437736496764183207 := by
  unfold tailWord_6893012
  simp only [CollatzResearch.WordTrace]
  refine ⟨125704400851901115785212645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167605867802534821046950193 125704400851901115785212645)
  ·
    refine ⟨23569575159731459209727371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125704400851901115785212645 23569575159731459209727371)
    ·
      refine ⟨35354362739597188814591057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23569575159731459209727371 35354362739597188814591057)
      ·
        refine ⟨26515772054697891610943293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35354362739597188814591057 26515772054697891610943293)
        ·
          refine ⟨9943414520511709354103735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26515772054697891610943293 9943414520511709354103735)
          ·
            refine ⟨14915121780767564031155603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9943414520511709354103735 14915121780767564031155603)
            ·
              refine ⟨22372682671151346046733405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14915121780767564031155603 22372682671151346046733405)
              ·
                refine ⟨8389756001681754767525027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22372682671151346046733405 8389756001681754767525027)
                ·
                  refine ⟨12584634002522632151287541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8389756001681754767525027 12584634002522632151287541)
                  ·
                    refine ⟨1179809437736496764183207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12584634002522632151287541 1179809437736496764183207)
                    ·
                      rfl

theorem cell23_6893012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_6893012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893012 prefixEnd_6893012 := by exact prefixLift 6893012
  have htrace : WordTrace (prefixWord ++ tailWord_6893012) baseStart_6893012 baseEnd_6893012 := by
    simpa [prefixWord, tailWord_6893012, baseEnd_6893012] using wordTrace_append hprefix tailTrace_6893012
  have hstable : (prefixWord ++ tailWord_6893012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893012).length < 2 ^ (prefixWord ++ tailWord_6893012).sum := by decide
  have hdescent : baseEnd_6893012 < baseStart_6893012 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893025 : List Nat := [1, 2, 3, 1, 2, 4, 1, 1, 4, 4]
def baseStart_6893025 : Nat := 118140960795 + 6893025 * 2 ^ 59
def prefixEnd_6893025 : Nat := 4983230072969 + 3 ^ 40 * 6893025 * 2
def baseEnd_6893025 : Nat := 1179811662819332913895687

theorem tailTrace_6893025 : CollatzResearch.WordTrace tailWord_6893025 prefixEnd_6893025 1179811662819332913895687 := by
  unfold tailWord_6893025
  simp only [CollatzResearch.WordTrace]
  refine ⟨251409275852755134790648529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167606183901836756527099019 251409275852755134790648529)
  ·
    refine ⟨188556956889566351092986397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251409275852755134790648529 188556956889566351092986397)
    ·
      refine ⟨70708858833587381659869899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188556956889566351092986397 70708858833587381659869899)
      ·
        refine ⟨106063288250381072489804849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70708858833587381659869899 106063288250381072489804849)
        ·
          refine ⟨79547466187785804367353637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106063288250381072489804849 79547466187785804367353637)
          ·
            refine ⟨14915149910209838318878807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79547466187785804367353637 14915149910209838318878807)
            ·
              refine ⟨22372724865314757478318211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14915149910209838318878807 22372724865314757478318211)
              ·
                refine ⟨33559087297972136217477317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22372724865314757478318211 33559087297972136217477317)
                ·
                  refine ⟨6292328868369775540776997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33559087297972136217477317 6292328868369775540776997)
                  ·
                    refine ⟨1179811662819332913895687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6292328868369775540776997 1179811662819332913895687)
                    ·
                      rfl

theorem cell23_6893025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 4, 4].length) (baseStart_6893025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893025 prefixEnd_6893025 := by exact prefixLift 6893025
  have htrace : WordTrace (prefixWord ++ tailWord_6893025) baseStart_6893025 baseEnd_6893025 := by
    simpa [prefixWord, tailWord_6893025, baseEnd_6893025] using wordTrace_append hprefix tailTrace_6893025
  have hstable : (prefixWord ++ tailWord_6893025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893025).length < 2 ^ (prefixWord ++ tailWord_6893025).sum := by decide
  have hdescent : baseEnd_6893025 < baseStart_6893025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893028 : List Nat := [2, 3, 1, 1, 1, 1, 1, 4, 3, 2, 4]
def baseStart_6893028 : Nat := 118140960795 + 6893028 * 2 ^ 59
def prefixEnd_6893028 : Nat := 4983230072969 + 3 ^ 40 * 6893028 * 2
def baseEnd_6893028 : Nat := 3539436528899962229949547

theorem tailTrace_6893028 : CollatzResearch.WordTrace tailWord_6893028 prefixEnd_6893028 3539436528899962229949547 := by
  unfold tailWord_6893028
  simp only [CollatzResearch.WordTrace]
  refine ⟨125704692635872133151503869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167606256847829510868671825 125704692635872133151503869)
  ·
    refine ⟨47139259738452049931813951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125704692635872133151503869 47139259738452049931813951)
    ·
      refine ⟨70708889607678074897720927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47139259738452049931813951 70708889607678074897720927)
      ·
        refine ⟨106063334411517112346581391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70708889607678074897720927 106063334411517112346581391)
        ·
          refine ⟨159095001617275668519872087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106063334411517112346581391 159095001617275668519872087)
          ·
            refine ⟨238642502425913502779808131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159095001617275668519872087 238642502425913502779808131)
            ·
              refine ⟨357963753638870254169712197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238642502425913502779808131 357963753638870254169712197)
              ·
                refine ⟨67118203807288172656821037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 357963753638870254169712197 67118203807288172656821037)
                ·
                  refine ⟨25169326427733064746307889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67118203807288172656821037 25169326427733064746307889)
                  ·
                    refine ⟨18876994820799798559730917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25169326427733064746307889 18876994820799798559730917)
                    ·
                      refine ⟨3539436528899962229949547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18876994820799798559730917 3539436528899962229949547)
                      ·
                        rfl

theorem cell23_6893028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_6893028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893028 prefixEnd_6893028 := by exact prefixLift 6893028
  have htrace : WordTrace (prefixWord ++ tailWord_6893028) baseStart_6893028 baseEnd_6893028 := by
    simpa [prefixWord, tailWord_6893028, baseEnd_6893028] using wordTrace_append hprefix tailTrace_6893028
  have hstable : (prefixWord ++ tailWord_6893028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893028).length < 2 ^ (prefixWord ++ tailWord_6893028).sum := by decide
  have hdescent : baseEnd_6893028 < baseStart_6893028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893038 : List Nat := [4, 1, 2, 1, 2, 1, 2, 10]
def baseStart_6893038 : Nat := 118140960795 + 6893038 * 2 ^ 59
def prefixEnd_6893038 : Nat := 4983230072969 + 3 ^ 40 * 6893038 * 2
def baseEnd_6893038 : Nat := 131090431989129895956463

theorem tailTrace_6893038 : CollatzResearch.WordTrace tailWord_6893038 prefixEnd_6893038 131090431989129895956463 := by
  unfold tailWord_6893038
  simp only [CollatzResearch.WordTrace]
  refine ⟨31426218750213504751358971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167606500001138692007247845 31426218750213504751358971)
  ·
    refine ⟨47139328125320257127038457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31426218750213504751358971 47139328125320257127038457)
    ·
      refine ⟨35354496093990192845278843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47139328125320257127038457 35354496093990192845278843)
      ·
        refine ⟨53031744140985289267918265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35354496093990192845278843 53031744140985289267918265)
        ·
          refine ⟨39773808105738966950938699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53031744140985289267918265 39773808105738966950938699)
          ·
            refine ⟨59660712158608450426408049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39773808105738966950938699 59660712158608450426408049)
            ·
              refine ⟨44745534118956337819806037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59660712158608450426408049 44745534118956337819806037)
              ·
                refine ⟨131090431989129895956463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 44745534118956337819806037 131090431989129895956463)
                ·
                  rfl

theorem cell23_6893038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 10].length) (baseStart_6893038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893038 prefixEnd_6893038 := by exact prefixLift 6893038
  have htrace : WordTrace (prefixWord ++ tailWord_6893038) baseStart_6893038 baseEnd_6893038 := by
    simpa [prefixWord, tailWord_6893038, baseEnd_6893038] using wordTrace_append hprefix tailTrace_6893038
  have hstable : (prefixWord ++ tailWord_6893038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893038).length < 2 ^ (prefixWord ++ tailWord_6893038).sum := by decide
  have hdescent : baseEnd_6893038 < baseStart_6893038 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893042 : List Nat := [3, 2, 1, 4, 1, 3, 1, 1, 1, 6]
def baseStart_6893042 : Nat := 118140960795 + 6893042 * 2 ^ 59
def prefixEnd_6893042 : Nat := 4983230072969 + 3 ^ 40 * 6893042 * 2
def baseEnd_6893042 : Nat := 1179814572543041725058161

theorem tailTrace_6893042 : CollatzResearch.WordTrace tailWord_6893042 prefixEnd_6893042 1179814572543041725058161 := by
  unfold tailWord_6893042
  simp only [CollatzResearch.WordTrace]
  refine ⟨62852473973423386673504345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167606597262462364462678253 62852473973423386673504345)
  ·
    refine ⟨47139355480067540005128259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62852473973423386673504345 47139355480067540005128259)
    ·
      refine ⟨70709033220101310007692389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47139355480067540005128259 70709033220101310007692389)
      ·
        refine ⟨13257943728768995626442323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70709033220101310007692389 13257943728768995626442323)
        ·
          refine ⟨19886915593153493439663485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13257943728768995626442323 19886915593153493439663485)
          ·
            refine ⟨7457593347432560039873807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19886915593153493439663485 7457593347432560039873807)
            ·
              refine ⟨11186390021148840059810711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7457593347432560039873807 11186390021148840059810711)
              ·
                refine ⟨16779585031723260089716067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11186390021148840059810711 16779585031723260089716067)
                ·
                  refine ⟨25169377547584890134574101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16779585031723260089716067 25169377547584890134574101)
                  ·
                    refine ⟨1179814572543041725058161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25169377547584890134574101 1179814572543041725058161)
                    ·
                      rfl

theorem cell23_6893042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 1, 6].length) (baseStart_6893042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893042 prefixEnd_6893042 := by exact prefixLift 6893042
  have htrace : WordTrace (prefixWord ++ tailWord_6893042) baseStart_6893042 baseEnd_6893042 := by
    simpa [prefixWord, tailWord_6893042, baseEnd_6893042] using wordTrace_append hprefix tailTrace_6893042
  have hstable : (prefixWord ++ tailWord_6893042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893042).length < 2 ^ (prefixWord ++ tailWord_6893042).sum := by decide
  have hdescent : baseEnd_6893042 < baseStart_6893042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893065 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 6, 1, 3]
def baseStart_6893065 : Nat := 118140960795 + 6893065 * 2 ^ 59
def prefixEnd_6893065 : Nat := 4983230072969 + 3 ^ 40 * 6893065 * 2
def baseEnd_6893065 : Nat := 3539455527684178585186877

theorem tailTrace_6893065 : CollatzResearch.WordTrace tailWord_6893065 prefixEnd_6893065 3539455527684178585186877 := by
  unfold tailWord_6893065
  simp only [CollatzResearch.WordTrace]
  refine ⟨251410734772610221622104649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167607156515073481081403099 251410734772610221622104649)
  ·
    refine ⟨188558051079457666216578487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251410734772610221622104649 188558051079457666216578487)
    ·
      refine ⟨282837076619186499324867731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188558051079457666216578487 282837076619186499324867731)
      ·
        refine ⟨424255614928779748987301597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282837076619186499324867731 424255614928779748987301597)
        ·
          refine ⟨159095855598292405870238099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 424255614928779748987301597 159095855598292405870238099)
          ·
            refine ⟨238643783397438608805357149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159095855598292405870238099 238643783397438608805357149)
            ·
              refine ⟨89491418774039478302008931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 238643783397438608805357149 89491418774039478302008931)
              ·
                refine ⟨134237128161059217453013397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89491418774039478302008931 134237128161059217453013397)
                ·
                  refine ⟨6292365382549650818110003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 134237128161059217453013397 6292365382549650818110003)
                  ·
                    refine ⟨9438548073824476227165005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6292365382549650818110003 9438548073824476227165005)
                    ·
                      refine ⟨3539455527684178585186877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9438548073824476227165005 3539455527684178585186877)
                      ·
                        rfl

theorem cell23_6893065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 6, 1, 3].length) (baseStart_6893065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893065 prefixEnd_6893065 := by exact prefixLift 6893065
  have htrace : WordTrace (prefixWord ++ tailWord_6893065) baseStart_6893065 baseEnd_6893065 := by
    simpa [prefixWord, tailWord_6893065, baseEnd_6893065] using wordTrace_append hprefix tailTrace_6893065
  have hstable : (prefixWord ++ tailWord_6893065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893065).length < 2 ^ (prefixWord ++ tailWord_6893065).sum := by decide
  have hdescent : baseEnd_6893065 < baseStart_6893065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893066 : List Nat := [3, 1, 2, 2, 2, 2, 3, 3, 1, 2, 2]
def baseStart_6893066 : Nat := 118140960795 + 6893066 * 2 ^ 59
def prefixEnd_6893066 : Nat := 4983230072969 + 3 ^ 40 * 6893066 * 2
def baseEnd_6893066 : Nat := 3539456041164833081274373

theorem tailTrace_6893066 : CollatzResearch.WordTrace tailWord_6893066 prefixEnd_6893066 3539456041164833081274373 := by
  unfold tailWord_6893066
  simp only [CollatzResearch.WordTrace]
  refine ⟨62852692811401649698222763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167607180830404399195260701 62852692811401649698222763)
  ·
    refine ⟨94279039217102474547334145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62852692811401649698222763 94279039217102474547334145)
    ·
      refine ⟨70709279412826855910500609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94279039217102474547334145 70709279412826855910500609)
      ·
        refine ⟨53031959559620141932875457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70709279412826855910500609 53031959559620141932875457)
        ·
          refine ⟨39773969669715106449656593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53031959559620141932875457 39773969669715106449656593)
          ·
            refine ⟨29830477252286329837242445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39773969669715106449656593 29830477252286329837242445)
            ·
              refine ⟨11186428969607373688965917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29830477252286329837242445 11186428969607373688965917)
              ·
                refine ⟨4194910863602765133362219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11186428969607373688965917 4194910863602765133362219)
                ·
                  refine ⟨6292366295404147700043329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4194910863602765133362219 6292366295404147700043329)
                  ·
                    refine ⟨4719274721553110775032497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6292366295404147700043329 4719274721553110775032497)
                    ·
                      refine ⟨3539456041164833081274373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4719274721553110775032497 3539456041164833081274373)
                      ·
                        rfl

theorem cell23_6893066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 3, 1, 2, 2].length) (baseStart_6893066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893066 prefixEnd_6893066 := by exact prefixLift 6893066
  have htrace : WordTrace (prefixWord ++ tailWord_6893066) baseStart_6893066 baseEnd_6893066 := by
    simpa [prefixWord, tailWord_6893066, baseEnd_6893066] using wordTrace_append hprefix tailTrace_6893066
  have hstable : (prefixWord ++ tailWord_6893066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893066).length < 2 ^ (prefixWord ++ tailWord_6893066).sum := by decide
  have hdescent : baseEnd_6893066 < baseStart_6893066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893082 : List Nat := [3, 1, 1, 3, 1, 1, 1, 6, 2, 1, 3]
def baseStart_6893082 : Nat := 118140960795 + 6893082 * 2 ^ 59
def prefixEnd_6893082 : Nat := 4983230072969 + 3 ^ 40 * 6893082 * 2
def baseEnd_6893082 : Nat := 3539464256855305018674299

theorem tailTrace_6893082 : CollatzResearch.WordTrace tailWord_6893082 prefixEnd_6893082 3539464256855305018674299 := by
  unfold tailWord_6893082
  simp only [CollatzResearch.WordTrace]
  refine ⟨62852838703387158381368375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167607569875699089016982333 62852838703387158381368375)
  ·
    refine ⟨94279258055080737572052563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62852838703387158381368375 94279258055080737572052563)
    ·
      refine ⟨141418887082621106358078845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94279258055080737572052563 141418887082621106358078845)
      ·
        refine ⟨53032082655982914884279567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141418887082621106358078845 53032082655982914884279567)
        ·
          refine ⟨79548123983974372326419351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53032082655982914884279567 79548123983974372326419351)
          ·
            refine ⟨119322185975961558489629027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79548123983974372326419351 119322185975961558489629027)
            ·
              refine ⟨178983278963942337734443541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119322185975961558489629027 178983278963942337734443541)
              ·
                refine ⟨8389841201434797081302041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 178983278963942337734443541 8389841201434797081302041)
                ·
                  refine ⟨6292380901076097810976531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8389841201434797081302041 6292380901076097810976531)
                  ·
                    refine ⟨9438571351614146716464797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6292380901076097810976531 9438571351614146716464797)
                    ·
                      refine ⟨3539464256855305018674299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9438571351614146716464797 3539464256855305018674299)
                      ·
                        rfl

theorem cell23_6893082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_6893082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893082 prefixEnd_6893082 := by exact prefixLift 6893082
  have htrace : WordTrace (prefixWord ++ tailWord_6893082) baseStart_6893082 baseEnd_6893082 := by
    simpa [prefixWord, tailWord_6893082, baseEnd_6893082] using wordTrace_append hprefix tailTrace_6893082
  have hstable : (prefixWord ++ tailWord_6893082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893082).length < 2 ^ (prefixWord ++ tailWord_6893082).sum := by decide
  have hdescent : baseEnd_6893082 < baseStart_6893082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893109 : List Nat := [1, 3, 3, 1, 1, 3, 3, 2, 1, 3, 2]
def baseStart_6893109 : Nat := 118140960795 + 6893109 * 2 ^ 59
def prefixEnd_6893109 : Nat := 4983230072969 + 3 ^ 40 * 6893109 * 2
def baseEnd_6893109 : Nat := 3539478120832976413036675

theorem tailTrace_6893109 : CollatzResearch.WordTrace tailWord_6893109 prefixEnd_6893109 3539478120832976413036675 := by
  unfold tailWord_6893109
  simp only [CollatzResearch.WordTrace]
  refine ⟨251412339584450817136706381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167608226389633878091137587 251412339584450817136706381)
  ·
    refine ⟨94279627344169056426264893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251412339584450817136706381 94279627344169056426264893)
    ·
      refine ⟨35354860254063396159849335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94279627344169056426264893 35354860254063396159849335)
      ·
        refine ⟨53032290381095094239774003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35354860254063396159849335 53032290381095094239774003)
        ·
          refine ⟨79548435571642641359661005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53032290381095094239774003 79548435571642641359661005)
          ·
            refine ⟨29830663339365990509872877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79548435571642641359661005 29830663339365990509872877)
            ·
              refine ⟨11186498752262246441202329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29830663339365990509872877 11186498752262246441202329)
              ·
                refine ⟨8389874064196684830901747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11186498752262246441202329 8389874064196684830901747)
                ·
                  refine ⟨12584811096295027246352621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8389874064196684830901747 12584811096295027246352621)
                  ·
                    refine ⟨4719304161110635217382233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12584811096295027246352621 4719304161110635217382233)
                    ·
                      refine ⟨3539478120832976413036675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4719304161110635217382233 3539478120832976413036675)
                      ·
                        rfl

theorem cell23_6893109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 1, 3, 2].length) (baseStart_6893109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893109 prefixEnd_6893109 := by exact prefixLift 6893109
  have htrace : WordTrace (prefixWord ++ tailWord_6893109) baseStart_6893109 baseEnd_6893109 := by
    simpa [prefixWord, tailWord_6893109, baseEnd_6893109] using wordTrace_append hprefix tailTrace_6893109
  have hstable : (prefixWord ++ tailWord_6893109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893109).length < 2 ^ (prefixWord ++ tailWord_6893109).sum := by decide
  have hdescent : baseEnd_6893109 < baseStart_6893109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893149 : List Nat := [1, 4, 4, 2, 1, 1, 1, 1, 2, 6]
def baseStart_6893149 : Nat := 118140960795 + 6893149 * 2 ^ 59
def prefixEnd_6893149 : Nat := 4983230072969 + 3 ^ 40 * 6893149 * 2
def baseEnd_6893149 : Nat := 1179832886686385418845497

theorem tailTrace_6893149 : CollatzResearch.WordTrace tailWord_6893149 prefixEnd_6893149 1179832886686385418845497 := by
  unfold tailWord_6893149
  simp only [CollatzResearch.WordTrace]
  refine ⟨251413798504305903968162501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167609199002870602645441667 251413798504305903968162501)
  ·
    refine ⟨47140087219557356994030469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 251413798504305903968162501 47140087219557356994030469)
    ·
      refine ⟨8838766353667004436380713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47140087219557356994030469 8838766353667004436380713)
      ·
        refine ⟨6629074765250253327285535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8838766353667004436380713 6629074765250253327285535)
        ·
          refine ⟨9943612147875379990928303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6629074765250253327285535 9943612147875379990928303)
          ·
            refine ⟨14915418221813069986392455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9943612147875379990928303 14915418221813069986392455)
            ·
              refine ⟨22373127332719604979588683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14915418221813069986392455 22373127332719604979588683)
              ·
                refine ⟨33559690999079407469383025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22373127332719604979588683 33559690999079407469383025)
                ·
                  refine ⟨25169768249309555602037269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33559690999079407469383025 25169768249309555602037269)
                  ·
                    refine ⟨1179832886686385418845497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25169768249309555602037269 1179832886686385418845497)
                    ·
                      rfl

theorem cell23_6893149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_6893149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893149 prefixEnd_6893149 := by exact prefixLift 6893149
  have htrace : WordTrace (prefixWord ++ tailWord_6893149) baseStart_6893149 baseEnd_6893149 := by
    simpa [prefixWord, tailWord_6893149, baseEnd_6893149] using wordTrace_append hprefix tailTrace_6893149
  have hstable : (prefixWord ++ tailWord_6893149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893149).length < 2 ^ (prefixWord ++ tailWord_6893149).sum := by decide
  have hdescent : baseEnd_6893149 < baseStart_6893149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893155 : List Nat := [1, 1, 1, 5, 1, 3, 1, 1, 1, 5, 3]
def baseStart_6893155 : Nat := 118140960795 + 6893155 * 2 ^ 59
def prefixEnd_6893155 : Nat := 4983230072969 + 3 ^ 40 * 6893155 * 2
def baseEnd_6893155 : Nat := 3539501740943083233061463

theorem tailTrace_6893155 : CollatzResearch.WordTrace tailWord_6893155 prefixEnd_6893155 3539501740943083233061463 := by
  unfold tailWord_6893155
  simp only [CollatzResearch.WordTrace]
  refine ⟨251414017342284166992880919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167609344894856111328587279 251414017342284166992880919)
  ·
    refine ⟨377121026013426250489321379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251414017342284166992880919 377121026013426250489321379)
    ·
      refine ⟨565681539020139375733982069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377121026013426250489321379 565681539020139375733982069)
      ·
        refine ⟨53032644283138066475060819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 565681539020139375733982069 53032644283138066475060819)
        ·
          refine ⟨79548966424707099712591229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53032644283138066475060819 79548966424707099712591229)
          ·
            refine ⟨29830862409265162392221711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79548966424707099712591229 29830862409265162392221711)
            ·
              refine ⟨44746293613897743588332567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29830862409265162392221711 44746293613897743588332567)
              ·
                refine ⟨67119440420846615382498851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44746293613897743588332567 67119440420846615382498851)
                ·
                  refine ⟨100679160631269923073748277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67119440420846615382498851 100679160631269923073748277)
                  ·
                    refine ⟨9438671309181555288163901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 100679160631269923073748277 9438671309181555288163901)
                    ·
                      refine ⟨3539501740943083233061463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9438671309181555288163901 3539501740943083233061463)
                      ·
                        rfl

theorem cell23_6893155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_6893155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893155 prefixEnd_6893155 := by exact prefixLift 6893155
  have htrace : WordTrace (prefixWord ++ tailWord_6893155) baseStart_6893155 baseEnd_6893155 := by
    simpa [prefixWord, tailWord_6893155, baseEnd_6893155] using wordTrace_append hprefix tailTrace_6893155
  have hstable : (prefixWord ++ tailWord_6893155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893155).length < 2 ^ (prefixWord ++ tailWord_6893155).sum := by decide
  have hdescent : baseEnd_6893155 < baseStart_6893155 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893195 : List Nat := [1, 1, 1, 1, 4, 1, 4, 1, 4, 1, 4]
def baseStart_6893195 : Nat := 118140960795 + 6893195 * 2 ^ 59
def prefixEnd_6893195 : Nat := 4983230072969 + 3 ^ 40 * 6893195 * 2
def baseEnd_6893195 : Nat := 3539522280169263076561279

theorem tailTrace_6893195 : CollatzResearch.WordTrace tailWord_6893195 prefixEnd_6893195 3539522280169263076561279 := by
  unfold tailWord_6893195
  simp only [CollatzResearch.WordTrace]
  refine ⟨251415476262139253824337039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167610317508092835882891359 251415476262139253824337039)
  ·
    refine ⟨377123214393208880736505559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251415476262139253824337039 377123214393208880736505559)
    ·
      refine ⟨565684821589813321104758339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377123214393208880736505559 565684821589813321104758339)
      ·
        refine ⟨848527232384719981657137509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565684821589813321104758339 848527232384719981657137509)
        ·
          refine ⟨159098856072134996560713283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 848527232384719981657137509 159098856072134996560713283)
          ·
            refine ⟨238648284108202494841069925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159098856072134996560713283 238648284108202494841069925)
            ·
              refine ⟨44746553270287967782700611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 238648284108202494841069925 44746553270287967782700611)
              ·
                refine ⟨67119829905431951674050917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44746553270287967782700611 67119829905431951674050917)
                ·
                  refine ⟨12584968107268490938884547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67119829905431951674050917 12584968107268490938884547)
                  ·
                    refine ⟨18877452160902736408326821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12584968107268490938884547 18877452160902736408326821)
                    ·
                      refine ⟨3539522280169263076561279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18877452160902736408326821 3539522280169263076561279)
                      ·
                        rfl

theorem cell23_6893195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4, 1, 4].length) (baseStart_6893195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893195 prefixEnd_6893195 := by exact prefixLift 6893195
  have htrace : WordTrace (prefixWord ++ tailWord_6893195) baseStart_6893195 baseEnd_6893195 := by
    simpa [prefixWord, tailWord_6893195, baseEnd_6893195] using wordTrace_append hprefix tailTrace_6893195
  have hstable : (prefixWord ++ tailWord_6893195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893195).length < 2 ^ (prefixWord ++ tailWord_6893195).sum := by decide
  have hdescent : baseEnd_6893195 < baseStart_6893195 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893252 : List Nat := [2, 3, 3, 1, 1, 1, 2, 4, 6]
def baseStart_6893252 : Nat := 118140960795 + 6893252 * 2 ^ 59
def prefixEnd_6893252 : Nat := 4983230072969 + 3 ^ 40 * 6893252 * 2
def baseEnd_6893252 : Nat := 393283505396285483727613

theorem tailTrace_6893252 : CollatzResearch.WordTrace tailWord_6893252 prefixEnd_6893252 393283505396285483727613 := by
  unfold tailWord_6893252
  simp only [CollatzResearch.WordTrace]
  refine ⟨125708777611466376279581005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167611703481955168372774673 125708777611466376279581005)
  ·
    refine ⟨47140791604299891104842877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125708777611466376279581005 47140791604299891104842877)
    ·
      refine ⟨17677796851612459164316079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47140791604299891104842877 17677796851612459164316079)
      ·
        refine ⟨26516695277418688746474119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17677796851612459164316079 26516695277418688746474119)
        ·
          refine ⟨39775042916128033119711179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26516695277418688746474119 39775042916128033119711179)
          ·
            refine ⟨59662564374192049679566769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39775042916128033119711179 59662564374192049679566769)
            ·
              refine ⟨44746923280644037259675077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59662564374192049679566769 44746923280644037259675077)
              ·
                refine ⟨8390048115120756986189077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44746923280644037259675077 8390048115120756986189077)
                ·
                  refine ⟨393283505396285483727613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8390048115120756986189077 393283505396285483727613)
                  ·
                    rfl

theorem cell23_6893252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4, 6].length) (baseStart_6893252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893252 prefixEnd_6893252 := by exact prefixLift 6893252
  have htrace : WordTrace (prefixWord ++ tailWord_6893252) baseStart_6893252 baseEnd_6893252 := by
    simpa [prefixWord, tailWord_6893252, baseEnd_6893252] using wordTrace_append hprefix tailTrace_6893252
  have hstable : (prefixWord ++ tailWord_6893252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893252).length < 2 ^ (prefixWord ++ tailWord_6893252).sum := by decide
  have hdescent : baseEnd_6893252 < baseStart_6893252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893256 : List Nat := [2, 1, 3, 1, 2, 2, 5, 2, 1, 4]
def baseStart_6893256 : Nat := 118140960795 + 6893256 * 2 ^ 59
def prefixEnd_6893256 : Nat := 4983230072969 + 3 ^ 40 * 6893256 * 2
def baseEnd_6893256 : Nat := 1179851200829729112632833

theorem tailTrace_6893256 : CollatzResearch.WordTrace tailWord_6893256 prefixEnd_6893256 1179851200829729112632833 := by
  unfold tailWord_6893256
  simp only [CollatzResearch.WordTrace]
  refine ⟨125708850557459130621153811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167611800743278840828205081 125708850557459130621153811)
  ·
    refine ⟨188563275836188695931730717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125708850557459130621153811 188563275836188695931730717)
    ·
      refine ⟨70711228438570760974399019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188563275836188695931730717 70711228438570760974399019)
      ·
        refine ⟨106066842657856141461598529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70711228438570760974399019 106066842657856141461598529)
        ·
          refine ⟨79550131993392106096198897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106066842657856141461598529 79550131993392106096198897)
          ·
            refine ⟨59662598995044079572149173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79550131993392106096198897 59662598995044079572149173)
            ·
              refine ⟨5593368655785382459888985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59662598995044079572149173 5593368655785382459888985)
              ·
                refine ⟨4195026491839036844916739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5593368655785382459888985 4195026491839036844916739)
                ·
                  refine ⟨6292539737758555267375109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4195026491839036844916739 6292539737758555267375109)
                  ·
                    refine ⟨1179851200829729112632833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6292539737758555267375109 1179851200829729112632833)
                    ·
                      rfl

theorem cell23_6893256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 2, 1, 4].length) (baseStart_6893256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893256 prefixEnd_6893256 := by exact prefixLift 6893256
  have htrace : WordTrace (prefixWord ++ tailWord_6893256) baseStart_6893256 baseEnd_6893256 := by
    simpa [prefixWord, tailWord_6893256, baseEnd_6893256] using wordTrace_append hprefix tailTrace_6893256
  have hstable : (prefixWord ++ tailWord_6893256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893256).length < 2 ^ (prefixWord ++ tailWord_6893256).sum := by decide
  have hdescent : baseEnd_6893256 < baseStart_6893256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893313 : List Nat := [1, 2, 4, 1, 1, 1, 6, 2, 1, 1, 3]
def baseStart_6893313 : Nat := 118140960795 + 6893313 * 2 ^ 59
def prefixEnd_6893313 : Nat := 4983230072969 + 3 ^ 40 * 6893313 * 2
def baseEnd_6893313 : Nat := 3539582870886493614885737

theorem tailTrace_6893313 : CollatzResearch.WordTrace tailWord_6893313 prefixEnd_6893313 3539582870886493614885737 := by
  unfold tailWord_6893313
  simp only [CollatzResearch.WordTrace]
  refine ⟨251419780075711759977132593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167613186717141173318088395 251419780075711759977132593)
  ·
    refine ⟨188564835056783819982849445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251419780075711759977132593 188564835056783819982849445)
    ·
      refine ⟨35355906573146966246784271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188564835056783819982849445 35355906573146966246784271)
      ·
        refine ⟨53033859859720449370176407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35355906573146966246784271 53033859859720449370176407)
        ·
          refine ⟨79550789789580674055264611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53033859859720449370176407 79550789789580674055264611)
          ·
            refine ⟨119326184684371011082896917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79550789789580674055264611 119326184684371011082896917)
            ·
              refine ⟨5593414907079891144510793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 119326184684371011082896917 5593414907079891144510793)
              ·
                refine ⟨4195061180309918358383095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5593414907079891144510793 4195061180309918358383095)
                ·
                  refine ⟨6292591770464877537574643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4195061180309918358383095 6292591770464877537574643)
                  ·
                    refine ⟨9438887655697316306361965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6292591770464877537574643 9438887655697316306361965)
                    ·
                      refine ⟨3539582870886493614885737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9438887655697316306361965 3539582870886493614885737)
                      ·
                        rfl

theorem cell23_6893313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 2, 1, 1, 3].length) (baseStart_6893313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893313 prefixEnd_6893313 := by exact prefixLift 6893313
  have htrace : WordTrace (prefixWord ++ tailWord_6893313) baseStart_6893313 baseEnd_6893313 := by
    simpa [prefixWord, tailWord_6893313, baseEnd_6893313] using wordTrace_append hprefix tailTrace_6893313
  have hstable : (prefixWord ++ tailWord_6893313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893313).length < 2 ^ (prefixWord ++ tailWord_6893313).sum := by decide
  have hdescent : baseEnd_6893313 < baseStart_6893313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893315 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 6]
def baseStart_6893315 : Nat := 118140960795 + 6893315 * 2 ^ 59
def prefixEnd_6893315 : Nat := 4983230072969 + 3 ^ 40 * 6893315 * 2
def baseEnd_6893315 : Nat := 3539583897847802607060727

theorem tailTrace_6893315 : CollatzResearch.WordTrace tailWord_6893315 prefixEnd_6893315 3539583897847802607060727 := by
  unfold tailWord_6893315
  simp only [CollatzResearch.WordTrace]
  refine ⟨251419853021704514318705399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167613235347803009545803599 251419853021704514318705399)
  ·
    refine ⟨377129779532556771478058099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251419853021704514318705399 377129779532556771478058099)
    ·
      refine ⟨565694669298835157217087149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377129779532556771478058099 565694669298835157217087149)
      ·
        refine ⟨212135500987063183956407681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 565694669298835157217087149 212135500987063183956407681)
        ·
          refine ⟨159101625740297387967305761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212135500987063183956407681 159101625740297387967305761)
          ·
            refine ⟨119326219305223040975479321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159101625740297387967305761 119326219305223040975479321)
            ·
              refine ⟨89494664478917280731609491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119326219305223040975479321 89494664478917280731609491)
              ·
                refine ⟨134241996718375921097414237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89494664478917280731609491 134241996718375921097414237)
                ·
                  refine ⟨50340748769390970411530339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134241996718375921097414237 50340748769390970411530339)
                  ·
                    refine ⟨75511123154086455617295509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50340748769390970411530339 75511123154086455617295509)
                    ·
                      refine ⟨3539583897847802607060727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75511123154086455617295509 3539583897847802607060727)
                      ·
                        rfl

theorem cell23_6893315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_6893315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893315 prefixEnd_6893315 := by exact prefixLift 6893315
  have htrace : WordTrace (prefixWord ++ tailWord_6893315) baseStart_6893315 baseEnd_6893315 := by
    simpa [prefixWord, tailWord_6893315, baseEnd_6893315] using wordTrace_append hprefix tailTrace_6893315
  have hstable : (prefixWord ++ tailWord_6893315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893315).length < 2 ^ (prefixWord ++ tailWord_6893315).sum := by decide
  have hdescent : baseEnd_6893315 < baseStart_6893315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893356 : List Nat := [2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 3]
def baseStart_6893356 : Nat := 118140960795 + 6893356 * 2 ^ 59
def prefixEnd_6893356 : Nat := 4983230072969 + 3 ^ 40 * 6893356 * 2
def baseEnd_6893356 : Nat := 3539604950554636946648039

theorem tailTrace_6893356 : CollatzResearch.WordTrace tailWord_6893356 prefixEnd_6893356 3539604950554636946648039 := by
  unfold tailWord_6893356
  simp only [CollatzResearch.WordTrace]
  refine ⟨125710674207277989160473961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167614232276370652213965281 125710674207277989160473961)
  ·
    refine ⟨94283005655458491870355471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125710674207277989160473961 94283005655458491870355471)
    ·
      refine ⟨141424508483187737805533207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94283005655458491870355471 141424508483187737805533207)
      ·
        refine ⟨212136762724781606708299811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141424508483187737805533207 212136762724781606708299811)
        ·
          refine ⟨318205144087172410062449717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212136762724781606708299811 318205144087172410062449717)
          ·
            refine ⟨29831732258172413443354661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 318205144087172410062449717 29831732258172413443354661)
            ·
              refine ⟨5593449798407327520628999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29831732258172413443354661 5593449798407327520628999)
              ·
                refine ⟨8390174697610991280943499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5593449798407327520628999 8390174697610991280943499)
                ·
                  refine ⟨12585262046416486921415249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8390174697610991280943499 12585262046416486921415249)
                  ·
                    refine ⟨9438946534812365191061437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12585262046416486921415249 9438946534812365191061437)
                    ·
                      refine ⟨3539604950554636946648039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9438946534812365191061437 3539604950554636946648039)
                      ·
                        rfl

theorem cell23_6893356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 3].length) (baseStart_6893356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893356 prefixEnd_6893356 := by exact prefixLift 6893356
  have htrace : WordTrace (prefixWord ++ tailWord_6893356) baseStart_6893356 baseEnd_6893356 := by
    simpa [prefixWord, tailWord_6893356, baseEnd_6893356] using wordTrace_append hprefix tailTrace_6893356
  have hstable : (prefixWord ++ tailWord_6893356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893356).length < 2 ^ (prefixWord ++ tailWord_6893356).sum := by decide
  have hdescent : baseEnd_6893356 < baseStart_6893356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893363 : List Nat := [1, 1, 1, 2, 8, 1, 1, 2, 2, 4]
def baseStart_6893363 : Nat := 118140960795 + 6893363 * 2 ^ 59
def prefixEnd_6893363 : Nat := 4983230072969 + 3 ^ 40 * 6893363 * 2
def baseEnd_6893363 : Nat := 1179869514973072806420169

theorem tailTrace_6893363 : CollatzResearch.WordTrace tailWord_6893363 prefixEnd_6893363 1179869514973072806420169 := by
  unfold tailWord_6893363
  simp only [CollatzResearch.WordTrace]
  refine ⟨251421603725530618516452743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167614402483687079010968495 251421603725530618516452743)
  ·
    refine ⟨377132405588295927774679115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251421603725530618516452743 377132405588295927774679115)
    ·
      refine ⟨565698608382443891662018673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377132405588295927774679115 565698608382443891662018673)
      ·
        refine ⟨424273956286832918746514005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 565698608382443891662018673 424273956286832918746514005)
        ·
          refine ⟨4971960425236323266560711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 424273956286832918746514005 4971960425236323266560711)
          ·
            refine ⟨7457940637854484899841067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4971960425236323266560711 7457940637854484899841067)
            ·
              refine ⟨11186910956781727349761601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7457940637854484899841067 11186910956781727349761601)
              ·
                refine ⟨8390183217586295512321201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11186910956781727349761601 8390183217586295512321201)
                ·
                  refine ⟨6292637413189721634240901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8390183217586295512321201 6292637413189721634240901)
                  ·
                    refine ⟨1179869514973072806420169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6292637413189721634240901 1179869514973072806420169)
                    ·
                      rfl

theorem cell23_6893363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 2, 2, 4].length) (baseStart_6893363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893363 prefixEnd_6893363 := by exact prefixLift 6893363
  have htrace : WordTrace (prefixWord ++ tailWord_6893363) baseStart_6893363 baseEnd_6893363 := by
    simpa [prefixWord, tailWord_6893363, baseEnd_6893363] using wordTrace_append hprefix tailTrace_6893363
  have hstable : (prefixWord ++ tailWord_6893363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893363).length < 2 ^ (prefixWord ++ tailWord_6893363).sum := by decide
  have hdescent : baseEnd_6893363 < baseStart_6893363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893404 : List Nat := [2, 2, 4, 2, 3, 1, 1, 3, 1, 2, 2]
def baseStart_6893404 : Nat := 118140960795 + 6893404 * 2 ^ 59
def prefixEnd_6893404 : Nat := 4983230072969 + 3 ^ 40 * 6893404 * 2
def baseEnd_6893404 : Nat := 3539629597626052758847819

theorem tailTrace_6893404 : CollatzResearch.WordTrace tailWord_6893404 prefixEnd_6893404 3539629597626052758847819 := by
  unfold tailWord_6893404
  simp only [CollatzResearch.WordTrace]
  refine ⟨125711549559191041259347633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167615399412254721679130177 125711549559191041259347633)
  ·
    refine ⟨94283662169393280944510725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125711549559191041259347633 94283662169393280944510725)
    ·
      refine ⟨17678186656761240177095761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94283662169393280944510725 17678186656761240177095761)
      ·
        refine ⟨13258639992570930132821821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17678186656761240177095761 13258639992570930132821821)
        ·
          refine ⟨4971989997214098799808183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13258639992570930132821821 4971989997214098799808183)
          ·
            refine ⟨7457984995821148199712275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4971989997214098799808183 7457984995821148199712275)
            ·
              refine ⟨11186977493731722299568413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7457984995821148199712275 11186977493731722299568413)
              ·
                refine ⟨4195116560149395862338155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11186977493731722299568413 4195116560149395862338155)
                ·
                  refine ⟨6292674840224093793507233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4195116560149395862338155 6292674840224093793507233)
                  ·
                    refine ⟨4719506130168070345130425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6292674840224093793507233 4719506130168070345130425)
                    ·
                      refine ⟨3539629597626052758847819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4719506130168070345130425 3539629597626052758847819)
                      ·
                        rfl

theorem cell23_6893404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_6893404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893404 prefixEnd_6893404 := by exact prefixLift 6893404
  have htrace : WordTrace (prefixWord ++ tailWord_6893404) baseStart_6893404 baseEnd_6893404 := by
    simpa [prefixWord, tailWord_6893404, baseEnd_6893404] using wordTrace_append hprefix tailTrace_6893404
  have hstable : (prefixWord ++ tailWord_6893404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893404).length < 2 ^ (prefixWord ++ tailWord_6893404).sum := by decide
  have hdescent : baseEnd_6893404 < baseStart_6893404 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893409 : List Nat := [1, 2, 3, 1, 1, 1, 4, 1, 3, 4, 2]
def baseStart_6893409 : Nat := 118140960795 + 6893409 * 2 ^ 59
def prefixEnd_6893409 : Nat := 4983230072969 + 3 ^ 40 * 6893409 * 2
def baseEnd_6893409 : Nat := 3539632165029325239285295

theorem tailTrace_6893409 : CollatzResearch.WordTrace tailWord_6893409 prefixEnd_6893409 3539632165029325239285295 := by
  unfold tailWord_6893409
  simp only [CollatzResearch.WordTrace]
  refine ⟨251423281483363968372627281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167615520988909312248418187 251423281483363968372627281)
  ·
    refine ⟨188567461112522976279470461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251423281483363968372627281 188567461112522976279470461)
    ·
      refine ⟨70712797917196116104801423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188567461112522976279470461 70712797917196116104801423)
      ·
        refine ⟨106069196875794174157202135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70712797917196116104801423 106069196875794174157202135)
        ·
          refine ⟨159103795313691261235803203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106069196875794174157202135 159103795313691261235803203)
          ·
            refine ⟨238655692970536891853704805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159103795313691261235803203 238655692970536891853704805)
            ·
              refine ⟨44747942431975667222569651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 238655692970536891853704805 44747942431975667222569651)
              ·
                refine ⟨67121913647963500833854477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44747942431975667222569651 67121913647963500833854477)
                ·
                  refine ⟨25170717617986312812695429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67121913647963500833854477 25170717617986312812695429)
                  ·
                    refine ⟨4719509553372433652380393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25170717617986312812695429 4719509553372433652380393)
                    ·
                      refine ⟨3539632165029325239285295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4719509553372433652380393 3539632165029325239285295)
                      ·
                        rfl

theorem cell23_6893409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 4, 2].length) (baseStart_6893409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893409 prefixEnd_6893409 := by exact prefixLift 6893409
  have htrace : WordTrace (prefixWord ++ tailWord_6893409) baseStart_6893409 baseEnd_6893409 := by
    simpa [prefixWord, tailWord_6893409, baseEnd_6893409] using wordTrace_append hprefix tailTrace_6893409
  have hstable : (prefixWord ++ tailWord_6893409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893409).length < 2 ^ (prefixWord ++ tailWord_6893409).sum := by decide
  have hdescent : baseEnd_6893409 < baseStart_6893409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893429 : List Nat := [1, 3, 4, 1, 1, 1, 2, 1, 2, 4, 3]
def baseStart_6893429 : Nat := 118140960795 + 6893429 * 2 ^ 59
def prefixEnd_6893429 : Nat := 4983230072969 + 3 ^ 40 * 6893429 * 2
def baseEnd_6893429 : Nat := 3539642434642415161035203

theorem tailTrace_6893429 : CollatzResearch.WordTrace tailWord_6893429 prefixEnd_6893429 3539642434642415161035203 := by
  unfold tailWord_6893429
  simp only [CollatzResearch.WordTrace]
  refine ⟨251424010943291511788355341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167616007295527674525570227 251424010943291511788355341)
  ·
    refine ⟨94284004103734316920633253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251424010943291511788355341 94284004103734316920633253)
    ·
      refine ⟨17678250769450184422618735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94284004103734316920633253 17678250769450184422618735)
      ·
        refine ⟨26517376154175276633928103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17678250769450184422618735 26517376154175276633928103)
        ·
          refine ⟨39776064231262914950892155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26517376154175276633928103 39776064231262914950892155)
          ·
            refine ⟨59664096346894372426338233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39776064231262914950892155 59664096346894372426338233)
            ·
              refine ⟨44748072260170779319753675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59664096346894372426338233 44748072260170779319753675)
              ·
                refine ⟨67122108390256168979630513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44748072260170779319753675 67122108390256168979630513)
                ·
                  refine ⟨50341581292692126734722885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67122108390256168979630513 50341581292692126734722885)
                  ·
                    refine ⟨9439046492379773762760541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50341581292692126734722885 9439046492379773762760541)
                    ·
                      refine ⟨3539642434642415161035203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9439046492379773762760541 3539642434642415161035203)
                      ·
                        rfl

theorem cell23_6893429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_6893429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893429 prefixEnd_6893429 := by exact prefixLift 6893429
  have htrace : WordTrace (prefixWord ++ tailWord_6893429) baseStart_6893429 baseEnd_6893429 := by
    simpa [prefixWord, tailWord_6893429, baseEnd_6893429] using wordTrace_append hprefix tailTrace_6893429
  have hstable : (prefixWord ++ tailWord_6893429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893429).length < 2 ^ (prefixWord ++ tailWord_6893429).sum := by decide
  have hdescent : baseEnd_6893429 < baseStart_6893429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893443 : List Nat := [1, 1, 1, 3, 4, 3, 1, 3, 2, 2, 2]
def baseStart_6893443 : Nat := 118140960795 + 6893443 * 2 ^ 59
def prefixEnd_6893443 : Nat := 4983230072969 + 3 ^ 40 * 6893443 * 2
def baseEnd_6893443 : Nat := 3539649623371578106260139

theorem tailTrace_6893443 : CollatzResearch.WordTrace tailWord_6893443 prefixEnd_6893443 3539649623371578106260139 := by
  unfold tailWord_6893443
  simp only [CollatzResearch.WordTrace]
  refine ⟨251424521565240792179364983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167616347710160528119576655 251424521565240792179364983)
  ·
    refine ⟨377136782347861188269047475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251424521565240792179364983 377136782347861188269047475)
    ·
      refine ⟨565705173521791782403571213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377136782347861188269047475 565705173521791782403571213)
      ·
        refine ⟨212139440070671918401339205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 565705173521791782403571213 212139440070671918401339205)
        ·
          refine ⟨39776145013250984700251101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212139440070671918401339205 39776145013250984700251101)
          ·
            refine ⟨14916054379969119262594163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39776145013250984700251101 14916054379969119262594163)
            ·
              refine ⟨22374081569953678893891245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14916054379969119262594163 22374081569953678893891245)
              ·
                refine ⟨8390280588732629585209217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22374081569953678893891245 8390280588732629585209217)
                ·
                  refine ⟨6292710441549472188906913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8390280588732629585209217 6292710441549472188906913)
                  ·
                    refine ⟨4719532831162104141680185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6292710441549472188906913 4719532831162104141680185)
                    ·
                      refine ⟨3539649623371578106260139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4719532831162104141680185 3539649623371578106260139)
                      ·
                        rfl

theorem cell23_6893443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3, 2, 2, 2].length) (baseStart_6893443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893443 prefixEnd_6893443 := by exact prefixLift 6893443
  have htrace : WordTrace (prefixWord ++ tailWord_6893443) baseStart_6893443 baseEnd_6893443 := by
    simpa [prefixWord, tailWord_6893443, baseEnd_6893443] using wordTrace_append hprefix tailTrace_6893443
  have hstable : (prefixWord ++ tailWord_6893443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893443).length < 2 ^ (prefixWord ++ tailWord_6893443).sum := by decide
  have hdescent : baseEnd_6893443 < baseStart_6893443 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893489 : List Nat := [1, 2, 2, 4, 2, 1, 2, 1, 1, 2, 5]
def baseStart_6893489 : Nat := 118140960795 + 6893489 * 2 ^ 59
def prefixEnd_6893489 : Nat := 4983230072969 + 3 ^ 40 * 6893489 * 2
def baseEnd_6893489 : Nat := 3539673243481684926284927

theorem tailTrace_6893489 : CollatzResearch.WordTrace tailWord_6893489 prefixEnd_6893489 3539673243481684926284927 := by
  unfold tailWord_6893489
  simp only [CollatzResearch.WordTrace]
  refine ⟨251426199323074142035539521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167617466215382761357026347 251426199323074142035539521)
  ·
    refine ⟨188569649492305606526654641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251426199323074142035539521 188569649492305606526654641)
    ·
      refine ⟨141427237119229204894990981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188569649492305606526654641 141427237119229204894990981)
      ·
        refine ⟨26517606959855475917810809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141427237119229204894990981 26517606959855475917810809)
        ·
          refine ⟨19888205219891606938358107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26517606959855475917810809 19888205219891606938358107)
          ·
            refine ⟨29832307829837410407537161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19888205219891606938358107 29832307829837410407537161)
            ·
              refine ⟨22374230872378057805652871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29832307829837410407537161 22374230872378057805652871)
              ·
                refine ⟨33561346308567086708479307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22374230872378057805652871 33561346308567086708479307)
                ·
                  refine ⟨50342019462850630062718961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33561346308567086708479307 50342019462850630062718961)
                  ·
                    refine ⟨37756514597137972547039221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50342019462850630062718961 37756514597137972547039221)
                    ·
                      refine ⟨3539673243481684926284927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37756514597137972547039221 3539673243481684926284927)
                      ·
                        rfl

theorem cell23_6893489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_6893489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893489 prefixEnd_6893489 := by exact prefixLift 6893489
  have htrace : WordTrace (prefixWord ++ tailWord_6893489) baseStart_6893489 baseEnd_6893489 := by
    simpa [prefixWord, tailWord_6893489, baseEnd_6893489] using wordTrace_append hprefix tailTrace_6893489
  have hstable : (prefixWord ++ tailWord_6893489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893489).length < 2 ^ (prefixWord ++ tailWord_6893489).sum := by decide
  have hdescent : baseEnd_6893489 < baseStart_6893489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893499 : List Nat := [1, 1, 1, 1, 1, 2, 2, 5, 1, 6, 2]
def baseStart_6893499 : Nat := 118140960795 + 6893499 * 2 ^ 59
def prefixEnd_6893499 : Nat := 4983230072969 + 3 ^ 40 * 6893499 * 2
def baseEnd_6893499 : Nat := 3539678378288229887159881

theorem tailTrace_6893499 : CollatzResearch.WordTrace tailWord_6893499 prefixEnd_6893499 3539678378288229887159881 := by
  unfold tailWord_6893499
  simp only [CollatzResearch.WordTrace]
  refine ⟨251426564053037913743403551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167617709368691942495602367 251426564053037913743403551)
  ·
    refine ⟨377139846079556870615105327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251426564053037913743403551 377139846079556870615105327)
    ·
      refine ⟨565709769119335305922657991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377139846079556870615105327 565709769119335305922657991)
      ·
        refine ⟨848564653679002958883986987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565709769119335305922657991 848564653679002958883986987)
        ·
          refine ⟨1272846980518504438325980481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 848564653679002958883986987 1272846980518504438325980481)
          ·
            refine ⟨954635235388878328744485361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1272846980518504438325980481 954635235388878328744485361)
            ·
              refine ⟨715976426541658746558364021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 954635235388878328744485361 715976426541658746558364021)
              ·
                refine ⟨67122789988280507489846627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 715976426541658746558364021 67122789988280507489846627)
                ·
                  refine ⟨100684184982420761234769941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67122789988280507489846627 100684184982420761234769941)
                  ·
                    refine ⟨4719571171050973182879841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 100684184982420761234769941 4719571171050973182879841)
                    ·
                      refine ⟨3539678378288229887159881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4719571171050973182879841 3539678378288229887159881)
                      ·
                        rfl

theorem cell23_6893499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 6, 2].length) (baseStart_6893499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893499 prefixEnd_6893499 := by exact prefixLift 6893499
  have htrace : WordTrace (prefixWord ++ tailWord_6893499) baseStart_6893499 baseEnd_6893499 := by
    simpa [prefixWord, tailWord_6893499, baseEnd_6893499] using wordTrace_append hprefix tailTrace_6893499
  have hstable : (prefixWord ++ tailWord_6893499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893499).length < 2 ^ (prefixWord ++ tailWord_6893499).sum := by decide
  have hdescent : baseEnd_6893499 < baseStart_6893499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893516 : List Nat := [2, 2, 1, 4, 1, 2, 3, 1, 2, 1, 4]
def baseStart_6893516 : Nat := 118140960795 + 6893516 * 2 ^ 59
def prefixEnd_6893516 : Nat := 4983230072969 + 3 ^ 40 * 6893516 * 2
def baseEnd_6893516 : Nat := 3539687107459356320647303

theorem tailTrace_6893516 : CollatzResearch.WordTrace tailWord_6893516 prefixEnd_6893516 3539687107459356320647303 := by
  unfold tailWord_6893516
  simp only [CollatzResearch.WordTrace]
  refine ⟨125713592046988162823386201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167618122729317550431181601 125713592046988162823386201)
  ·
    refine ⟨94285194035241122117539651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125713592046988162823386201 94285194035241122117539651)
    ·
      refine ⟨141427791052861683176309477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94285194035241122117539651 141427791052861683176309477)
      ·
        refine ⟨26517710822411565595558027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141427791052861683176309477 26517710822411565595558027)
        ·
          refine ⟨39776566233617348393337041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26517710822411565595558027 39776566233617348393337041)
          ·
            refine ⟨29832424675213011295002781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39776566233617348393337041 29832424675213011295002781)
            ·
              refine ⟨11187159253204879235626043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29832424675213011295002781 11187159253204879235626043)
              ·
                refine ⟨16780738879807318853439065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11187159253204879235626043 16780738879807318853439065)
                ·
                  refine ⟨12585554159855489140079299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16780738879807318853439065 12585554159855489140079299)
                  ·
                    refine ⟨18878331239783233710118949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12585554159855489140079299 18878331239783233710118949)
                    ·
                      refine ⟨3539687107459356320647303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18878331239783233710118949 3539687107459356320647303)
                      ·
                        rfl

theorem cell23_6893516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_6893516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893516 prefixEnd_6893516 := by exact prefixLift 6893516
  have htrace : WordTrace (prefixWord ++ tailWord_6893516) baseStart_6893516 baseEnd_6893516 := by
    simpa [prefixWord, tailWord_6893516, baseEnd_6893516] using wordTrace_append hprefix tailTrace_6893516
  have hstable : (prefixWord ++ tailWord_6893516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893516).length < 2 ^ (prefixWord ++ tailWord_6893516).sum := by decide
  have hdescent : baseEnd_6893516 < baseStart_6893516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893519 : List Nat := [1, 1, 2, 1, 1, 5, 3, 1, 1, 4, 3]
def baseStart_6893519 : Nat := 118140960795 + 6893519 * 2 ^ 59
def prefixEnd_6893519 : Nat := 4983230072969 + 3 ^ 40 * 6893519 * 2
def baseEnd_6893519 : Nat := 3539688647901319808909789

theorem tailTrace_6893519 : CollatzResearch.WordTrace tailWord_6893519 prefixEnd_6893519 3539688647901319808909789 := by
  unfold tailWord_6893519
  simp only [CollatzResearch.WordTrace]
  refine ⟨251427293512965457159131611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167618195675310304772754407 251427293512965457159131611)
  ·
    refine ⟨377140940269448185738697417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251427293512965457159131611 377140940269448185738697417)
    ·
      refine ⟨282855705202086139304023063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377140940269448185738697417 282855705202086139304023063)
      ·
        refine ⟨424283557803129208956034595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282855705202086139304023063 424283557803129208956034595)
        ·
          refine ⟨636425336704693813434051893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424283557803129208956034595 636425336704693813434051893)
          ·
            refine ⟨59664875316065045009442365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 636425336704693813434051893 59664875316065045009442365)
            ·
              refine ⟨22374328243524391878540887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59664875316065045009442365 22374328243524391878540887)
              ·
                refine ⟨33561492365286587817811331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22374328243524391878540887 33561492365286587817811331)
                ·
                  refine ⟨50342238547929881726716997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33561492365286587817811331 50342238547929881726716997)
                  ·
                    refine ⟨9439169727736852823759437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50342238547929881726716997 9439169727736852823759437)
                    ·
                      refine ⟨3539688647901319808909789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9439169727736852823759437 3539688647901319808909789)
                      ·
                        rfl

theorem cell23_6893519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 4, 3].length) (baseStart_6893519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893519 prefixEnd_6893519 := by exact prefixLift 6893519
  have htrace : WordTrace (prefixWord ++ tailWord_6893519) baseStart_6893519 baseEnd_6893519 := by
    simpa [prefixWord, tailWord_6893519, baseEnd_6893519] using wordTrace_append hprefix tailTrace_6893519
  have hstable : (prefixWord ++ tailWord_6893519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893519).length < 2 ^ (prefixWord ++ tailWord_6893519).sum := by decide
  have hdescent : baseEnd_6893519 < baseStart_6893519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893539 : List Nat := [1, 1, 1, 6, 1, 3, 1, 1, 8]
def baseStart_6893539 : Nat := 118140960795 + 6893539 * 2 ^ 59
def prefixEnd_6893539 : Nat := 4983230072969 + 3 ^ 40 * 6893539 * 2
def baseEnd_6893539 : Nat := 393299879723823303406633

theorem tailTrace_6893539 : CollatzResearch.WordTrace tailWord_6893539 prefixEnd_6893539 393299879723823303406633 := by
  unfold tailWord_6893539
  simp only [CollatzResearch.WordTrace]
  refine ⟨251428022972893000574859671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167618681981928667049906447 251428022972893000574859671)
  ·
    refine ⟨377142034459339500862289507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251428022972893000574859671 377142034459339500862289507)
    ·
      refine ⟨565713051689009251293434261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377142034459339500862289507 565713051689009251293434261)
      ·
        refine ⟨26517799297922308654379731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 565713051689009251293434261 26517799297922308654379731)
        ·
          refine ⟨39776698946883462981569597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26517799297922308654379731 39776698946883462981569597)
          ·
            refine ⟨14916262105081298618088599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39776698946883462981569597 14916262105081298618088599)
            ·
              refine ⟨22374393157621947927132899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14916262105081298618088599 22374393157621947927132899)
              ·
                refine ⟨33561589736432921890699349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22374393157621947927132899 33561589736432921890699349)
                ·
                  refine ⟨393299879723823303406633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33561589736432921890699349 393299879723823303406633)
                  ·
                    rfl

theorem cell23_6893539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 8].length) (baseStart_6893539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893539 prefixEnd_6893539 := by exact prefixLift 6893539
  have htrace : WordTrace (prefixWord ++ tailWord_6893539) baseStart_6893539 baseEnd_6893539 := by
    simpa [prefixWord, tailWord_6893539, baseEnd_6893539] using wordTrace_append hprefix tailTrace_6893539
  have hstable : (prefixWord ++ tailWord_6893539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893539).length < 2 ^ (prefixWord ++ tailWord_6893539).sum := by decide
  have hdescent : baseEnd_6893539 < baseStart_6893539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893543 : List Nat := [1, 1, 5, 2, 3, 1, 2, 1, 3, 4]
def baseStart_6893543 : Nat := 118140960795 + 6893543 * 2 ^ 59
def prefixEnd_6893543 : Nat := 4983230072969 + 3 ^ 40 * 6893543 * 2
def baseEnd_6893543 : Nat := 1179900323812342571669893

theorem tailTrace_6893543 : CollatzResearch.WordTrace tailWord_6893543 prefixEnd_6893543 1179900323812342571669893 := by
  unfold tailWord_6893543
  simp only [CollatzResearch.WordTrace]
  refine ⟨251428168864878509258005283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167618779243252339505336855 251428168864878509258005283)
  ·
    refine ⟨377142253297317763887007925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251428168864878509258005283 377142253297317763887007925)
    ·
      refine ⟨35357086246623540364406993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 377142253297317763887007925 35357086246623540364406993)
      ·
        refine ⟨26517814684967655273305245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35357086246623540364406993 26517814684967655273305245)
        ·
          refine ⟨9944180506862870727489467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26517814684967655273305245 9944180506862870727489467)
          ·
            refine ⟨14916270760294306091234201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9944180506862870727489467 14916270760294306091234201)
            ·
              refine ⟨11187203070220729568425651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14916270760294306091234201 11187203070220729568425651)
              ·
                refine ⟨16780804605331094352638477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11187203070220729568425651 16780804605331094352638477)
                ·
                  refine ⟨6292801726999160382239429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16780804605331094352638477 6292801726999160382239429)
                  ·
                    refine ⟨1179900323812342571669893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6292801726999160382239429 1179900323812342571669893)
                    ·
                      rfl

theorem cell23_6893543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_6893543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893543 prefixEnd_6893543 := by exact prefixLift 6893543
  have htrace : WordTrace (prefixWord ++ tailWord_6893543) baseStart_6893543 baseEnd_6893543 := by
    simpa [prefixWord, tailWord_6893543, baseEnd_6893543] using wordTrace_append hprefix tailTrace_6893543
  have hstable : (prefixWord ++ tailWord_6893543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893543).length < 2 ^ (prefixWord ++ tailWord_6893543).sum := by decide
  have hdescent : baseEnd_6893543 < baseStart_6893543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893576 : List Nat := [2, 1, 3, 2, 1, 2, 1, 3, 1, 5, 2]
def baseStart_6893576 : Nat := 118140960795 + 6893576 * 2 ^ 59
def prefixEnd_6893576 : Nat := 4983230072969 + 3 ^ 40 * 6893576 * 2
def baseEnd_6893576 : Nat := 3539717916298626085897027

theorem tailTrace_6893576 : CollatzResearch.WordTrace tailWord_6893576 prefixEnd_6893576 3539717916298626085897027 := by
  unfold tailWord_6893576
  simp only [CollatzResearch.WordTrace]
  refine ⟨125714686236879477946978291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167619581649172637262637721 125714686236879477946978291)
  ·
    refine ⟨188572029355319216920467437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125714686236879477946978291 188572029355319216920467437)
    ·
      refine ⟨70714511008244706345175289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188572029355319216920467437 70714511008244706345175289)
      ·
        refine ⟨53035883256183529758881467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70714511008244706345175289 53035883256183529758881467)
        ·
          refine ⟨79553824884275294638322201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53035883256183529758881467 79553824884275294638322201)
          ·
            refine ⟨59665368663206470978741651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79553824884275294638322201 59665368663206470978741651)
            ·
              refine ⟨89498052994809706468112477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59665368663206470978741651 89498052994809706468112477)
              ·
                refine ⟨33561769873053639925542179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89498052994809706468112477 33561769873053639925542179)
                ·
                  refine ⟨50342654809580459888313269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33561769873053639925542179 50342654809580459888313269)
                  ·
                    refine ⟨4719623888398168114529369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50342654809580459888313269 4719623888398168114529369)
                    ·
                      refine ⟨3539717916298626085897027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4719623888398168114529369 3539717916298626085897027)
                      ·
                        rfl

theorem cell23_6893576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 1, 5, 2].length) (baseStart_6893576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893576 prefixEnd_6893576 := by exact prefixLift 6893576
  have htrace : WordTrace (prefixWord ++ tailWord_6893576) baseStart_6893576 baseEnd_6893576 := by
    simpa [prefixWord, tailWord_6893576, baseEnd_6893576] using wordTrace_append hprefix tailTrace_6893576
  have hstable : (prefixWord ++ tailWord_6893576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893576).length < 2 ^ (prefixWord ++ tailWord_6893576).sum := by decide
  have hdescent : baseEnd_6893576 < baseStart_6893576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893607 : List Nat := [1, 1, 7, 1, 3, 1, 2, 1, 6]
def baseStart_6893607 : Nat := 118140960795 + 6893607 * 2 ^ 59
def prefixEnd_6893607 : Nat := 4983230072969 + 3 ^ 40 * 6893607 * 2
def baseEnd_6893607 : Nat := 393303759355435051623265

theorem tailTrace_6893607 : CollatzResearch.WordTrace tailWord_6893607 prefixEnd_6893607 393303759355435051623265 := by
  unfold tailWord_6893607
  simp only [CollatzResearch.WordTrace]
  refine ⟨251430503136646648188335075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167620335424431098792223383 251430503136646648188335075)
  ·
    refine ⟨377145754704969972282502613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251430503136646648188335075 377145754704969972282502613)
    ·
      refine ⟨8839353625897733725371155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 377145754704969972282502613 8839353625897733725371155)
      ·
        refine ⟨13259030438846600588056733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8839353625897733725371155 13259030438846600588056733)
        ·
          refine ⟨4972136414567475220521275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13259030438846600588056733 4972136414567475220521275)
          ·
            refine ⟨7458204621851212830781913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4972136414567475220521275 7458204621851212830781913)
            ·
              refine ⟨5593653466388409623086435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7458204621851212830781913 5593653466388409623086435)
              ·
                refine ⟨8390480199582614434629653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5593653466388409623086435 8390480199582614434629653)
                ·
                  refine ⟨393303759355435051623265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8390480199582614434629653 393303759355435051623265)
                  ·
                    rfl

theorem cell23_6893607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 1, 6].length) (baseStart_6893607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893607 prefixEnd_6893607 := by exact prefixLift 6893607
  have htrace : WordTrace (prefixWord ++ tailWord_6893607) baseStart_6893607 baseEnd_6893607 := by
    simpa [prefixWord, tailWord_6893607, baseEnd_6893607] using wordTrace_append hprefix tailTrace_6893607
  have hstable : (prefixWord ++ tailWord_6893607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893607).length < 2 ^ (prefixWord ++ tailWord_6893607).sum := by decide
  have hdescent : baseEnd_6893607 < baseStart_6893607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893619 : List Nat := [1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 6]
def baseStart_6893619 : Nat := 118140960795 + 6893619 * 2 ^ 59
def prefixEnd_6893619 : Nat := 4983230072969 + 3 ^ 40 * 6893619 * 2
def baseEnd_6893619 : Nat := 3539739995966769417659329

theorem tailTrace_6893619 : CollatzResearch.WordTrace tailWord_6893619 prefixEnd_6893619 3539739995966769417659329 := by
  unfold tailWord_6893619
  simp only [CollatzResearch.WordTrace]
  refine ⟨251430940812603174237771911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167620627208402116158514607 251430940812603174237771911)
  ·
    refine ⟨377146411218904761356657867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251430940812603174237771911 377146411218904761356657867)
    ·
      refine ⟨565719616828357142034986801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377146411218904761356657867 565719616828357142034986801)
      ·
        refine ⟨424289712621267856526240101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 565719616828357142034986801 424289712621267856526240101)
        ·
          refine ⟨79554321116487723098670019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 424289712621267856526240101 79554321116487723098670019)
          ·
            refine ⟨119331481674731584648005029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79554321116487723098670019 119331481674731584648005029)
            ·
              refine ⟨22374652814012172121500943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119331481674731584648005029 22374652814012172121500943)
              ·
                refine ⟨33561979221018258182251415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22374652814012172121500943 33561979221018258182251415)
                ·
                  refine ⟨50342968831527387273377123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33561979221018258182251415 50342968831527387273377123)
                  ·
                    refine ⟨75514453247291080910065685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50342968831527387273377123 75514453247291080910065685)
                    ·
                      refine ⟨3539739995966769417659329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75514453247291080910065685 3539739995966769417659329)
                      ·
                        rfl

theorem cell23_6893619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 6].length) (baseStart_6893619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893619 prefixEnd_6893619 := by exact prefixLift 6893619
  have htrace : WordTrace (prefixWord ++ tailWord_6893619) baseStart_6893619 baseEnd_6893619 := by
    simpa [prefixWord, tailWord_6893619, baseEnd_6893619] using wordTrace_append hprefix tailTrace_6893619
  have hstable : (prefixWord ++ tailWord_6893619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893619).length < 2 ^ (prefixWord ++ tailWord_6893619).sum := by decide
  have hdescent : baseEnd_6893619 < baseStart_6893619 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893623 : List Nat := [1, 1, 3, 1, 2, 2, 2, 4, 3, 2, 2]
def baseStart_6893623 : Nat := 118140960795 + 6893623 * 2 ^ 59
def prefixEnd_6893623 : Nat := 4983230072969 + 3 ^ 40 * 6893623 * 2
def baseEnd_6893623 : Nat := 3539742049889387402009311

theorem tailTrace_6893623 : CollatzResearch.WordTrace tailWord_6893623 prefixEnd_6893623 3539742049889387402009311 := by
  unfold tailWord_6893623
  simp only [CollatzResearch.WordTrace]
  refine ⟨251431086704588682920917523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167620724469725788613945015 251431086704588682920917523)
  ·
    refine ⟨377146630056883024381376285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251431086704588682920917523 377146630056883024381376285)
    ·
      refine ⟨141429986271331134143016107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377146630056883024381376285 141429986271331134143016107)
      ·
        refine ⟨212144979406996701214524161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141429986271331134143016107 212144979406996701214524161)
        ·
          refine ⟨159108734555247525910893121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212144979406996701214524161 159108734555247525910893121)
          ·
            refine ⟨119331550916435644433169841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159108734555247525910893121 119331550916435644433169841)
            ·
              refine ⟨89498663187326733324877381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119331550916435644433169841 89498663187326733324877381)
              ·
                refine ⟨16780999347623762498414509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89498663187326733324877381 16780999347623762498414509)
                ·
                  refine ⟨6292874755358910936905441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16780999347623762498414509 6292874755358910936905441)
                  ·
                    refine ⟨4719656066519183202679081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6292874755358910936905441 4719656066519183202679081)
                    ·
                      refine ⟨3539742049889387402009311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4719656066519183202679081 3539742049889387402009311)
                      ·
                        rfl

theorem cell23_6893623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 3, 2, 2].length) (baseStart_6893623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893623 prefixEnd_6893623 := by exact prefixLift 6893623
  have htrace : WordTrace (prefixWord ++ tailWord_6893623) baseStart_6893623 baseEnd_6893623 := by
    simpa [prefixWord, tailWord_6893623, baseEnd_6893623] using wordTrace_append hprefix tailTrace_6893623
  have hstable : (prefixWord ++ tailWord_6893623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893623).length < 2 ^ (prefixWord ++ tailWord_6893623).sum := by decide
  have hdescent : baseEnd_6893623 < baseStart_6893623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893629 : List Nat := [1, 4, 1, 3, 1, 1, 1, 11]
def baseStart_6893629 : Nat := 118140960795 + 6893629 * 2 ^ 59
def prefixEnd_6893629 : Nat := 4983230072969 + 3 ^ 40 * 6893629 * 2
def baseEnd_6893629 : Nat := 131101671510122754760529

theorem tailTrace_6893629 : CollatzResearch.WordTrace tailWord_6893629 prefixEnd_6893629 131101671510122754760529 := by
  unfold tailWord_6893629
  simp only [CollatzResearch.WordTrace]
  refine ⟨251431305542566945945635941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167620870361711297297090627 251431305542566945945635941)
  ·
    refine ⟨47143369789231302364806739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 251431305542566945945635941 47143369789231302364806739)
    ·
      refine ⟨70715054683846953547210109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47143369789231302364806739 70715054683846953547210109)
      ·
        refine ⟨26518145506442607580203791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70715054683846953547210109 26518145506442607580203791)
        ·
          refine ⟨39777218259663911370305687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26518145506442607580203791 39777218259663911370305687)
          ·
            refine ⟨59665827389495867055458531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39777218259663911370305687 59665827389495867055458531)
            ·
              refine ⟨89498741084243800583187797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59665827389495867055458531 89498741084243800583187797)
              ·
                refine ⟨131101671510122754760529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 89498741084243800583187797 131101671510122754760529)
                ·
                  rfl

theorem cell23_6893629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 11].length) (baseStart_6893629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893629 prefixEnd_6893629 := by exact prefixLift 6893629
  have htrace : WordTrace (prefixWord ++ tailWord_6893629) baseStart_6893629 baseEnd_6893629 := by
    simpa [prefixWord, tailWord_6893629, baseEnd_6893629] using wordTrace_append hprefix tailTrace_6893629
  have hstable : (prefixWord ++ tailWord_6893629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893629).length < 2 ^ (prefixWord ++ tailWord_6893629).sum := by decide
  have hdescent : baseEnd_6893629 < baseStart_6893629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893650 : List Nat := [3, 2, 2, 1, 4, 1, 2, 2, 2, 4]
def baseStart_6893650 : Nat := 118140960795 + 6893650 * 2 ^ 59
def prefixEnd_6893650 : Nat := 4983230072969 + 3 ^ 40 * 6893650 * 2
def baseEnd_6893650 : Nat := 1179918637955686265457229

theorem tailTrace_6893650 : CollatzResearch.WordTrace tailWord_6893650 prefixEnd_6893650 1179918637955686265457229 := by
  unfold tailWord_6893650
  simp only [CollatzResearch.WordTrace]
  refine ⟨62858017868872716633037601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167621380983660577688100269 62858017868872716633037601)
  ·
    refine ⟨47143513401654537474778201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62858017868872716633037601 47143513401654537474778201)
    ·
      refine ⟨35357635051240903106083651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47143513401654537474778201 35357635051240903106083651)
      ·
        refine ⟨53036452576861354659125477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35357635051240903106083651 53036452576861354659125477)
        ·
          refine ⟨9944334858161503998586027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53036452576861354659125477 9944334858161503998586027)
          ·
            refine ⟨14916502287242255997879041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9944334858161503998586027 14916502287242255997879041)
            ·
              refine ⟨11187376715431691998409281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14916502287242255997879041 11187376715431691998409281)
              ·
                refine ⟨8390532536573768998806961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11187376715431691998409281 8390532536573768998806961)
                ·
                  refine ⟨6292899402430326749105221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8390532536573768998806961 6292899402430326749105221)
                  ·
                    refine ⟨1179918637955686265457229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6292899402430326749105221 1179918637955686265457229)
                    ·
                      rfl

theorem cell23_6893650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_6893650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893650 prefixEnd_6893650 := by exact prefixLift 6893650
  have htrace : WordTrace (prefixWord ++ tailWord_6893650) baseStart_6893650 baseEnd_6893650 := by
    simpa [prefixWord, tailWord_6893650, baseEnd_6893650] using wordTrace_append hprefix tailTrace_6893650
  have hstable : (prefixWord ++ tailWord_6893650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893650).length < 2 ^ (prefixWord ++ tailWord_6893650).sum := by decide
  have hdescent : baseEnd_6893650 < baseStart_6893650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893673 : List Nat := [1, 2, 1, 1, 1, 5, 1, 5, 2, 1, 3]
def baseStart_6893673 : Nat := 118140960795 + 6893673 * 2 ^ 59
def prefixEnd_6893673 : Nat := 4983230072969 + 3 ^ 40 * 6893673 * 2
def baseEnd_6893673 : Nat := 3539767723922112206384081

theorem tailTrace_6893673 : CollatzResearch.WordTrace tailWord_6893673 prefixEnd_6893673 3539767723922112206384081 := by
  unfold tailWord_6893673
  simp only [CollatzResearch.WordTrace]
  refine ⟨251432910354407541460237673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167621940236271694306825115 251432910354407541460237673)
  ·
    refine ⟨188574682765805656095178255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251432910354407541460237673 188574682765805656095178255)
    ·
      refine ⟨282862024148708484142767383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188574682765805656095178255 282862024148708484142767383)
      ·
        refine ⟨424293036223062726214151075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282862024148708484142767383 424293036223062726214151075)
        ·
          refine ⟨636439554334594089321226613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424293036223062726214151075 636439554334594089321226613)
          ·
            refine ⟨59666208218868195873864995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 636439554334594089321226613 59666208218868195873864995)
            ·
              refine ⟨89499312328302293810797493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59666208218868195873864995 89499312328302293810797493)
              ·
                refine ⟨8390560530778340044762265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89499312328302293810797493 8390560530778340044762265)
                ·
                  refine ⟨6292920398083755033571699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8390560530778340044762265 6292920398083755033571699)
                  ·
                    refine ⟨9439380597125632550357549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6292920398083755033571699 9439380597125632550357549)
                    ·
                      refine ⟨3539767723922112206384081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9439380597125632550357549 3539767723922112206384081)
                      ·
                        rfl

theorem cell23_6893673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5, 2, 1, 3].length) (baseStart_6893673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893673 prefixEnd_6893673 := by exact prefixLift 6893673
  have htrace : WordTrace (prefixWord ++ tailWord_6893673) baseStart_6893673 baseEnd_6893673 := by
    simpa [prefixWord, tailWord_6893673, baseEnd_6893673] using wordTrace_append hprefix tailTrace_6893673
  have hstable : (prefixWord ++ tailWord_6893673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893673).length < 2 ^ (prefixWord ++ tailWord_6893673).sum := by decide
  have hdescent : baseEnd_6893673 < baseStart_6893673 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893700 : List Nat := [2, 3, 2, 1, 2, 1, 3, 3, 1, 3, 2]
def baseStart_6893700 : Nat := 118140960795 + 6893700 * 2 ^ 59
def prefixEnd_6893700 : Nat := 4983230072969 + 3 ^ 40 * 6893700 * 2
def baseEnd_6893700 : Nat := 3539781587899783600746457

theorem tailTrace_6893700 : CollatzResearch.WordTrace tailWord_6893700 prefixEnd_6893700 3539781587899783600746457 := by
  unfold tailWord_6893700
  simp only [CollatzResearch.WordTrace]
  refine ⟨125716947562654862535735277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167622596750206483380980369 125716947562654862535735277)
  ·
    refine ⟨47143855335995573450900729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125716947562654862535735277 47143855335995573450900729)
    ·
      refine ⟨35357891501996680088175547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47143855335995573450900729 35357891501996680088175547)
      ·
        refine ⟨53036837252995020132263321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35357891501996680088175547 53036837252995020132263321)
        ·
          refine ⟨39777627939746265099197491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53036837252995020132263321 39777627939746265099197491)
          ·
            refine ⟨59666441909619397648796237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39777627939746265099197491 59666441909619397648796237)
            ·
              refine ⟨22374915716107274118298589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59666441909619397648796237 22374915716107274118298589)
              ·
                refine ⟨8390593393540227794361971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22374915716107274118298589 8390593393540227794361971)
                ·
                  refine ⟨12585890090310341691542957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8390593393540227794361971 12585890090310341691542957)
                  ·
                    refine ⟨4719708783866378134328609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12585890090310341691542957 4719708783866378134328609)
                    ·
                      refine ⟨3539781587899783600746457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4719708783866378134328609 3539781587899783600746457)
                      ·
                        rfl

theorem cell23_6893700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3, 1, 3, 2].length) (baseStart_6893700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893700 prefixEnd_6893700 := by exact prefixLift 6893700
  have htrace : WordTrace (prefixWord ++ tailWord_6893700) baseStart_6893700 baseEnd_6893700 := by
    simpa [prefixWord, tailWord_6893700, baseEnd_6893700] using wordTrace_append hprefix tailTrace_6893700
  have hstable : (prefixWord ++ tailWord_6893700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893700).length < 2 ^ (prefixWord ++ tailWord_6893700).sum := by decide
  have hdescent : baseEnd_6893700 < baseStart_6893700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893706 : List Nat := [3, 1, 2, 3, 1, 2, 1, 2, 2, 6]
def baseStart_6893706 : Nat := 118140960795 + 6893706 * 2 ^ 59
def prefixEnd_6893706 : Nat := 4983230072969 + 3 ^ 40 * 6893706 * 2
def baseEnd_6893706 : Nat := 1179928222927903525757143

theorem tailTrace_6893706 : CollatzResearch.WordTrace tailWord_6893706 prefixEnd_6893706 1179928222927903525757143 := by
  unfold tailWord_6893706
  simp only [CollatzResearch.WordTrace]
  refine ⟨62858528490821997024047243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167622742642191992064125981 62858528490821997024047243)
  ·
    refine ⟨94287792736232995536070865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62858528490821997024047243 94287792736232995536070865)
    ·
      refine ⟨70715844552174746652053149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94287792736232995536070865 70715844552174746652053149)
      ·
        refine ⟨26518441707065529994519931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70715844552174746652053149 26518441707065529994519931)
        ·
          refine ⟨39777662560598294991779897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26518441707065529994519931 39777662560598294991779897)
          ·
            refine ⟨29833246920448721243834923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39777662560598294991779897 29833246920448721243834923)
            ·
              refine ⟨44749870380673081865752385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29833246920448721243834923 44749870380673081865752385)
              ·
                refine ⟨33562402785504811399314289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44749870380673081865752385 33562402785504811399314289)
                ·
                  refine ⟨25171802089128608549485717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33562402785504811399314289 25171802089128608549485717)
                  ·
                    refine ⟨1179928222927903525757143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25171802089128608549485717 1179928222927903525757143)
                    ·
                      rfl

theorem cell23_6893706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_6893706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893706 prefixEnd_6893706 := by exact prefixLift 6893706
  have htrace : WordTrace (prefixWord ++ tailWord_6893706) baseStart_6893706 baseEnd_6893706 := by
    simpa [prefixWord, tailWord_6893706, baseEnd_6893706] using wordTrace_append hprefix tailTrace_6893706
  have hstable : (prefixWord ++ tailWord_6893706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893706).length < 2 ^ (prefixWord ++ tailWord_6893706).sum := by decide
  have hdescent : baseEnd_6893706 < baseStart_6893706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893718 : List Nat := [5, 3, 2, 1, 1, 1, 3, 1, 2, 4]
def baseStart_6893718 : Nat := 118140960795 + 6893718 * 2 ^ 59
def prefixEnd_6893718 : Nat := 4983230072969 + 3 ^ 40 * 6893718 * 2
def baseEnd_6893718 : Nat := 1179930276850521510107125

theorem tailTrace_6893718 : CollatzResearch.WordTrace tailWord_6893718 prefixEnd_6893718 1179930276850521510107125 := by
  unfold tailWord_6893718
  simp only [CollatzResearch.WordTrace]
  refine ⟨15714659477452782134101613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167623034426163009430417205 15714659477452782134101613)
  ·
    refine ⟨5892997304044793300288105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15714659477452782134101613 5892997304044793300288105)
    ·
      refine ⟨4419747978033594975216079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5892997304044793300288105 4419747978033594975216079)
      ·
        refine ⟨6629621967050392462824119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4419747978033594975216079 6629621967050392462824119)
        ·
          refine ⟨9944432950575588694236179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6629621967050392462824119 9944432950575588694236179)
          ·
            refine ⟨14916649425863383041354269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9944432950575588694236179 14916649425863383041354269)
            ·
              refine ⟨5593743534698768640507851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14916649425863383041354269 5593743534698768640507851)
              ·
                refine ⟨8390615302048152960761777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5593743534698768640507851 8390615302048152960761777)
                ·
                  refine ⟨6292961476536114720571333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8390615302048152960761777 6292961476536114720571333)
                  ·
                    refine ⟨1179930276850521510107125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6292961476536114720571333 1179930276850521510107125)
                    ·
                      rfl

theorem cell23_6893718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_6893718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893718 prefixEnd_6893718 := by exact prefixLift 6893718
  have htrace : WordTrace (prefixWord ++ tailWord_6893718) baseStart_6893718 baseEnd_6893718 := by
    simpa [prefixWord, tailWord_6893718, baseEnd_6893718] using wordTrace_append hprefix tailTrace_6893718
  have hstable : (prefixWord ++ tailWord_6893718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893718).length < 2 ^ (prefixWord ++ tailWord_6893718).sum := by decide
  have hdescent : baseEnd_6893718 < baseStart_6893718 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893739 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 6]
def baseStart_6893739 : Nat := 118140960795 + 6893739 * 2 ^ 59
def prefixEnd_6893739 : Nat := 4983230072969 + 3 ^ 40 * 6893739 * 2
def baseEnd_6893739 : Nat := 3539801613645308948158777

theorem tailTrace_6893739 : CollatzResearch.WordTrace tailWord_6893739 prefixEnd_6893739 3539801613645308948158777 := by
  unfold tailWord_6893739
  simp only [CollatzResearch.WordTrace]
  refine ⟨251435317572168434732140271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167623545048112289821426847 251435317572168434732140271)
  ·
    refine ⟨377152976358252652098210407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251435317572168434732140271 377152976358252652098210407)
    ·
      refine ⟨565729464537378978147315611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377152976358252652098210407 565729464537378978147315611)
      ·
        refine ⟨848594196806068467220973417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565729464537378978147315611 848594196806068467220973417)
        ·
          refine ⟨636445647604551350415730063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 848594196806068467220973417 636445647604551350415730063)
          ·
            refine ⟨954668471406827025623595095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 636445647604551350415730063 954668471406827025623595095)
            ·
              refine ⟨1432002707110240538435392643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 954668471406827025623595095 1432002707110240538435392643)
              ·
                refine ⟨2148004060665360807653088965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1432002707110240538435392643 2148004060665360807653088965)
                ·
                  refine ⟨402750761374755151434954181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2148004060665360807653088965 402750761374755151434954181)
                  ·
                    refine ⟨75515767757766590894053909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 402750761374755151434954181 75515767757766590894053909)
                    ·
                      refine ⟨3539801613645308948158777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75515767757766590894053909 3539801613645308948158777)
                      ·
                        rfl

theorem cell23_6893739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 6].length) (baseStart_6893739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893739 prefixEnd_6893739 := by exact prefixLift 6893739
  have htrace : WordTrace (prefixWord ++ tailWord_6893739) baseStart_6893739 baseEnd_6893739 := by
    simpa [prefixWord, tailWord_6893739, baseEnd_6893739] using wordTrace_append hprefix tailTrace_6893739
  have hstable : (prefixWord ++ tailWord_6893739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893739).length < 2 ^ (prefixWord ++ tailWord_6893739).sum := by decide
  have hdescent : baseEnd_6893739 < baseStart_6893739 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893770 : List Nat := [3, 1, 2, 1, 3, 1, 5, 2, 5]
def baseStart_6893770 : Nat := 118140960795 + 6893770 * 2 ^ 59
def prefixEnd_6893770 : Nat := 4983230072969 + 3 ^ 40 * 6893770 * 2
def baseEnd_6893770 : Nat := 393313059060622036319015

theorem tailTrace_6893770 : CollatzResearch.WordTrace tailWord_6893770 prefixEnd_6893770 393313059060622036319015 := by
  unfold tailWord_6893770
  simp only [CollatzResearch.WordTrace]
  refine ⟨62859112058764031756629691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167624298823370751351012509 62859112058764031756629691)
  ·
    refine ⟨94288668088146047634944537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62859112058764031756629691 94288668088146047634944537)
    ·
      refine ⟨70716501066109535726208403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94288668088146047634944537 70716501066109535726208403)
      ·
        refine ⟨106074751599164303589312605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70716501066109535726208403 106074751599164303589312605)
        ·
          refine ⟨39778031849686613845992227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106074751599164303589312605 39778031849686613845992227)
          ·
            refine ⟨59667047774529920768988341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39778031849686613845992227 59667047774529920768988341)
            ·
              refine ⟨5593785728862180072092657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59667047774529920768988341 5593785728862180072092657)
              ·
                refine ⟨4195339296646635054069493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5593785728862180072092657 4195339296646635054069493)
                ·
                  refine ⟨393313059060622036319015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4195339296646635054069493 393313059060622036319015)
                  ·
                    rfl

theorem cell23_6893770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 2, 5].length) (baseStart_6893770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893770 prefixEnd_6893770 := by exact prefixLift 6893770
  have htrace : WordTrace (prefixWord ++ tailWord_6893770) baseStart_6893770 baseEnd_6893770 := by
    simpa [prefixWord, tailWord_6893770, baseEnd_6893770] using wordTrace_append hprefix tailTrace_6893770
  have hstable : (prefixWord ++ tailWord_6893770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893770).length < 2 ^ (prefixWord ++ tailWord_6893770).sum := by decide
  have hdescent : baseEnd_6893770 < baseStart_6893770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893781 : List Nat := [1, 3, 2, 4, 2, 2, 2, 1, 2, 2, 2]
def baseStart_6893781 : Nat := 118140960795 + 6893781 * 2 ^ 59
def prefixEnd_6893781 : Nat := 4983230072969 + 3 ^ 40 * 6893781 * 2
def baseEnd_6893781 : Nat := 3539823179832797783833585

theorem tailTrace_6893781 : CollatzResearch.WordTrace tailWord_6893781 prefixEnd_6893781 3539823179832797783833585 := by
  unfold tailWord_6893781
  simp only [CollatzResearch.WordTrace]
  refine ⟨251436849438016275905169197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167624566292010850603446131 251436849438016275905169197)
  ·
    refine ⟨94288818539256103464438449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251436849438016275905169197 94288818539256103464438449)
    ·
      refine ⟨70716613904442077598328837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94288818539256103464438449 70716613904442077598328837)
      ·
        refine ⟨13259365107082889549686657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70716613904442077598328837 13259365107082889549686657)
        ·
          refine ⟨9944523830312167162264993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13259365107082889549686657 9944523830312167162264993)
          ·
            refine ⟨7458392872734125371698745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9944523830312167162264993 7458392872734125371698745)
            ·
              refine ⟨5593794654550594028774059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7458392872734125371698745 5593794654550594028774059)
              ·
                refine ⟨8390691981825891043161089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5593794654550594028774059 8390691981825891043161089)
                ·
                  refine ⟨6293018986369418282370817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8390691981825891043161089 6293018986369418282370817)
                  ·
                    refine ⟨4719764239777063711778113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6293018986369418282370817 4719764239777063711778113)
                    ·
                      refine ⟨3539823179832797783833585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4719764239777063711778113 3539823179832797783833585)
                      ·
                        rfl

theorem cell23_6893781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_6893781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893781 prefixEnd_6893781 := by exact prefixLift 6893781
  have htrace : WordTrace (prefixWord ++ tailWord_6893781) baseStart_6893781 baseEnd_6893781 := by
    simpa [prefixWord, tailWord_6893781, baseEnd_6893781] using wordTrace_append hprefix tailTrace_6893781
  have hstable : (prefixWord ++ tailWord_6893781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893781).length < 2 ^ (prefixWord ++ tailWord_6893781).sum := by decide
  have hdescent : baseEnd_6893781 < baseStart_6893781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893786 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 3, 3, 4]
def baseStart_6893786 : Nat := 118140960795 + 6893786 * 2 ^ 59
def prefixEnd_6893786 : Nat := 4983230072969 + 3 ^ 40 * 6893786 * 2
def baseEnd_6893786 : Nat := 3539825747236070264271061

theorem tailTrace_6893786 : CollatzResearch.WordTrace tailWord_6893786 prefixEnd_6893786 3539825747236070264271061 := by
  unfold tailWord_6893786
  simp only [CollatzResearch.WordTrace]
  refine ⟨62859257950749540439775303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167624687868665441172734141 62859257950749540439775303)
  ·
    refine ⟨94288886926124310659662955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62859257950749540439775303 94288886926124310659662955)
    ·
      refine ⟨141433330389186465989494433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94288886926124310659662955 141433330389186465989494433)
      ·
        refine ⟨106074997791889849492120825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141433330389186465989494433 106074997791889849492120825)
        ·
          refine ⟨79556248343917387119090619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106074997791889849492120825 79556248343917387119090619)
          ·
            refine ⟨119334372515876080678635929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79556248343917387119090619 119334372515876080678635929)
            ·
              refine ⟨89500779386907060508976947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119334372515876080678635929 89500779386907060508976947)
              ·
                refine ⟨134251169080360590763465421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89500779386907060508976947 134251169080360590763465421)
                ·
                  refine ⟨50344188405135221536299533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134251169080360590763465421 50344188405135221536299533)
                  ·
                    refine ⟨18879070651925708076112325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50344188405135221536299533 18879070651925708076112325)
                    ·
                      refine ⟨3539825747236070264271061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18879070651925708076112325 3539825747236070264271061)
                      ·
                        rfl

theorem cell23_6893786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_6893786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893786 prefixEnd_6893786 := by exact prefixLift 6893786
  have htrace : WordTrace (prefixWord ++ tailWord_6893786) baseStart_6893786 baseEnd_6893786 := by
    simpa [prefixWord, tailWord_6893786, baseEnd_6893786] using wordTrace_append hprefix tailTrace_6893786
  have hstable : (prefixWord ++ tailWord_6893786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893786).length < 2 ^ (prefixWord ++ tailWord_6893786).sum := by decide
  have hdescent : baseEnd_6893786 < baseStart_6893786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893803 : List Nat := [1, 1, 1, 1, 2, 5, 4, 1, 2, 1, 4]
def baseStart_6893803 : Nat := 118140960795 + 6893803 * 2 ^ 59
def prefixEnd_6893803 : Nat := 4983230072969 + 3 ^ 40 * 6893803 * 2
def baseEnd_6893803 : Nat := 3539834476407196697758483

theorem tailTrace_6893803 : CollatzResearch.WordTrace tailWord_6893803 prefixEnd_6893803 3539834476407196697758483 := by
  unfold tailWord_6893803
  simp only [CollatzResearch.WordTrace]
  refine ⟨251437651843936573662470063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167625101229291049108313375 251437651843936573662470063)
  ·
    refine ⟨377156477765904860493705095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251437651843936573662470063 377156477765904860493705095)
    ·
      refine ⟨565734716648857290740557643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377156477765904860493705095 565734716648857290740557643)
      ·
        refine ⟨848602074973285936110836465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565734716648857290740557643 848602074973285936110836465)
        ·
          refine ⟨636451556229964452083127349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 848602074973285936110836465 636451556229964452083127349)
          ·
            refine ⟨59667333396559167382793189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 636451556229964452083127349 59667333396559167382793189)
            ·
              refine ⟨11187625011854843884273723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59667333396559167382793189 11187625011854843884273723)
              ·
                refine ⟨16781437517782265826410585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11187625011854843884273723 16781437517782265826410585)
                ·
                  refine ⟨12586078138336699369807939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16781437517782265826410585 12586078138336699369807939)
                  ·
                    refine ⟨18879117207505049054711909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12586078138336699369807939 18879117207505049054711909)
                    ·
                      refine ⟨3539834476407196697758483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18879117207505049054711909 3539834476407196697758483)
                      ·
                        rfl

theorem cell23_6893803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 2, 1, 4].length) (baseStart_6893803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893803 prefixEnd_6893803 := by exact prefixLift 6893803
  have htrace : WordTrace (prefixWord ++ tailWord_6893803) baseStart_6893803 baseEnd_6893803 := by
    simpa [prefixWord, tailWord_6893803, baseEnd_6893803] using wordTrace_append hprefix tailTrace_6893803
  have hstable : (prefixWord ++ tailWord_6893803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893803).length < 2 ^ (prefixWord ++ tailWord_6893803).sum := by decide
  have hdescent : baseEnd_6893803 < baseStart_6893803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893823 : List Nat := [1, 1, 2, 2, 1, 4, 1, 4, 2, 2, 3]
def baseStart_6893823 : Nat := 118140960795 + 6893823 * 2 ^ 59
def prefixEnd_6893823 : Nat := 4983230072969 + 3 ^ 40 * 6893823 * 2
def baseEnd_6893823 : Nat := 3539844746020286619508391

theorem tailTrace_6893823 : CollatzResearch.WordTrace tailWord_6893823 prefixEnd_6893823 3539844746020286619508391 := by
  unfold tailWord_6893823
  simp only [CollatzResearch.WordTrace]
  refine ⟨251438381303864117078198123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167625587535909411385465415 251438381303864117078198123)
  ·
    refine ⟨377157571955796175617297185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251438381303864117078198123 377157571955796175617297185)
    ·
      refine ⟨282868178966847131712972889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377157571955796175617297185 282868178966847131712972889)
      ·
        refine ⟨212151134225135348784729667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282868178966847131712972889 212151134225135348784729667)
        ·
          refine ⟨318226701337703023177094501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212151134225135348784729667 318226701337703023177094501)
          ·
            refine ⟨59667506500819316845705219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 318226701337703023177094501 59667506500819316845705219)
            ·
              refine ⟨89501259751228975268557829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59667506500819316845705219 89501259751228975268557829)
              ·
                refine ⟨16781486203355432862854593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89501259751228975268557829 16781486203355432862854593)
                ·
                  refine ⟨12586114652516574647140945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16781486203355432862854593 12586114652516574647140945)
                  ·
                    refine ⟨9439585989387430985355709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12586114652516574647140945 9439585989387430985355709)
                    ·
                      refine ⟨3539844746020286619508391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9439585989387430985355709 3539844746020286619508391)
                      ·
                        rfl

theorem cell23_6893823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2, 2, 3].length) (baseStart_6893823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893823 prefixEnd_6893823 := by exact prefixLift 6893823
  have htrace : WordTrace (prefixWord ++ tailWord_6893823) baseStart_6893823 baseEnd_6893823 := by
    simpa [prefixWord, tailWord_6893823, baseEnd_6893823] using wordTrace_append hprefix tailTrace_6893823
  have hstable : (prefixWord ++ tailWord_6893823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893823).length < 2 ^ (prefixWord ++ tailWord_6893823).sum := by decide
  have hdescent : baseEnd_6893823 < baseStart_6893823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893854 : List Nat := [4, 3, 2, 1, 1, 3, 1, 1, 2, 1, 4]
def baseStart_6893854 : Nat := 118140960795 + 6893854 * 2 ^ 59
def prefixEnd_6893854 : Nat := 4983230072969 + 3 ^ 40 * 6893854 * 2
def baseEnd_6893854 : Nat := 3539860663920575998220749

theorem tailTrace_6893854 : CollatzResearch.WordTrace tailWord_6893854 prefixEnd_6893854 3539860663920575998220749 := by
  unfold tailWord_6893854
  simp only [CollatzResearch.WordTrace]
  refine ⟨31429938995843976171572077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167626341311167872915051077 31429938995843976171572077)
  ·
    refine ⟨11786227123441491064339529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31429938995843976171572077 11786227123441491064339529)
    ·
      refine ⟨8839670342581118298254647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11786227123441491064339529 8839670342581118298254647)
      ·
        refine ⟨13259505513871677447381971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8839670342581118298254647 13259505513871677447381971)
        ·
          refine ⟨19889258270807516171072957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13259505513871677447381971 19889258270807516171072957)
          ·
            refine ⟨7458471851552818564152359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19889258270807516171072957 7458471851552818564152359)
            ·
              refine ⟨11187707777329227846228539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7458471851552818564152359 11187707777329227846228539)
              ·
                refine ⟨16781561665993841769342809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11187707777329227846228539 16781561665993841769342809)
                ·
                  refine ⟨12586171249495381327007107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16781561665993841769342809 12586171249495381327007107)
                  ·
                    refine ⟨18879256874243071990510661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12586171249495381327007107 18879256874243071990510661)
                    ·
                      refine ⟨3539860663920575998220749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18879256874243071990510661 3539860663920575998220749)
                      ·
                        rfl

theorem cell23_6893854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_6893854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893854 prefixEnd_6893854 := by exact prefixLift 6893854
  have htrace : WordTrace (prefixWord ++ tailWord_6893854) baseStart_6893854 baseEnd_6893854 := by
    simpa [prefixWord, tailWord_6893854, baseEnd_6893854] using wordTrace_append hprefix tailTrace_6893854
  have hstable : (prefixWord ++ tailWord_6893854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893854).length < 2 ^ (prefixWord ++ tailWord_6893854).sum := by decide
  have hdescent : baseEnd_6893854 < baseStart_6893854 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893864 : List Nat := [2, 1, 5, 1, 3, 1, 2, 3, 1, 4]
def baseStart_6893864 : Nat := 118140960795 + 6893864 * 2 ^ 59
def prefixEnd_6893864 : Nat := 4983230072969 + 3 ^ 40 * 6893864 * 2
def baseEnd_6893864 : Nat := 1179955266242373653031901

theorem tailTrace_6893864 : CollatzResearch.WordTrace tailWord_6893864 prefixEnd_6893864 1179955266242373653031901 := by
  unfold tailWord_6893864
  simp only [CollatzResearch.WordTrace]
  refine ⟨125719938348357790540220323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167626584464477054053627097 125719938348357790540220323)
  ·
    refine ⟨188579907522536685810330485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125719938348357790540220323 188579907522536685810330485)
    ·
      refine ⟨17679366330237814294718483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 188579907522536685810330485 17679366330237814294718483)
      ·
        refine ⟨26519049495356721442077725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17679366330237814294718483 26519049495356721442077725)
        ·
          refine ⟨9944643560758770540779147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26519049495356721442077725 9944643560758770540779147)
          ·
            refine ⟨14916965341138155811168721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9944643560758770540779147 14916965341138155811168721)
            ·
              refine ⟨11187724005853616858376541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14916965341138155811168721 11187724005853616858376541)
              ·
                refine ⟨4195396502195106321891203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11187724005853616858376541 4195396502195106321891203)
                ·
                  refine ⟨6293094753292659482836805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4195396502195106321891203 6293094753292659482836805)
                  ·
                    refine ⟨1179955266242373653031901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6293094753292659482836805 1179955266242373653031901)
                    ·
                      rfl

theorem cell23_6893864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_6893864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893864 prefixEnd_6893864 := by exact prefixLift 6893864
  have htrace : WordTrace (prefixWord ++ tailWord_6893864) baseStart_6893864 baseEnd_6893864 := by
    simpa [prefixWord, tailWord_6893864, baseEnd_6893864] using wordTrace_append hprefix tailTrace_6893864
  have hstable : (prefixWord ++ tailWord_6893864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893864).length < 2 ^ (prefixWord ++ tailWord_6893864).sum := by decide
  have hdescent : baseEnd_6893864 < baseStart_6893864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893880 : List Nat := [2, 1, 2, 1, 3, 1, 2, 4, 2, 3, 2]
def baseStart_6893880 : Nat := 118140960795 + 6893880 * 2 ^ 59
def prefixEnd_6893880 : Nat := 4983230072969 + 3 ^ 40 * 6893880 * 2
def baseEnd_6893880 : Nat := 3539874014417592896495629

theorem tailTrace_6893880 : CollatzResearch.WordTrace tailWord_6893880 prefixEnd_6893880 3539874014417592896495629 := by
  unfold tailWord_6893880
  simp only [CollatzResearch.WordTrace]
  refine ⟨125720230132328807906511547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167626973509771743875348729 125720230132328807906511547)
  ·
    refine ⟨188580345198493211859767321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125720230132328807906511547 188580345198493211859767321)
    ·
      refine ⟨141435258898869908894825491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188580345198493211859767321 141435258898869908894825491)
      ·
        refine ⟨212152888348304863342238237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141435258898869908894825491 212152888348304863342238237)
        ·
          refine ⟨79557333130614323753339339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212152888348304863342238237 79557333130614323753339339)
          ·
            refine ⟨119335999695921485630009009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79557333130614323753339339 119335999695921485630009009)
            ·
              refine ⟨89501999771941114222506757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119335999695921485630009009 89501999771941114222506757)
              ·
                refine ⟨16781624957238958916720017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89501999771941114222506757 16781624957238958916720017)
                ·
                  refine ⟨12586218717929219187540013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16781624957238958916720017 12586218717929219187540013)
                  ·
                    refine ⟨4719832019223457195327505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12586218717929219187540013 4719832019223457195327505)
                    ·
                      refine ⟨3539874014417592896495629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4719832019223457195327505 3539874014417592896495629)
                      ·
                        rfl

theorem cell23_6893880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 2, 3, 2].length) (baseStart_6893880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893880 prefixEnd_6893880 := by exact prefixLift 6893880
  have htrace : WordTrace (prefixWord ++ tailWord_6893880) baseStart_6893880 baseEnd_6893880 := by
    simpa [prefixWord, tailWord_6893880, baseEnd_6893880] using wordTrace_append hprefix tailTrace_6893880
  have hstable : (prefixWord ++ tailWord_6893880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893880).length < 2 ^ (prefixWord ++ tailWord_6893880).sum := by decide
  have hdescent : baseEnd_6893880 < baseStart_6893880 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893887 : List Nat := [1, 1, 2, 2, 4, 1, 1, 6, 1, 1, 3]
def baseStart_6893887 : Nat := 118140960795 + 6893887 * 2 ^ 59
def prefixEnd_6893887 : Nat := 4983230072969 + 3 ^ 40 * 6893887 * 2
def baseEnd_6893887 : Nat := 3539877608782174369108097

theorem tailTrace_6893887 : CollatzResearch.WordTrace tailWord_6893887 prefixEnd_6893887 3539877608782174369108097 := by
  unfold tailWord_6893887
  simp only [CollatzResearch.WordTrace]
  refine ⟨251440715575632256008527915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167627143717088170672351943 251440715575632256008527915)
  ·
    refine ⟨377161073363448384012791873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251440715575632256008527915 377161073363448384012791873)
    ·
      refine ⟨282870805022586288009593905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377161073363448384012791873 282870805022586288009593905)
      ·
        refine ⟨212153103766939716007195429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282870805022586288009593905 212153103766939716007195429)
        ·
          refine ⟨39778706956301196751349143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212153103766939716007195429 39778706956301196751349143)
          ·
            refine ⟨59668060434451795127023715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39778706956301196751349143 59668060434451795127023715)
            ·
              refine ⟨89502090651677692690535573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59668060434451795127023715 89502090651677692690535573)
              ·
                refine ⟨4195410499297391844868855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89502090651677692690535573 4195410499297391844868855)
                ·
                  refine ⟨6293115748946087767303283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4195410499297391844868855 6293115748946087767303283)
                  ·
                    refine ⟨9439673623419131650954925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6293115748946087767303283 9439673623419131650954925)
                    ·
                      refine ⟨3539877608782174369108097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9439673623419131650954925 3539877608782174369108097)
                      ·
                        rfl

theorem cell23_6893887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 6, 1, 1, 3].length) (baseStart_6893887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893887 prefixEnd_6893887 := by exact prefixLift 6893887
  have htrace : WordTrace (prefixWord ++ tailWord_6893887) baseStart_6893887 baseEnd_6893887 := by
    simpa [prefixWord, tailWord_6893887, baseEnd_6893887] using wordTrace_append hprefix tailTrace_6893887
  have hstable : (prefixWord ++ tailWord_6893887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893887).length < 2 ^ (prefixWord ++ tailWord_6893887).sum := by decide
  have hdescent : baseEnd_6893887 < baseStart_6893887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893923 : List Nat := [1, 1, 1, 5, 2, 1, 2, 1, 3, 2, 4]
def baseStart_6893923 : Nat := 118140960795 + 6893923 * 2 ^ 59
def prefixEnd_6893923 : Nat := 4983230072969 + 3 ^ 40 * 6893923 * 2
def baseEnd_6893923 : Nat := 3539896094085736228257931

theorem tailTrace_6893923 : CollatzResearch.WordTrace tailWord_6893923 prefixEnd_6893923 3539896094085736228257931 := by
  unfold tailWord_6893923
  simp only [CollatzResearch.WordTrace]
  refine ⟨251442028603501834156838423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167628019069001222771225615 251442028603501834156838423)
  ·
    refine ⟨377163042905252751235257635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251442028603501834156838423 377163042905252751235257635)
    ·
      refine ⟨565744564357879126852886453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377163042905252751235257635 565744564357879126852886453)
      ·
        refine ⟨53038552908551168142458105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 565744564357879126852886453 53038552908551168142458105)
        ·
          refine ⟨39778914681413376106843579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53038552908551168142458105 39778914681413376106843579)
          ·
            refine ⟨59668372022120064160265369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39778914681413376106843579 59668372022120064160265369)
            ·
              refine ⟨44751279016590048120199027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59668372022120064160265369 44751279016590048120199027)
              ·
                refine ⟨67126918524885072180298541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44751279016590048120199027 67126918524885072180298541)
                ·
                  refine ⟨25172594446831902067611953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67126918524885072180298541 25172594446831902067611953)
                  ·
                    refine ⟨18879445835123926550708965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25172594446831902067611953 18879445835123926550708965)
                    ·
                      refine ⟨3539896094085736228257931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18879445835123926550708965 3539896094085736228257931)
                      ·
                        rfl

theorem cell23_6893923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_6893923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893923 prefixEnd_6893923 := by exact prefixLift 6893923
  have htrace : WordTrace (prefixWord ++ tailWord_6893923) baseStart_6893923 baseEnd_6893923 := by
    simpa [prefixWord, tailWord_6893923, baseEnd_6893923] using wordTrace_append hprefix tailTrace_6893923
  have hstable : (prefixWord ++ tailWord_6893923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893923).length < 2 ^ (prefixWord ++ tailWord_6893923).sum := by decide
  have hdescent : baseEnd_6893923 < baseStart_6893923 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893930 : List Nat := [3, 1, 3, 3, 1, 1, 1, 3, 1, 1, 5]
def baseStart_6893930 : Nat := 118140960795 + 6893930 * 2 ^ 59
def prefixEnd_6893930 : Nat := 4983230072969 + 3 ^ 40 * 6893930 * 2
def baseEnd_6893930 : Nat := 3539899688450317700870399

theorem tailTrace_6893930 : CollatzResearch.WordTrace tailWord_6893930 prefixEnd_6893930 3539899688450317700870399 := by
  unfold tailWord_6893930
  simp only [CollatzResearch.WordTrace]
  refine ⟨62860570978619118588085811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167628189276317649568228829 62860570978619118588085811)
  ·
    refine ⟨94290856467928677882128717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62860570978619118588085811 94290856467928677882128717)
    ·
      refine ⟨35359071175473254205798269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94290856467928677882128717 35359071175473254205798269)
      ·
        refine ⟨13259651690802470327174351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35359071175473254205798269 13259651690802470327174351)
        ·
          refine ⟨19889477536203705490761527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13259651690802470327174351 19889477536203705490761527)
          ·
            refine ⟨29834216304305558236142291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19889477536203705490761527 29834216304305558236142291)
            ·
              refine ⟨44751324456458337354213437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29834216304305558236142291 44751324456458337354213437)
              ·
                refine ⟨16781746671171876507830039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44751324456458337354213437 16781746671171876507830039)
                ·
                  refine ⟨25172620006757814761745059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16781746671171876507830039 25172620006757814761745059)
                  ·
                    refine ⟨37758930010136722142617589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25172620006757814761745059 37758930010136722142617589)
                    ·
                      refine ⟨3539899688450317700870399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37758930010136722142617589 3539899688450317700870399)
                      ·
                        rfl

theorem cell23_6893930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_6893930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893930 prefixEnd_6893930 := by exact prefixLift 6893930
  have htrace : WordTrace (prefixWord ++ tailWord_6893930) baseStart_6893930 baseEnd_6893930 := by
    simpa [prefixWord, tailWord_6893930, baseEnd_6893930] using wordTrace_append hprefix tailTrace_6893930
  have hstable : (prefixWord ++ tailWord_6893930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893930).length < 2 ^ (prefixWord ++ tailWord_6893930).sum := by decide
  have hdescent : baseEnd_6893930 < baseStart_6893930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893943 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 5, 3, 3]
def baseStart_6893943 : Nat := 118140960795 + 6893943 * 2 ^ 59
def prefixEnd_6893943 : Nat := 4983230072969 + 3 ^ 40 * 6893943 * 2
def baseEnd_6893943 : Nat := 3539906363698826150007839

theorem tailTrace_6893943 : CollatzResearch.WordTrace tailWord_6893943 prefixEnd_6893943 3539906363698826150007839 := by
  unfold tailWord_6893943
  simp only [CollatzResearch.WordTrace]
  refine ⟨251442758063429377572566483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167628505375619585048377655 251442758063429377572566483)
  ·
    refine ⟨377164137095144066358849725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251442758063429377572566483 377164137095144066358849725)
    ·
      refine ⟨141436551410679024884568647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377164137095144066358849725 141436551410679024884568647)
      ·
        refine ⟨212154827116018537326852971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141436551410679024884568647 212154827116018537326852971)
        ·
          refine ⟨318232240674027805990279457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212154827116018537326852971 318232240674027805990279457)
          ·
            refine ⟨238674180505520854492709593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318232240674027805990279457 238674180505520854492709593)
            ·
              refine ⟨179005635379140640869532195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238674180505520854492709593 179005635379140640869532195)
              ·
                refine ⟨268508453068710961304298293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179005635379140640869532195 268508453068710961304298293)
                ·
                  refine ⟨25172667475191652622277965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 268508453068710961304298293 25172667475191652622277965)
                  ·
                    refine ⟨9439750303196869733354237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25172667475191652622277965 9439750303196869733354237)
                    ·
                      refine ⟨3539906363698826150007839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9439750303196869733354237 3539906363698826150007839)
                      ·
                        rfl

theorem cell23_6893943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 3, 3].length) (baseStart_6893943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893943 prefixEnd_6893943 := by exact prefixLift 6893943
  have htrace : WordTrace (prefixWord ++ tailWord_6893943) baseStart_6893943 baseEnd_6893943 := by
    simpa [prefixWord, tailWord_6893943, baseEnd_6893943] using wordTrace_append hprefix tailTrace_6893943
  have hstable : (prefixWord ++ tailWord_6893943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893943).length < 2 ^ (prefixWord ++ tailWord_6893943).sum := by decide
  have hdescent : baseEnd_6893943 < baseStart_6893943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6893960 : List Nat := [2, 1, 3, 3, 1, 1, 2, 3, 1, 3, 3]
def baseStart_6893960 : Nat := 118140960795 + 6893960 * 2 ^ 59
def prefixEnd_6893960 : Nat := 4983230072969 + 3 ^ 40 * 6893960 * 2
def baseEnd_6893960 : Nat := 3539915092869952583495261

theorem tailTrace_6893960 : CollatzResearch.WordTrace tailWord_6893960 prefixEnd_6893960 3539915092869952583495261 := by
  unfold tailWord_6893960
  simp only [CollatzResearch.WordTrace]
  refine ⟨125721689052183894737967667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167628918736245192983956889 125721689052183894737967667)
  ·
    refine ⟨188582533578275842106951501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125721689052183894737967667 188582533578275842106951501)
    ·
      refine ⟨70718450091853440790106813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188582533578275842106951501 70718450091853440790106813)
      ·
        refine ⟨26519418784445040296290055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70718450091853440790106813 26519418784445040296290055)
        ·
          refine ⟨39779128176667560444435083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26519418784445040296290055 39779128176667560444435083)
          ·
            refine ⟨59668692265001340666652625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39779128176667560444435083 59668692265001340666652625)
            ·
              refine ⟨44751519198751005499989469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59668692265001340666652625 44751519198751005499989469)
              ·
                refine ⟨16781819699531627062496051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44751519198751005499989469 16781819699531627062496051)
                ·
                  refine ⟨25172729549297440593744077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16781819699531627062496051 25172729549297440593744077)
                  ·
                    refine ⟨9439773580986540222654029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25172729549297440593744077 9439773580986540222654029)
                    ·
                      refine ⟨3539915092869952583495261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9439773580986540222654029 3539915092869952583495261)
                      ·
                        rfl

theorem cell23_6893960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_6893960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6893960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6893960 prefixEnd_6893960 := by exact prefixLift 6893960
  have htrace : WordTrace (prefixWord ++ tailWord_6893960) baseStart_6893960 baseEnd_6893960 := by
    simpa [prefixWord, tailWord_6893960, baseEnd_6893960] using wordTrace_append hprefix tailTrace_6893960
  have hstable : (prefixWord ++ tailWord_6893960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6893960).length < 2 ^ (prefixWord ++ tailWord_6893960).sum := by decide
  have hdescent : baseEnd_6893960 < baseStart_6893960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6893960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6894023 : List Nat := [1, 1, 4, 1, 1, 4, 1, 1, 9]
def baseStart_6894023 : Nat := 118140960795 + 6894023 * 2 ^ 59
def prefixEnd_6894023 : Nat := 4983230072969 + 3 ^ 40 * 6894023 * 2
def baseEnd_6894023 : Nat := 393327493572353981889719

theorem tailTrace_6894023 : CollatzResearch.WordTrace tailWord_6894023 prefixEnd_6894023 393327493572353981889719 := by
  unfold tailWord_6894023
  simp only [CollatzResearch.WordTrace]
  refine ⟨251445675903139551235478723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167630450602093034156985815 251445675903139551235478723)
  ·
    refine ⟨377168513854709326853218085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251445675903139551235478723 377168513854709326853218085)
    ·
      refine ⟨70719096347757998784978391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 377168513854709326853218085 70719096347757998784978391)
      ·
        refine ⟨106078644521636998177467587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70719096347757998784978391 106078644521636998177467587)
        ·
          refine ⟨159117966782455497266201381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106078644521636998177467587 159117966782455497266201381)
          ·
            refine ⟨29834618771710405737412759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159117966782455497266201381 29834618771710405737412759)
            ·
              refine ⟨44751928157565608606119139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29834618771710405737412759 44751928157565608606119139)
              ·
                refine ⟨67127892236348412909178709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44751928157565608606119139 67127892236348412909178709)
                ·
                  refine ⟨393327493572353981889719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67127892236348412909178709 393327493572353981889719)
                  ·
                    rfl

theorem cell23_6894023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 9].length) (baseStart_6894023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6894023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6894023 prefixEnd_6894023 := by exact prefixLift 6894023
  have htrace : WordTrace (prefixWord ++ tailWord_6894023) baseStart_6894023 baseEnd_6894023 := by
    simpa [prefixWord, tailWord_6894023, baseEnd_6894023] using wordTrace_append hprefix tailTrace_6894023
  have hstable : (prefixWord ++ tailWord_6894023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6894023).length < 2 ^ (prefixWord ++ tailWord_6894023).sum := by decide
  have hdescent : baseEnd_6894023 < baseStart_6894023 := by decide
  rcases family_descends (prefixWord ++ tailWord_6894023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6894063 : List Nat := [1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 7]
def baseStart_6894063 : Nat := 118140960795 + 6894063 * 2 ^ 59
def prefixEnd_6894063 : Nat := 4983230072969 + 3 ^ 40 * 6894063 * 2
def baseEnd_6894063 : Nat := 3539967981377365680507287

theorem tailTrace_6894063 : CollatzResearch.WordTrace tailWord_6894063 prefixEnd_6894063 3539967981377365680507287 := by
  unfold tailWord_6894063
  simp only [CollatzResearch.WordTrace]
  refine ⟨251447134822994638066934843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167631423215329758711289895 251447134822994638066934843)
  ·
    refine ⟨377170702234491957100402265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251447134822994638066934843 377170702234491957100402265)
    ·
      refine ⟨282878026675868967825301699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377170702234491957100402265 282878026675868967825301699)
      ·
        refine ⟨424317040013803451737952549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282878026675868967825301699 424317040013803451737952549)
        ·
          refine ⟨79559445002588147200866103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 424317040013803451737952549 79559445002588147200866103)
          ·
            refine ⟨119339167503882220801299155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79559445002588147200866103 119339167503882220801299155)
            ·
              refine ⟨179008751255823331201948733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119339167503882220801299155 179008751255823331201948733)
              ·
                refine ⟨67128281720933749200730775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179008751255823331201948733 67128281720933749200730775)
                ·
                  refine ⟨100692422581400623801096163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67128281720933749200730775 100692422581400623801096163)
                  ·
                    refine ⟨151038633872100935701644245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 100692422581400623801096163 151038633872100935701644245)
                    ·
                      refine ⟨3539967981377365680507287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 151038633872100935701644245 3539967981377365680507287)
                      ·
                        rfl

theorem cell23_6894063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 7].length) (baseStart_6894063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6894063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6894063 prefixEnd_6894063 := by exact prefixLift 6894063
  have htrace : WordTrace (prefixWord ++ tailWord_6894063) baseStart_6894063 baseEnd_6894063 := by
    simpa [prefixWord, tailWord_6894063, baseEnd_6894063] using wordTrace_append hprefix tailTrace_6894063
  have hstable : (prefixWord ++ tailWord_6894063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6894063).length < 2 ^ (prefixWord ++ tailWord_6894063).sum := by decide
  have hdescent : baseEnd_6894063 < baseStart_6894063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6894063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6894070 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 3, 7]
def baseStart_6894070 : Nat := 118140960795 + 6894070 * 2 ^ 59
def prefixEnd_6894070 : Nat := 4983230072969 + 3 ^ 40 * 6894070 * 2
def baseEnd_6894070 : Nat := 1179990525247315717706585

theorem tailTrace_6894070 : CollatzResearch.WordTrace tailWord_6894070 prefixEnd_6894070 1179990525247315717706585 := by
  unfold tailWord_6894070
  simp only [CollatzResearch.WordTrace]
  refine ⟨15715461883373079891402479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167631593422646185508293109 15715461883373079891402479)
  ·
    refine ⟨23573192825059619837103719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15715461883373079891402479 23573192825059619837103719)
    ·
      refine ⟨35359789237589429755655579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23573192825059619837103719 35359789237589429755655579)
      ·
        refine ⟨53039683856384144633483369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35359789237589429755655579 53039683856384144633483369)
        ·
          refine ⟨39779762892288108475112527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53039683856384144633483369 39779762892288108475112527)
          ·
            refine ⟨59669644338432162712668791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39779762892288108475112527 59669644338432162712668791)
            ·
              refine ⟨89504466507648244069003187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59669644338432162712668791 89504466507648244069003187)
              ·
                refine ⟨134256699761472366103504781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89504466507648244069003187 134256699761472366103504781)
                ·
                  refine ⟨50346262410552137288814293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134256699761472366103504781 50346262410552137288814293)
                  ·
                    refine ⟨1179990525247315717706585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50346262410552137288814293 1179990525247315717706585)
                    ·
                      rfl

theorem cell23_6894070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_6894070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6894070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6894070 prefixEnd_6894070 := by exact prefixLift 6894070
  have htrace : WordTrace (prefixWord ++ tailWord_6894070) baseStart_6894070 baseEnd_6894070 := by
    simpa [prefixWord, tailWord_6894070, baseEnd_6894070] using wordTrace_append hprefix tailTrace_6894070
  have hstable : (prefixWord ++ tailWord_6894070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6894070).length < 2 ^ (prefixWord ++ tailWord_6894070).sum := by decide
  have hdescent : baseEnd_6894070 < baseStart_6894070 := by decide
  rcases family_descends (prefixWord ++ tailWord_6894070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6894083 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 2, 8]
def baseStart_6894083 : Nat := 118140960795 + 6894083 * 2 ^ 59
def prefixEnd_6894083 : Nat := 4983230072969 + 3 ^ 40 * 6894083 * 2
def baseEnd_6894083 : Nat := 1179992750330151867419065

theorem tailTrace_6894083 : CollatzResearch.WordTrace tailWord_6894083 prefixEnd_6894083 1179992750330151867419065 := by
  unfold tailWord_6894083
  simp only [CollatzResearch.WordTrace]
  refine ⟨251447864282922181482662903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167631909521948120988441935 251447864282922181482662903)
  ·
    refine ⟨377171796424383272223994355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251447864282922181482662903 377171796424383272223994355)
    ·
      refine ⟨565757694636574908335991533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377171796424383272223994355 565757694636574908335991533)
      ·
        refine ⟨212159135488715590625996825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 565757694636574908335991533 212159135488715590625996825)
        ·
          refine ⟨159119351616536692969497619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212159135488715590625996825 159119351616536692969497619)
          ·
            refine ⟨238679027424805039454246429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159119351616536692969497619 238679027424805039454246429)
            ·
              refine ⟨89504635284301889795342411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 238679027424805039454246429 89504635284301889795342411)
              ·
                refine ⟨134256952926452834693013617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89504635284301889795342411 134256952926452834693013617)
                ·
                  refine ⟨100692714694839626019760213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134256952926452834693013617 100692714694839626019760213)
                  ·
                    refine ⟨1179992750330151867419065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 100692714694839626019760213 1179992750330151867419065)
                    ·
                      rfl

theorem cell23_6894083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 8].length) (baseStart_6894083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6894083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6894083 prefixEnd_6894083 := by exact prefixLift 6894083
  have htrace : WordTrace (prefixWord ++ tailWord_6894083) baseStart_6894083 baseEnd_6894083 := by
    simpa [prefixWord, tailWord_6894083, baseEnd_6894083] using wordTrace_append hprefix tailTrace_6894083
  have hstable : (prefixWord ++ tailWord_6894083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6894083).length < 2 ^ (prefixWord ++ tailWord_6894083).sum := by decide
  have hdescent : baseEnd_6894083 < baseStart_6894083 := by decide
  rcases family_descends (prefixWord ++ tailWord_6894083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6894090 : List Nat := [3, 1, 2, 2, 2, 1, 1, 3, 1, 3, 4]
def baseStart_6894090 : Nat := 118140960795 + 6894090 * 2 ^ 59
def prefixEnd_6894090 : Nat := 4983230072969 + 3 ^ 40 * 6894090 * 2
def baseEnd_6894090 : Nat := 3539981845355037074869663

theorem tailTrace_6894090 : CollatzResearch.WordTrace tailWord_6894090 prefixEnd_6894090 3539981845355037074869663 := by
  unfold tailWord_6894090
  simp only [CollatzResearch.WordTrace]
  refine ⟨62862029898474205419541931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167632079729264547785445149 62862029898474205419541931)
  ·
    refine ⟨94293044847711308129312897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62862029898474205419541931 94293044847711308129312897)
    ·
      refine ⟨70719783635783481096984673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94293044847711308129312897 70719783635783481096984673)
      ·
        refine ⟨53039837726837610822738505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70719783635783481096984673 53039837726837610822738505)
        ·
          refine ⟨39779878295128208117053879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53039837726837610822738505 39779878295128208117053879)
          ·
            refine ⟨59669817442692312175580819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39779878295128208117053879 59669817442692312175580819)
            ·
              refine ⟨89504726164038468263371229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59669817442692312175580819 89504726164038468263371229)
              ·
                refine ⟨33564272311514425598764211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89504726164038468263371229 33564272311514425598764211)
                ·
                  refine ⟨50346408467271638398146317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33564272311514425598764211 50346408467271638398146317)
                  ·
                    refine ⟨18879903175226864399304869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50346408467271638398146317 18879903175226864399304869)
                    ·
                      refine ⟨3539981845355037074869663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18879903175226864399304869 3539981845355037074869663)
                      ·
                        rfl

theorem cell23_6894090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_6894090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6894090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6894090 prefixEnd_6894090 := by exact prefixLift 6894090
  have htrace : WordTrace (prefixWord ++ tailWord_6894090) baseStart_6894090 baseEnd_6894090 := by
    simpa [prefixWord, tailWord_6894090, baseEnd_6894090] using wordTrace_append hprefix tailTrace_6894090
  have hstable : (prefixWord ++ tailWord_6894090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6894090).length < 2 ^ (prefixWord ++ tailWord_6894090).sum := by decide
  have hdescent : baseEnd_6894090 < baseStart_6894090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6894090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6894117 : List Nat := [1, 3, 1, 2, 2, 1, 5, 1, 3, 4]
def baseStart_6894117 : Nat := 118140960795 + 6894117 * 2 ^ 59
def prefixEnd_6894117 : Nat := 4983230072969 + 3 ^ 40 * 6894117 * 2
def baseEnd_6894117 : Nat := 1179998569777569489744013

theorem tailTrace_6894117 : CollatzResearch.WordTrace tailWord_6894117 prefixEnd_6894117 1179998569777569489744013 := by
  unfold tailWord_6894117
  simp only [CollatzResearch.WordTrace]
  refine ⟨251449104364799005289400605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167632736243199336859600403 251449104364799005289400605)
  ·
    refine ⟨94293414136799626983525227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251449104364799005289400605 94293414136799626983525227)
    ·
      refine ⟨141440121205199440475287841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94293414136799626983525227 141440121205199440475287841)
      ·
        refine ⟨106080090903899580356465881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141440121205199440475287841 106080090903899580356465881)
        ·
          refine ⟨79560068177924685267349411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106080090903899580356465881 79560068177924685267349411)
          ·
            refine ⟨119340102266887027901024117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79560068177924685267349411 119340102266887027901024117)
            ·
              refine ⟨11188134587520658865721011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119340102266887027901024117 11188134587520658865721011)
              ·
                refine ⟨16782201881280988298581517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11188134587520658865721011 16782201881280988298581517)
                ·
                  refine ⟨6293325705480370611968069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16782201881280988298581517 6293325705480370611968069)
                  ·
                    refine ⟨1179998569777569489744013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6293325705480370611968069 1179998569777569489744013)
                    ·
                      rfl

theorem cell23_6894117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 3, 4].length) (baseStart_6894117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6894117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6894117 prefixEnd_6894117 := by exact prefixLift 6894117
  have htrace : WordTrace (prefixWord ++ tailWord_6894117) baseStart_6894117 baseEnd_6894117 := by
    simpa [prefixWord, tailWord_6894117, baseEnd_6894117] using wordTrace_append hprefix tailTrace_6894117
  have hstable : (prefixWord ++ tailWord_6894117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6894117).length < 2 ^ (prefixWord ++ tailWord_6894117).sum := by decide
  have hdescent : baseEnd_6894117 < baseStart_6894117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6894117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6894200 : List Nat := [2, 1, 2, 1, 1, 1, 2, 4, 3, 1, 5]
def baseStart_6894200 : Nat := 118140960795 + 6894200 * 2 ^ 59
def prefixEnd_6894200 : Nat := 4983230072969 + 3 ^ 40 * 6894200 * 2
def baseEnd_6894200 : Nat := 3540038328227031644494157

theorem tailTrace_6894200 : CollatzResearch.WordTrace tailWord_6894200 prefixEnd_6894200 3540038328227031644494157 := by
  unfold tailWord_6894200
  simp only [CollatzResearch.WordTrace]
  refine ⟨125726065811749155232336027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167634754415665540309781369 125726065811749155232336027)
  ·
    refine ⟨188589098717623732848504041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125726065811749155232336027 188589098717623732848504041)
    ·
      refine ⟨141441824038217799636378031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188589098717623732848504041 141441824038217799636378031)
      ·
        refine ⟨212162736057326699454567047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141441824038217799636378031 212162736057326699454567047)
        ·
          refine ⟨318244104085990049181850571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212162736057326699454567047 318244104085990049181850571)
          ·
            refine ⟨477366156128985073772775857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318244104085990049181850571 477366156128985073772775857)
            ·
              refine ⟨358024617096738805329581893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 477366156128985073772775857 358024617096738805329581893)
              ·
                refine ⟨67129615705638525999296605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 358024617096738805329581893 67129615705638525999296605)
                ·
                  refine ⟨25173605889614447249736227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67129615705638525999296605 25173605889614447249736227)
                  ·
                    refine ⟨37760408834421670874604341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25173605889614447249736227 37760408834421670874604341)
                    ·
                      refine ⟨3540038328227031644494157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37760408834421670874604341 3540038328227031644494157)
                      ·
                        rfl

theorem cell23_6894200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 3, 1, 5].length) (baseStart_6894200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6894200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6894200 prefixEnd_6894200 := by exact prefixLift 6894200
  have htrace : WordTrace (prefixWord ++ tailWord_6894200) baseStart_6894200 baseEnd_6894200 := by
    simpa [prefixWord, tailWord_6894200, baseEnd_6894200] using wordTrace_append hprefix tailTrace_6894200
  have hstable : (prefixWord ++ tailWord_6894200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6894200).length < 2 ^ (prefixWord ++ tailWord_6894200).sum := by decide
  have hdescent : baseEnd_6894200 < baseStart_6894200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6894200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6894201 : List Nat := [1, 2, 1, 3, 3, 4, 1, 1, 2, 3, 2]
def baseStart_6894201 : Nat := 118140960795 + 6894201 * 2 ^ 59
def prefixEnd_6894201 : Nat := 4983230072969 + 3 ^ 40 * 6894201 * 2
def baseEnd_6894201 : Nat := 3540038841707686140581653

theorem tailTrace_6894201 : CollatzResearch.WordTrace tailWord_6894201 prefixEnd_6894201 3540038841707686140581653 := by
  unfold tailWord_6894201
  simp only [CollatzResearch.WordTrace]
  refine ⟨251452168096494687635458457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167634778730996458423638971 251452168096494687635458457)
  ·
    refine ⟨188589126072371015726593843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251452168096494687635458457 188589126072371015726593843)
    ·
      refine ⟨282883689108556523589890765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188589126072371015726593843 282883689108556523589890765)
      ·
        refine ⟨106081383415708696346209037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282883689108556523589890765 106081383415708696346209037)
        ·
          refine ⟨39780518780890761129828389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106081383415708696346209037 39780518780890761129828389)
          ·
            refine ⟨7458847271417017711842823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39780518780890761129828389 7458847271417017711842823)
            ·
              refine ⟨11188270907125526567764235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7458847271417017711842823 11188270907125526567764235)
              ·
                refine ⟨16782406360688289851646353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11188270907125526567764235 16782406360688289851646353)
                ·
                  refine ⟨12586804770516217388734765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16782406360688289851646353 12586804770516217388734765)
                  ·
                    refine ⟨4720051788943581520775537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12586804770516217388734765 4720051788943581520775537)
                    ·
                      refine ⟨3540038841707686140581653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4720051788943581520775537 3540038841707686140581653)
                      ·
                        rfl

theorem cell23_6894201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 2, 3, 2].length) (baseStart_6894201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6894201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6894201 prefixEnd_6894201 := by exact prefixLift 6894201
  have htrace : WordTrace (prefixWord ++ tailWord_6894201) baseStart_6894201 baseEnd_6894201 := by
    simpa [prefixWord, tailWord_6894201, baseEnd_6894201] using wordTrace_append hprefix tailTrace_6894201
  have hstable : (prefixWord ++ tailWord_6894201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6894201).length < 2 ^ (prefixWord ++ tailWord_6894201).sum := by decide
  have hdescent : baseEnd_6894201 < baseStart_6894201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6894201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6894231 : List Nat := [1, 1, 3, 3, 2, 1, 4, 1, 3, 2, 2]
def baseStart_6894231 : Nat := 118140960795 + 6894231 * 2 ^ 59
def prefixEnd_6894231 : Nat := 4983230072969 + 3 ^ 40 * 6894231 * 2
def baseEnd_6894231 : Nat := 3540054246127321023206515

theorem tailTrace_6894231 : CollatzResearch.WordTrace tailWord_6894231 prefixEnd_6894231 3540054246127321023206515 := by
  unfold tailWord_6894231
  simp only [CollatzResearch.WordTrace]
  refine ⟨251453262286386002759050547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167635508190924001839367031 251453262286386002759050547)
  ·
    refine ⟨377179893429579004138575821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251453262286386002759050547 377179893429579004138575821)
    ·
      refine ⟨141442460036092126551965933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377179893429579004138575821 141442460036092126551965933)
      ·
        refine ⟨53040922513534547456987225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141442460036092126551965933 53040922513534547456987225)
        ·
          refine ⟨39780691885150910592740419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53040922513534547456987225 39780691885150910592740419)
          ·
            refine ⟨59671037827726365889110629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39780691885150910592740419 59671037827726365889110629)
            ·
              refine ⟨11188319592698693604208243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59671037827726365889110629 11188319592698693604208243)
              ·
                refine ⟨16782479389048040406312365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11188319592698693604208243 16782479389048040406312365)
                ·
                  refine ⟨6293429770893015152367137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16782479389048040406312365 6293429770893015152367137)
                  ·
                    refine ⟨4720072328169761364275353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6293429770893015152367137 4720072328169761364275353)
                    ·
                      refine ⟨3540054246127321023206515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4720072328169761364275353 3540054246127321023206515)
                      ·
                        rfl

theorem cell23_6894231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 3, 2, 2].length) (baseStart_6894231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6894231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6894231 prefixEnd_6894231 := by exact prefixLift 6894231
  have htrace : WordTrace (prefixWord ++ tailWord_6894231) baseStart_6894231 baseEnd_6894231 := by
    simpa [prefixWord, tailWord_6894231, baseEnd_6894231] using wordTrace_append hprefix tailTrace_6894231
  have hstable : (prefixWord ++ tailWord_6894231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6894231).length < 2 ^ (prefixWord ++ tailWord_6894231).sum := by decide
  have hdescent : baseEnd_6894231 < baseStart_6894231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6894231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6894241 : List Nat := [1, 2, 3, 3, 4, 1, 1, 1, 1, 6]
def baseStart_6894241 : Nat := 118140960795 + 6894241 * 2 ^ 59
def prefixEnd_6894241 : Nat := 4983230072969 + 3 ^ 40 * 6894241 * 2
def baseEnd_6894241 : Nat := 1180019793644621994693823

theorem tailTrace_6894241 : CollatzResearch.WordTrace tailWord_6894241 prefixEnd_6894241 1180019793644621994693823 := by
  unfold tailWord_6894241
  simp only [CollatzResearch.WordTrace]
  refine ⟨251453627016349774466914577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167635751344233182977943051 251453627016349774466914577)
  ·
    refine ⟨188590220262262330850185933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251453627016349774466914577 188590220262262330850185933)
    ·
      refine ⟨70721332598348374068819725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188590220262262330850185933 70721332598348374068819725)
      ·
        refine ⟨26520499724380640275807397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70721332598348374068819725 26520499724380640275807397)
        ·
          refine ⟨4972593698321370051713887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26520499724380640275807397 4972593698321370051713887)
          ·
            refine ⟨7458890547482055077570831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4972593698321370051713887 7458890547482055077570831)
            ·
              refine ⟨11188335821223082616356247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7458890547482055077570831 11188335821223082616356247)
              ·
                refine ⟨16782503731834623924534371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11188335821223082616356247 16782503731834623924534371)
                ·
                  refine ⟨25173755597751935886801557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16782503731834623924534371 25173755597751935886801557)
                  ·
                    refine ⟨1180019793644621994693823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25173755597751935886801557 1180019793644621994693823)
                    ·
                      rfl

theorem cell23_6894241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 1, 6].length) (baseStart_6894241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6894241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6894241 prefixEnd_6894241 := by exact prefixLift 6894241
  have htrace : WordTrace (prefixWord ++ tailWord_6894241) baseStart_6894241 baseEnd_6894241 := by
    simpa [prefixWord, tailWord_6894241, baseEnd_6894241] using wordTrace_append hprefix tailTrace_6894241
  have hstable : (prefixWord ++ tailWord_6894241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6894241).length < 2 ^ (prefixWord ++ tailWord_6894241).sum := by decide
  have hdescent : baseEnd_6894241 < baseStart_6894241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6894241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6894254 : List Nat := [4, 1, 4, 1, 1, 2, 1, 9]
def baseStart_6894254 : Nat := 118140960795 + 6894254 * 2 ^ 59
def prefixEnd_6894254 : Nat := 4983230072969 + 3 ^ 40 * 6894254 * 2
def baseEnd_6894254 : Nat := 131113557636384238267367

theorem tailTrace_6894254 : CollatzResearch.WordTrace tailWord_6894254 prefixEnd_6894254 131113557636384238267367 := by
  unfold tailWord_6894254
  simp only [CollatzResearch.WordTrace]
  refine ⟨31431762645662834710892227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167636067443535118458091877 31431762645662834710892227)
  ·
    refine ⟨47147643968494252066338341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31431762645662834710892227 47147643968494252066338341)
    ·
      refine ⟨8840183244092672262438439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47147643968494252066338341 8840183244092672262438439)
      ·
        refine ⟨13260274866139008393657659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8840183244092672262438439 13260274866139008393657659)
        ·
          refine ⟨19890412299208512590486489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13260274866139008393657659 19890412299208512590486489)
          ·
            refine ⟨14917809224406384442864867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19890412299208512590486489 14917809224406384442864867)
            ·
              refine ⟨22376713836609576664297301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14917809224406384442864867 22376713836609576664297301)
              ·
                refine ⟨131113557636384238267367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22376713836609576664297301 131113557636384238267367)
                ·
                  rfl

theorem cell23_6894254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 9].length) (baseStart_6894254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6894254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6894254 prefixEnd_6894254 := by exact prefixLift 6894254
  have htrace : WordTrace (prefixWord ++ tailWord_6894254) baseStart_6894254 baseEnd_6894254 := by
    simpa [prefixWord, tailWord_6894254, baseEnd_6894254] using wordTrace_append hprefix tailTrace_6894254
  have hstable : (prefixWord ++ tailWord_6894254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6894254).length < 2 ^ (prefixWord ++ tailWord_6894254).sum := by decide
  have hdescent : baseEnd_6894254 < baseStart_6894254 := by decide
  rcases family_descends (prefixWord ++ tailWord_6894254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6894304 : List Nat := [2, 1, 1, 3, 1, 2, 1, 5, 1, 4, 2]
def baseStart_6894304 : Nat := 118140960795 + 6894304 * 2 ^ 59
def prefixEnd_6894304 : Nat := 4983230072969 + 3 ^ 40 * 6894304 * 2
def baseEnd_6894304 : Nat := 3540091730215099237593679

theorem tailTrace_6894304 : CollatzResearch.WordTrace tailWord_6894304 prefixEnd_6894304 3540091730215099237593679 := by
  unfold tailWord_6894304
  simp only [CollatzResearch.WordTrace]
  refine ⟨125727962407560768113228983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167637283210081024150971977 125727962407560768113228983)
  ·
    refine ⟨188591943611341152169843475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125727962407560768113228983 188591943611341152169843475)
    ·
      refine ⟨282887915417011728254765213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188591943611341152169843475 282887915417011728254765213)
      ·
        refine ⟨106082968281379398095536955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282887915417011728254765213 106082968281379398095536955)
        ·
          refine ⟨159124452422069097143305433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106082968281379398095536955 159124452422069097143305433)
          ·
            refine ⟨119343339316551822857479075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159124452422069097143305433 119343339316551822857479075)
            ·
              refine ⟨179015008974827734286218613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119343339316551822857479075 179015008974827734286218613)
              ·
                refine ⟨16782657091390100089332995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 179015008974827734286218613 16782657091390100089332995)
                ·
                  refine ⟨25173985637085150133999493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16782657091390100089332995 25173985637085150133999493)
                  ·
                    refine ⟨4720122306953465650124905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25173985637085150133999493 4720122306953465650124905)
                    ·
                      refine ⟨3540091730215099237593679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4720122306953465650124905 3540091730215099237593679)
                      ·
                        rfl

theorem cell23_6894304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 1, 4, 2].length) (baseStart_6894304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6894304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6894304 prefixEnd_6894304 := by exact prefixLift 6894304
  have htrace : WordTrace (prefixWord ++ tailWord_6894304) baseStart_6894304 baseEnd_6894304 := by
    simpa [prefixWord, tailWord_6894304, baseEnd_6894304] using wordTrace_append hprefix tailTrace_6894304
  have hstable : (prefixWord ++ tailWord_6894304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6894304).length < 2 ^ (prefixWord ++ tailWord_6894304).sum := by decide
  have hdescent : baseEnd_6894304 < baseStart_6894304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6894304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6894308 : List Nat := [2, 3, 1, 1, 1, 6, 1, 2, 1, 3, 2]
def baseStart_6894308 : Nat := 118140960795 + 6894308 * 2 ^ 59
def prefixEnd_6894308 : Nat := 4983230072969 + 3 ^ 40 * 6894308 * 2
def baseEnd_6894308 : Nat := 3540093784137717221943661

theorem tailTrace_6894308 : CollatzResearch.WordTrace tailWord_6894308 prefixEnd_6894308 3540093784137717221943661 := by
  unfold tailWord_6894308
  simp only [CollatzResearch.WordTrace]
  refine ⟨125728035353553522454801789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167637380471404696606402385 125728035353553522454801789)
  ·
    refine ⟨47148013257582570920550671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125728035353553522454801789 47148013257582570920550671)
    ·
      refine ⟨70722019886373856380826007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47148013257582570920550671 70722019886373856380826007)
      ·
        refine ⟨106083029829560784571239011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70722019886373856380826007 106083029829560784571239011)
        ·
          refine ⟨159124544744341176856858517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106083029829560784571239011 159124544744341176856858517)
          ·
            refine ⟨7458963034890992665165243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 159124544744341176856858517 7458963034890992665165243)
            ·
              refine ⟨11188444552336488997747865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7458963034890992665165243 11188444552336488997747865)
              ·
                refine ⟨8391333414252366748310899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11188444552336488997747865 8391333414252366748310899)
                ·
                  refine ⟨12587000121378550122466349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8391333414252366748310899 12587000121378550122466349)
                  ·
                    refine ⟨4720125045516956295924881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12587000121378550122466349 4720125045516956295924881)
                    ·
                      refine ⟨3540093784137717221943661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4720125045516956295924881 3540093784137717221943661)
                      ·
                        rfl

theorem cell23_6894308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 2, 1, 3, 2].length) (baseStart_6894308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6894308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6894308 prefixEnd_6894308 := by exact prefixLift 6894308
  have htrace : WordTrace (prefixWord ++ tailWord_6894308) baseStart_6894308 baseEnd_6894308 := by
    simpa [prefixWord, tailWord_6894308, baseEnd_6894308] using wordTrace_append hprefix tailTrace_6894308
  have hstable : (prefixWord ++ tailWord_6894308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6894308).length < 2 ^ (prefixWord ++ tailWord_6894308).sum := by decide
  have hdescent : baseEnd_6894308 < baseStart_6894308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6894308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6894357 : List Nat := [1, 3, 2, 1, 2, 2, 2, 2, 1, 7]
def baseStart_6894357 : Nat := 118140960795 + 6894357 * 2 ^ 59
def prefixEnd_6894357 : Nat := 4983230072969 + 3 ^ 40 * 6894357 * 2
def baseEnd_6894357 : Nat := 1180039648229929176743645

theorem tailTrace_6894357 : CollatzResearch.WordTrace tailWord_6894357 prefixEnd_6894357 1180039648229929176743645 := by
  unfold tailWord_6894357
  simp only [CollatzResearch.WordTrace]
  refine ⟨251457857883929526278137325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167638571922619684185424883 251457857883929526278137325)
  ·
    refine ⟨94296696706473572354301497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251457857883929526278137325 94296696706473572354301497)
    ·
      refine ⟨70722522529855179265726123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94296696706473572354301497 70722522529855179265726123)
      ·
        refine ⟨106083783794782768898589185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70722522529855179265726123 106083783794782768898589185)
        ·
          refine ⟨79562837846087076673941889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106083783794782768898589185 79562837846087076673941889)
          ·
            refine ⟨59672128384565307505456417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79562837846087076673941889 59672128384565307505456417)
            ·
              refine ⟨44754096288423980629092313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59672128384565307505456417 44754096288423980629092313)
              ·
                refine ⟨33565572216317985471819235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44754096288423980629092313 33565572216317985471819235)
                ·
                  refine ⟨50348358324476978207728853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33565572216317985471819235 50348358324476978207728853)
                  ·
                    refine ⟨1180039648229929176743645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50348358324476978207728853 1180039648229929176743645)
                    ·
                      rfl

theorem cell23_6894357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_6894357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6894357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6894357 prefixEnd_6894357 := by exact prefixLift 6894357
  have htrace : WordTrace (prefixWord ++ tailWord_6894357) baseStart_6894357 baseEnd_6894357 := by
    simpa [prefixWord, tailWord_6894357, baseEnd_6894357] using wordTrace_append hprefix tailTrace_6894357
  have hstable : (prefixWord ++ tailWord_6894357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6894357).length < 2 ^ (prefixWord ++ tailWord_6894357).sum := by decide
  have hdescent : baseEnd_6894357 < baseStart_6894357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6894357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6894377 : List Nat := [1, 2, 1, 1, 1, 1, 1, 7, 1, 3, 4]
def baseStart_6894377 : Nat := 118140960795 + 6894377 * 2 ^ 59
def prefixEnd_6894377 : Nat := 4983230072969 + 3 ^ 40 * 6894377 * 2
def baseEnd_6894377 : Nat := 3540129214302877451980843

theorem tailTrace_6894377 : CollatzResearch.WordTrace tailWord_6894377 prefixEnd_6894377 3540129214302877451980843 := by
  unfold tailWord_6894377
  simp only [CollatzResearch.WordTrace]
  refine ⟨251458587343857069693865385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167639058229238046462576923 251458587343857069693865385)
  ·
    refine ⟨188593940507892802270399039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251458587343857069693865385 188593940507892802270399039)
    ·
      refine ⟨282890910761839203405598559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188593940507892802270399039 282890910761839203405598559)
      ·
        refine ⟨424336366142758805108397839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282890910761839203405598559 424336366142758805108397839)
        ·
          refine ⟨636504549214138207662596759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424336366142758805108397839 636504549214138207662596759)
          ·
            refine ⟨954756823821207311493895139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 636504549214138207662596759 954756823821207311493895139)
            ·
              refine ⟨1432135235731810967240842709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 954756823821207311493895139 1432135235731810967240842709)
              ·
                refine ⟨33565669587464319544707251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1432135235731810967240842709 33565669587464319544707251)
                ·
                  refine ⟨50348504381196479317060877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33565669587464319544707251 50348504381196479317060877)
                  ·
                    refine ⟨18880689142948679743897829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50348504381196479317060877 18880689142948679743897829)
                    ·
                      refine ⟨3540129214302877451980843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18880689142948679743897829 3540129214302877451980843)
                      ·
                        rfl

theorem cell23_6894377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 3, 4].length) (baseStart_6894377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6894377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6894377 prefixEnd_6894377 := by exact prefixLift 6894377
  have htrace : WordTrace (prefixWord ++ tailWord_6894377) baseStart_6894377 baseEnd_6894377 := by
    simpa [prefixWord, tailWord_6894377, baseEnd_6894377] using wordTrace_append hprefix tailTrace_6894377
  have hstable : (prefixWord ++ tailWord_6894377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6894377).length < 2 ^ (prefixWord ++ tailWord_6894377).sum := by decide
  have hdescent : baseEnd_6894377 < baseStart_6894377 := by decide
  rcases family_descends (prefixWord ++ tailWord_6894377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6894407 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 6]
def baseStart_6894407 : Nat := 118140960795 + 6894407 * 2 ^ 59
def prefixEnd_6894407 : Nat := 4983230072969 + 3 ^ 40 * 6894407 * 2
def baseEnd_6894407 : Nat := 3540144618722512334605705

theorem tailTrace_6894407 : CollatzResearch.WordTrace tailWord_6894407 prefixEnd_6894407 3540144618722512334605705 := by
  unfold tailWord_6894407
  simp only [CollatzResearch.WordTrace]
  refine ⟨251459681533748384817457475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167639787689165589878304983 251459681533748384817457475)
  ·
    refine ⟨377189522300622577226186213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251459681533748384817457475 377189522300622577226186213)
    ·
      refine ⟨70723035431366733229909915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 377189522300622577226186213 70723035431366733229909915)
      ·
        refine ⟨106084553147050099844864873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70723035431366733229909915 106084553147050099844864873)
        ·
          refine ⟨79563414860287574883648655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106084553147050099844864873 79563414860287574883648655)
          ·
            refine ⟨119345122290431362325472983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79563414860287574883648655 119345122290431362325472983)
            ·
              refine ⟨179017683435647043488209475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119345122290431362325472983 179017683435647043488209475)
              ·
                refine ⟨268526525153470565232314213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179017683435647043488209475 268526525153470565232314213)
                ·
                  refine ⟨50348723466275730981058915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 268526525153470565232314213 50348723466275730981058915)
                  ·
                    refine ⟨75523085199413596471588373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50348723466275730981058915 75523085199413596471588373)
                    ·
                      refine ⟨3540144618722512334605705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75523085199413596471588373 3540144618722512334605705)
                      ·
                        rfl

theorem cell23_6894407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_6894407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6894407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6894407 prefixEnd_6894407 := by exact prefixLift 6894407
  have htrace : WordTrace (prefixWord ++ tailWord_6894407) baseStart_6894407 baseEnd_6894407 := by
    simpa [prefixWord, tailWord_6894407, baseEnd_6894407] using wordTrace_append hprefix tailTrace_6894407
  have hstable : (prefixWord ++ tailWord_6894407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6894407).length < 2 ^ (prefixWord ++ tailWord_6894407).sum := by decide
  have hdescent : baseEnd_6894407 < baseStart_6894407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6894407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6894521 : List Nat := [1, 2, 1, 4, 2, 2, 1, 2, 3, 2, 3]
def baseStart_6894521 : Nat := 118140960795 + 6894521 * 2 ^ 59
def prefixEnd_6894521 : Nat := 4983230072969 + 3 ^ 40 * 6894521 * 2
def baseEnd_6894521 : Nat := 3540203155517124888580181

theorem tailTrace_6894521 : CollatzResearch.WordTrace tailWord_6894521 prefixEnd_6894521 3540203155517124888580181 := by
  unfold tailWord_6894521
  simp only [CollatzResearch.WordTrace]
  refine ⟨251463839455335382287107417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167642559636890254858071611 251463839455335382287107417)
  ·
    refine ⟨188597879591501536715330563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251463839455335382287107417 188597879591501536715330563)
    ·
      refine ⟨282896819387252305072995845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188597879591501536715330563 282896819387252305072995845)
      ·
        refine ⟨53043153635109807201186721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 282896819387252305072995845 53043153635109807201186721)
        ·
          refine ⟨39782365226332355400890041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53043153635109807201186721 39782365226332355400890041)
          ·
            refine ⟨29836773919749266550667531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39782365226332355400890041 29836773919749266550667531)
            ·
              refine ⟨44755160879623899826001297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29836773919749266550667531 44755160879623899826001297)
              ·
                refine ⟨33566370659717924869500973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44755160879623899826001297 33566370659717924869500973)
                ·
                  refine ⟨12587388997394221826062865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33566370659717924869500973 12587388997394221826062865)
                  ·
                    refine ⟨9440541748045666369547149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12587388997394221826062865 9440541748045666369547149)
                    ·
                      refine ⟨3540203155517124888580181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9440541748045666369547149 3540203155517124888580181)
                      ·
                        rfl

theorem cell23_6894521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_6894521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6894521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6894521 prefixEnd_6894521 := by exact prefixLift 6894521
  have htrace : WordTrace (prefixWord ++ tailWord_6894521) baseStart_6894521 baseEnd_6894521 := by
    simpa [prefixWord, tailWord_6894521, baseEnd_6894521] using wordTrace_append hprefix tailTrace_6894521
  have hstable : (prefixWord ++ tailWord_6894521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6894521).length < 2 ^ (prefixWord ++ tailWord_6894521).sum := by decide
  have hdescent : baseEnd_6894521 < baseStart_6894521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6894521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6894552 : List Nat := [2, 1, 2, 2, 2, 4, 2, 3, 1, 2, 2]
def baseStart_6894552 : Nat := 118140960795 + 6894552 * 2 ^ 59
def prefixEnd_6894552 : Nat := 4983230072969 + 3 ^ 40 * 6894552 * 2
def baseEnd_6894552 : Nat := 3540219073417414267292539

theorem tailTrace_6894552 : CollatzResearch.WordTrace tailWord_6894552 prefixEnd_6894552 3540219073417414267292539 := by
  unfold tailWord_6894552
  simp only [CollatzResearch.WordTrace]
  refine ⟨125732485059111537290742955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167643313412148716387657273 125732485059111537290742955)
  ·
    refine ⟨188598727588667305936114433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125732485059111537290742955 188598727588667305936114433)
    ·
      refine ⟨141449045691500479452085825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188598727588667305936114433 141449045691500479452085825)
      ·
        refine ⟨106086784268625359589064369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141449045691500479452085825 106086784268625359589064369)
        ·
          refine ⟨79565088201469019691798277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106086784268625359589064369 79565088201469019691798277)
          ·
            refine ⟨14918454037775441192212177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79565088201469019691798277 14918454037775441192212177)
            ·
              refine ⟨11188840528331580894159133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14918454037775441192212177 11188840528331580894159133)
              ·
                refine ⟨4195815198124342835309675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11188840528331580894159133 4195815198124342835309675)
                ·
                  refine ⟨6293722797186514252964513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4195815198124342835309675 6293722797186514252964513)
                  ·
                    refine ⟨4720292097889885689723385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6293722797186514252964513 4720292097889885689723385)
                    ·
                      refine ⟨3540219073417414267292539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4720292097889885689723385 3540219073417414267292539)
                      ·
                        rfl

theorem cell23_6894552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 3, 1, 2, 2].length) (baseStart_6894552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6894552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6894552 prefixEnd_6894552 := by exact prefixLift 6894552
  have htrace : WordTrace (prefixWord ++ tailWord_6894552) baseStart_6894552 baseEnd_6894552 := by
    simpa [prefixWord, tailWord_6894552, baseEnd_6894552] using wordTrace_append hprefix tailTrace_6894552
  have hstable : (prefixWord ++ tailWord_6894552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6894552).length < 2 ^ (prefixWord ++ tailWord_6894552).sum := by decide
  have hdescent : baseEnd_6894552 < baseStart_6894552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6894552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6894562 : List Nat := [3, 3, 3, 1, 1, 3, 1, 2, 2, 4]
def baseStart_6894562 : Nat := 118140960795 + 6894562 * 2 ^ 59
def prefixEnd_6894562 : Nat := 4983230072969 + 3 ^ 40 * 6894562 * 2
def baseEnd_6894562 : Nat := 1180074736074653076055831

theorem tailTrace_6894562 : CollatzResearch.WordTrace tailWord_6894562 prefixEnd_6894562 1180074736074653076055831 := by
  unfold tailWord_6894562
  simp only [CollatzResearch.WordTrace]
  refine ⟨62866333712046711572337485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167643556565457897526233293 62866333712046711572337485)
  ·
    refine ⟨23574875142017516839626557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62866333712046711572337485 23574875142017516839626557)
    ·
      refine ⟨8840578178256568814859959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23574875142017516839626557 8840578178256568814859959)
      ·
        refine ⟨13260867267384853222289939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8840578178256568814859959 13260867267384853222289939)
        ·
          refine ⟨19891300901077279833434909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13260867267384853222289939 19891300901077279833434909)
          ·
            refine ⟨7459237837903979937538091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19891300901077279833434909 7459237837903979937538091)
            ·
              refine ⟨11188856756855969906307137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7459237837903979937538091 11188856756855969906307137)
              ·
                refine ⟨8391642567641977429730353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11188856756855969906307137 8391642567641977429730353)
                ·
                  refine ⟨6293731925731483072297765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8391642567641977429730353 6293731925731483072297765)
                  ·
                    refine ⟨1180074736074653076055831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6293731925731483072297765 1180074736074653076055831)
                    ·
                      rfl

theorem cell23_6894562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_6894562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6894562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6894562 prefixEnd_6894562 := by exact prefixLift 6894562
  have htrace : WordTrace (prefixWord ++ tailWord_6894562) baseStart_6894562 baseEnd_6894562 := by
    simpa [prefixWord, tailWord_6894562, baseEnd_6894562] using wordTrace_append hprefix tailTrace_6894562
  have hstable : (prefixWord ++ tailWord_6894562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6894562).length < 2 ^ (prefixWord ++ tailWord_6894562).sum := by decide
  have hdescent : baseEnd_6894562 < baseStart_6894562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6894562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6894564 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 4, 2, 5]
def baseStart_6894564 : Nat := 118140960795 + 6894564 * 2 ^ 59
def prefixEnd_6894564 : Nat := 4983230072969 + 3 ^ 40 * 6894564 * 2
def baseEnd_6894564 : Nat := 3540225235185268220342483

theorem tailTrace_6894564 : CollatzResearch.WordTrace tailWord_6894564 prefixEnd_6894564 3540225235185268220342483 := by
  unfold tailWord_6894564
  simp only [CollatzResearch.WordTrace]
  refine ⟨125732703897089800315461373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167643605196119733753948497 125732703897089800315461373)
  ·
    refine ⟨47149763961408675118298015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125732703897089800315461373 47149763961408675118298015)
    ·
      refine ⟨70724645942113012677447023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47149763961408675118298015 70724645942113012677447023)
      ·
        refine ⟨106086968913169519016170535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70724645942113012677447023 106086968913169519016170535)
        ·
          refine ⟨159130453369754278524255803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106086968913169519016170535 159130453369754278524255803)
          ·
            refine ⟨238695680054631417786383705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159130453369754278524255803 238695680054631417786383705)
            ·
              refine ⟨179021760040973563339787779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238695680054631417786383705 179021760040973563339787779)
              ·
                refine ⟨268532640061460345009681669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179021760040973563339787779 268532640061460345009681669)
                ·
                  refine ⟨50349870011523814689315313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 268532640061460345009681669 50349870011523814689315313)
                  ·
                    refine ⟨37762402508642861016986485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50349870011523814689315313 37762402508642861016986485)
                    ·
                      refine ⟨3540225235185268220342483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37762402508642861016986485 3540225235185268220342483)
                      ·
                        rfl

theorem cell23_6894564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_6894564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6894564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6894564 prefixEnd_6894564 := by exact prefixLift 6894564
  have htrace : WordTrace (prefixWord ++ tailWord_6894564) baseStart_6894564 baseEnd_6894564 := by
    simpa [prefixWord, tailWord_6894564, baseEnd_6894564] using wordTrace_append hprefix tailTrace_6894564
  have hstable : (prefixWord ++ tailWord_6894564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6894564).length < 2 ^ (prefixWord ++ tailWord_6894564).sum := by decide
  have hdescent : baseEnd_6894564 < baseStart_6894564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6894564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6894585 : List Nat := [1, 2, 1, 3, 1, 3, 5, 1, 2, 1, 3]
def baseStart_6894585 : Nat := 118140960795 + 6894585 * 2 ^ 59
def prefixEnd_6894585 : Nat := 4983230072969 + 3 ^ 40 * 6894585 * 2
def baseEnd_6894585 : Nat := 3540236018279012638179887

theorem tailTrace_6894585 : CollatzResearch.WordTrace tailWord_6894585 prefixEnd_6894585 3540236018279012638179887 := by
  unfold tailWord_6894585
  simp only [CollatzResearch.WordTrace]
  refine ⟨251466173727103521217437209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167644115818069014144958139 251466173727103521217437209)
  ·
    refine ⟨188599630295327640913077907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251466173727103521217437209 188599630295327640913077907)
    ·
      refine ⟨282899445442991461369616861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188599630295327640913077907 282899445442991461369616861)
      ·
        refine ⟨106087292041121798013606323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282899445442991461369616861 106087292041121798013606323)
        ·
          refine ⟨159130938061682697020409485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106087292041121798013606323 159130938061682697020409485)
          ·
            refine ⟨59674101773131011382653557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159130938061682697020409485 59674101773131011382653557)
            ·
              refine ⟨5594447041231032317123771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59674101773131011382653557 5594447041231032317123771)
              ·
                refine ⟨8391670561846548475685657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5594447041231032317123771 8391670561846548475685657)
                ·
                  refine ⟨6293752921384911356764243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8391670561846548475685657 6293752921384911356764243)
                  ·
                    refine ⟨9440629382077367035146365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6293752921384911356764243 9440629382077367035146365)
                    ·
                      refine ⟨3540236018279012638179887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9440629382077367035146365 3540236018279012638179887)
                      ·
                        rfl

theorem cell23_6894585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 1, 2, 1, 3].length) (baseStart_6894585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6894585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6894585 prefixEnd_6894585 := by exact prefixLift 6894585
  have htrace : WordTrace (prefixWord ++ tailWord_6894585) baseStart_6894585 baseEnd_6894585 := by
    simpa [prefixWord, tailWord_6894585, baseEnd_6894585] using wordTrace_append hprefix tailTrace_6894585
  have hstable : (prefixWord ++ tailWord_6894585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6894585).length < 2 ^ (prefixWord ++ tailWord_6894585).sum := by decide
  have hdescent : baseEnd_6894585 < baseStart_6894585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6894585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6894625 : List Nat := [1, 2, 3, 2, 3, 1, 2, 1, 4, 2, 2]
def baseStart_6894625 : Nat := 118140960795 + 6894625 * 2 ^ 59
def prefixEnd_6894625 : Nat := 4983230072969 + 3 ^ 40 * 6894625 * 2
def baseEnd_6894625 : Nat := 3540256557505192481679703

theorem tailTrace_6894625 : CollatzResearch.WordTrace tailWord_6894625 prefixEnd_6894625 3540256557505192481679703 := by
  unfold tailWord_6894625
  simp only [CollatzResearch.WordTrace]
  refine ⟨251467632646958608048893329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167645088431305738699262219 251467632646958608048893329)
  ·
    refine ⟨188600724485218956036669997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251467632646958608048893329 188600724485218956036669997)
    ·
      refine ⟨70725271681957108513751249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188600724485218956036669997 70725271681957108513751249)
      ·
        refine ⟨53043953761467831385313437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70725271681957108513751249 53043953761467831385313437)
        ·
          refine ⟨19891482660550436769492539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53043953761467831385313437 19891482660550436769492539)
          ·
            refine ⟨29837223990825655154238809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19891482660550436769492539 29837223990825655154238809)
            ·
              refine ⟨22377917993119241365679107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29837223990825655154238809 22377917993119241365679107)
              ·
                refine ⟨33566876989678862048518661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22377917993119241365679107 33566876989678862048518661)
                ·
                  refine ⟨6293789435564786634097249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33566876989678862048518661 6293789435564786634097249)
                  ·
                    refine ⟨4720342076673589975572937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6293789435564786634097249 4720342076673589975572937)
                    ·
                      refine ⟨3540256557505192481679703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4720342076673589975572937 3540256557505192481679703)
                      ·
                        rfl

theorem cell23_6894625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 4, 2, 2].length) (baseStart_6894625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6894625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6894625 prefixEnd_6894625 := by exact prefixLift 6894625
  have htrace : WordTrace (prefixWord ++ tailWord_6894625) baseStart_6894625 baseEnd_6894625 := by
    simpa [prefixWord, tailWord_6894625, baseEnd_6894625] using wordTrace_append hprefix tailTrace_6894625
  have hstable : (prefixWord ++ tailWord_6894625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6894625).length < 2 ^ (prefixWord ++ tailWord_6894625).sum := by decide
  have hdescent : baseEnd_6894625 < baseStart_6894625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6894625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6894641 : List Nat := [1, 2, 2, 3, 1, 2, 2, 1, 1, 5, 3]
def baseStart_6894641 : Nat := 118140960795 + 6894641 * 2 ^ 59
def prefixEnd_6894641 : Nat := 4983230072969 + 3 ^ 40 * 6894641 * 2
def baseEnd_6894641 : Nat := 3540264773195664419079629

theorem tailTrace_6894641 : CollatzResearch.WordTrace tailWord_6894641 prefixEnd_6894641 3540264773195664419079629 := by
  unfold tailWord_6894641
  simp only [CollatzResearch.WordTrace]
  refine ⟨251468216214900642781475777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167645477476600428520983851 251468216214900642781475777)
  ·
    refine ⟨188601162161175482086106833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251468216214900642781475777 188601162161175482086106833)
    ·
      refine ⟨141450871620881611564580125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188601162161175482086106833 141450871620881611564580125)
      ·
        refine ⟨53044076857830604336717547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141450871620881611564580125 53044076857830604336717547)
        ·
          refine ⟨79566115286745906505076321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53044076857830604336717547 79566115286745906505076321)
          ·
            refine ⟨59674586465059429878807241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79566115286745906505076321 59674586465059429878807241)
            ·
              refine ⟨44755939848794572409105431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59674586465059429878807241 44755939848794572409105431)
              ·
                refine ⟨67133909773191858613658147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44755939848794572409105431 67133909773191858613658147)
                ·
                  refine ⟨100700864659787787920487221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67133909773191858613658147 100700864659787787920487221)
                  ·
                    refine ⟨9440706061855105117545677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 100700864659787787920487221 9440706061855105117545677)
                    ·
                      refine ⟨3540264773195664419079629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9440706061855105117545677 3540264773195664419079629)
                      ·
                        rfl

theorem cell23_6894641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_6894641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6894641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6894641 prefixEnd_6894641 := by exact prefixLift 6894641
  have htrace : WordTrace (prefixWord ++ tailWord_6894641) baseStart_6894641 baseEnd_6894641 := by
    simpa [prefixWord, tailWord_6894641, baseEnd_6894641] using wordTrace_append hprefix tailTrace_6894641
  have hstable : (prefixWord ++ tailWord_6894641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6894641).length < 2 ^ (prefixWord ++ tailWord_6894641).sum := by decide
  have hdescent : baseEnd_6894641 < baseStart_6894641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6894641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6894661 : List Nat := [1, 3, 1, 1, 1, 3, 3, 3, 2, 5]
def baseStart_6894661 : Nat := 118140960795 + 6894661 * 2 ^ 59
def prefixEnd_6894661 : Nat := 4983230072969 + 3 ^ 40 * 6894661 * 2
def baseEnd_6894661 : Nat := 1180091680936251446943179

theorem tailTrace_6894661 : CollatzResearch.WordTrace tailWord_6894661 prefixEnd_6894661 1180091680936251446943179 := by
  unfold tailWord_6894661
  simp only [CollatzResearch.WordTrace]
  refine ⟨251468945674828186197203837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167645963783218790798135891 251468945674828186197203837)
  ·
    refine ⟨94300854628060569823951439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251468945674828186197203837 94300854628060569823951439)
    ·
      refine ⟨141451281942090854735927159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94300854628060569823951439 141451281942090854735927159)
      ·
        refine ⟨212176922913136282103890739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141451281942090854735927159 212176922913136282103890739)
        ·
          refine ⟨318265384369704423155836109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212176922913136282103890739 318265384369704423155836109)
          ·
            refine ⟨119349519138639158683438541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 318265384369704423155836109 119349519138639158683438541)
            ·
              refine ⟨44756069676989684506289453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119349519138639158683438541 44756069676989684506289453)
              ·
                refine ⟨16783526128871131689858545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44756069676989684506289453 16783526128871131689858545)
                ·
                  refine ⟨12587644596653348767393909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16783526128871131689858545 12587644596653348767393909)
                  ·
                    refine ⟨1180091680936251446943179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12587644596653348767393909 1180091680936251446943179)
                    ·
                      rfl

theorem cell23_6894661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2, 5].length) (baseStart_6894661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6894661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6894661 prefixEnd_6894661 := by exact prefixLift 6894661
  have htrace : WordTrace (prefixWord ++ tailWord_6894661) baseStart_6894661 baseEnd_6894661 := by
    simpa [prefixWord, tailWord_6894661, baseEnd_6894661] using wordTrace_append hprefix tailTrace_6894661
  have hstable : (prefixWord ++ tailWord_6894661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6894661).length < 2 ^ (prefixWord ++ tailWord_6894661).sum := by decide
  have hdescent : baseEnd_6894661 < baseStart_6894661 := by decide
  rcases family_descends (prefixWord ++ tailWord_6894661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6894681 : List Nat := [1, 2, 1, 2, 2, 1, 2, 3, 4, 1, 4]
def baseStart_6894681 : Nat := 118140960795 + 6894681 * 2 ^ 59
def prefixEnd_6894681 : Nat := 4983230072969 + 3 ^ 40 * 6894681 * 2
def baseEnd_6894681 : Nat := 3540285312421844262579445

theorem tailTrace_6894681 : CollatzResearch.WordTrace tailWord_6894681 prefixEnd_6894681 3540285312421844262579445 := by
  unfold tailWord_6894681
  simp only [CollatzResearch.WordTrace]
  refine ⟨251469675134755729612931897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167646450089837153075287931 251469675134755729612931897)
  ·
    refine ⟨188602256351066797209698923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251469675134755729612931897 188602256351066797209698923)
    ·
      refine ⟨282903384526600195814548385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188602256351066797209698923 282903384526600195814548385)
      ·
        refine ⟨212177538394950146860911289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282903384526600195814548385 212177538394950146860911289)
        ·
          refine ⟨159133153796212610145683467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212177538394950146860911289 159133153796212610145683467)
          ·
            refine ⟨238699730694318915218525201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159133153796212610145683467 238699730694318915218525201)
            ·
              refine ⟨179024798020739186413893901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238699730694318915218525201 179024798020739186413893901)
              ·
                refine ⟨67134299257777194905210213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179024798020739186413893901 67134299257777194905210213)
                ·
                  refine ⟨12587681110833224044726915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67134299257777194905210213 12587681110833224044726915)
                  ·
                    refine ⟨18881521666249836067090373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12587681110833224044726915 18881521666249836067090373)
                    ·
                      refine ⟨3540285312421844262579445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18881521666249836067090373 3540285312421844262579445)
                      ·
                        rfl

theorem cell23_6894681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4, 1, 4].length) (baseStart_6894681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6894681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6894681 prefixEnd_6894681 := by exact prefixLift 6894681
  have htrace : WordTrace (prefixWord ++ tailWord_6894681) baseStart_6894681 baseEnd_6894681 := by
    simpa [prefixWord, tailWord_6894681, baseEnd_6894681] using wordTrace_append hprefix tailTrace_6894681
  have hstable : (prefixWord ++ tailWord_6894681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6894681).length < 2 ^ (prefixWord ++ tailWord_6894681).sum := by decide
  have hdescent : baseEnd_6894681 < baseStart_6894681 := by decide
  rcases family_descends (prefixWord ++ tailWord_6894681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6894731 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 1, 7, 3]
def baseStart_6894731 : Nat := 118140960795 + 6894731 * 2 ^ 59
def prefixEnd_6894731 : Nat := 4983230072969 + 3 ^ 40 * 6894731 * 2
def baseEnd_6894731 : Nat := 3540310986454569066954215

theorem tailTrace_6894731 : CollatzResearch.WordTrace tailWord_6894731 prefixEnd_6894731 3540310986454569066954215 := by
  unfold tailWord_6894731
  simp only [CollatzResearch.WordTrace]
  refine ⟨251471498784574588152252047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167647665856383058768168031 251471498784574588152252047)
  ·
    refine ⟨377207248176861882228378071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251471498784574588152252047 377207248176861882228378071)
    ·
      refine ⟨565810872265292823342567107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377207248176861882228378071 565810872265292823342567107)
      ·
        refine ⟨848716308397939235013850661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565810872265292823342567107 848716308397939235013850661)
        ·
          refine ⟨159134307824613606565096999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 848716308397939235013850661 159134307824613606565096999)
          ·
            refine ⟨238701461736920409847645499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159134307824613606565096999 238701461736920409847645499)
            ·
              refine ⟨358052192605380614771468249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238701461736920409847645499 358052192605380614771468249)
              ·
                refine ⟨268539144454035461078601187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 358052192605380614771468249 268539144454035461078601187)
                ·
                  refine ⟨402808716681053191617901781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 268539144454035461078601187 402808716681053191617901781)
                  ·
                    refine ⟨9440829297212184178544573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 402808716681053191617901781 9440829297212184178544573)
                    ·
                      refine ⟨3540310986454569066954215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9440829297212184178544573 3540310986454569066954215)
                      ·
                        rfl

theorem cell23_6894731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 7, 3].length) (baseStart_6894731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6894731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6894731 prefixEnd_6894731 := by exact prefixLift 6894731
  have htrace : WordTrace (prefixWord ++ tailWord_6894731) baseStart_6894731 baseEnd_6894731 := by
    simpa [prefixWord, tailWord_6894731, baseEnd_6894731] using wordTrace_append hprefix tailTrace_6894731
  have hstable : (prefixWord ++ tailWord_6894731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6894731).length < 2 ^ (prefixWord ++ tailWord_6894731).sum := by decide
  have hdescent : baseEnd_6894731 < baseStart_6894731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6894731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6894738 : List Nat := [3, 2, 3, 1, 1, 3, 1, 1, 8]
def baseStart_6894738 : Nat := 118140960795 + 6894738 * 2 ^ 59
def prefixEnd_6894738 : Nat := 4983230072969 + 3 ^ 40 * 6894738 * 2
def baseEnd_6894738 : Nat := 393368286757683393285187

theorem tailTrace_6894738 : CollatzResearch.WordTrace tailWord_6894738 prefixEnd_6894738 393368286757683393285187 := by
  unfold tailWord_6894738
  simp only [CollatzResearch.WordTrace]
  refine ⟨62867938523887307086939217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167647836063699485565171245 62867938523887307086939217)
  ·
    refine ⟨47150953892915480315204413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62867938523887307086939217 47150953892915480315204413)
    ·
      refine ⟨17681607709843305118201655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47150953892915480315204413 17681607709843305118201655)
      ·
        refine ⟨26522411564764957677302483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17681607709843305118201655 26522411564764957677302483)
        ·
          refine ⟨39783617347147436515953725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26522411564764957677302483 39783617347147436515953725)
          ·
            refine ⟨14918856505180288693482647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39783617347147436515953725 14918856505180288693482647)
            ·
              refine ⟨22378284757770433040223971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14918856505180288693482647 22378284757770433040223971)
              ·
                refine ⟨33567427136655649560335957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22378284757770433040223971 33567427136655649560335957)
                ·
                  refine ⟨393368286757683393285187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33567427136655649560335957 393368286757683393285187)
                  ·
                    rfl

theorem cell23_6894738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 8].length) (baseStart_6894738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6894738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6894738 prefixEnd_6894738 := by exact prefixLift 6894738
  have htrace : WordTrace (prefixWord ++ tailWord_6894738) baseStart_6894738 baseEnd_6894738 := by
    simpa [prefixWord, tailWord_6894738, baseEnd_6894738] using wordTrace_append hprefix tailTrace_6894738
  have hstable : (prefixWord ++ tailWord_6894738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6894738).length < 2 ^ (prefixWord ++ tailWord_6894738).sum := by decide
  have hdescent : baseEnd_6894738 < baseStart_6894738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6894738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6894775 : List Nat := [1, 1, 3, 1, 4, 1, 2, 3, 2, 3, 2]
def baseStart_6894775 : Nat := 118140960795 + 6894775 * 2 ^ 59
def prefixEnd_6894775 : Nat := 4983230072969 + 3 ^ 40 * 6894775 * 2
def baseEnd_6894775 : Nat := 3540333579603366894804013

theorem tailTrace_6894775 : CollatzResearch.WordTrace tailWord_6894775 prefixEnd_6894775 3540333579603366894804013 := by
  unfold tailWord_6894775
  simp only [CollatzResearch.WordTrace]
  refine ⟨251473103596415183666853779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167648735730943455777902519 251473103596415183666853779)
  ·
    refine ⟨377209655394622775500280669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251473103596415183666853779 377209655394622775500280669)
    ·
      refine ⟨141453620772983540812605251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377209655394622775500280669 141453620772983540812605251)
      ·
        refine ⟨212180431159475311218907877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141453620772983540812605251 212180431159475311218907877)
        ·
          refine ⟨39783830842401620853545227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212180431159475311218907877 39783830842401620853545227)
          ·
            refine ⟨59675746263602431280317841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39783830842401620853545227 59675746263602431280317841)
            ·
              refine ⟨44756809697701823460238381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59675746263602431280317841 44756809697701823460238381)
              ·
                refine ⟨16783803636638183797589393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44756809697701823460238381 16783803636638183797589393)
                ·
                  refine ⟨12587852727478637848192045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16783803636638183797589393 12587852727478637848192045)
                  ·
                    refine ⟨4720444772804489193072017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12587852727478637848192045 4720444772804489193072017)
                    ·
                      refine ⟨3540333579603366894804013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4720444772804489193072017 3540333579603366894804013)
                      ·
                        rfl

theorem cell23_6894775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2, 3, 2].length) (baseStart_6894775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6894775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6894775 prefixEnd_6894775 := by exact prefixLift 6894775
  have htrace : WordTrace (prefixWord ++ tailWord_6894775) baseStart_6894775 baseEnd_6894775 := by
    simpa [prefixWord, tailWord_6894775, baseEnd_6894775] using wordTrace_append hprefix tailTrace_6894775
  have hstable : (prefixWord ++ tailWord_6894775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6894775).length < 2 ^ (prefixWord ++ tailWord_6894775).sum := by decide
  have hdescent : baseEnd_6894775 < baseStart_6894775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6894775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6894806 : List Nat := [5, 2, 1, 2, 3, 1, 2, 1, 6]
def baseStart_6894806 : Nat := 118140960795 + 6894806 * 2 ^ 59
def prefixEnd_6894806 : Nat := 4983230072969 + 3 ^ 40 * 6894806 * 2
def baseEnd_6894806 : Nat := 393372166389295141501819

theorem tailTrace_6894806 : CollatzResearch.WordTrace tailWord_6894806 prefixEnd_6894806 393372166389295141501819 := by
  unfold tailWord_6894806
  simp only [CollatzResearch.WordTrace]
  refine ⟨15717139641206429747577017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167649489506201917307488181 15717139641206429747577017)
  ·
    refine ⟨11787854730904822310682763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15717139641206429747577017 11787854730904822310682763)
    ·
      refine ⟨17681782096357233466024145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11787854730904822310682763 17681782096357233466024145)
      ·
        refine ⟨13261336572267925099518109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17681782096357233466024145 13261336572267925099518109)
        ·
          refine ⟨4973001214600471912319291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13261336572267925099518109 4973001214600471912319291)
          ·
            refine ⟨7459501821900707868478937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4973001214600471912319291 7459501821900707868478937)
            ·
              refine ⟨5594626366425530901359203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7459501821900707868478937 5594626366425530901359203)
              ·
                refine ⟨8391939549638296352038805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5594626366425530901359203 8391939549638296352038805)
                ·
                  refine ⟨393372166389295141501819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8391939549638296352038805 393372166389295141501819)
                  ·
                    rfl

theorem cell23_6894806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_6894806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6894806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6894806 prefixEnd_6894806 := by exact prefixLift 6894806
  have htrace : WordTrace (prefixWord ++ tailWord_6894806) baseStart_6894806 baseEnd_6894806 := by
    simpa [prefixWord, tailWord_6894806, baseEnd_6894806] using wordTrace_append hprefix tailTrace_6894806
  have hstable : (prefixWord ++ tailWord_6894806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6894806).length < 2 ^ (prefixWord ++ tailWord_6894806).sum := by decide
  have hdescent : baseEnd_6894806 < baseStart_6894806 := by decide
  rcases family_descends (prefixWord ++ tailWord_6894806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6894842 : List Nat := [3, 1, 1, 1, 1, 4, 5, 1, 1, 2, 3]
def baseStart_6894842 : Nat := 118140960795 + 6894842 * 2 ^ 59
def prefixEnd_6894842 : Nat := 4983230072969 + 3 ^ 40 * 6894842 * 2
def baseEnd_6894842 : Nat := 3540367982807218132666205

theorem tailTrace_6894842 : CollatzResearch.WordTrace tailWord_6894842 prefixEnd_6894842 3540367982807218132666205 := by
  unfold tailWord_6894842
  simp only [CollatzResearch.WordTrace]
  refine ⟨62868886821793113527385695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167650364858114969406361853 62868886821793113527385695)
  ·
    refine ⟨94303330232689670291078543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62868886821793113527385695 94303330232689670291078543)
    ·
      refine ⟨141454995349034505436617815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94303330232689670291078543 141454995349034505436617815)
      ·
        refine ⟨212182493023551758154926723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141454995349034505436617815 212182493023551758154926723)
        ·
          refine ⟨318273739535327637232390085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212182493023551758154926723 318273739535327637232390085)
          ·
            refine ⟨59676326162873931981073141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 318273739535327637232390085 59676326162873931981073141)
            ·
              refine ⟨5594655577769431123225607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59676326162873931981073141 5594655577769431123225607)
              ·
                refine ⟨8391983366654146684838411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5594655577769431123225607 8391983366654146684838411)
                ·
                  refine ⟨12587975049981220027257617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8391983366654146684838411 12587975049981220027257617)
                  ·
                    refine ⟨9440981287485915020443213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12587975049981220027257617 9440981287485915020443213)
                    ·
                      refine ⟨3540367982807218132666205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9440981287485915020443213 3540367982807218132666205)
                      ·
                        rfl

theorem cell23_6894842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 1, 1, 2, 3].length) (baseStart_6894842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6894842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6894842 prefixEnd_6894842 := by exact prefixLift 6894842
  have htrace : WordTrace (prefixWord ++ tailWord_6894842) baseStart_6894842 baseEnd_6894842 := by
    simpa [prefixWord, tailWord_6894842, baseEnd_6894842] using wordTrace_append hprefix tailTrace_6894842
  have hstable : (prefixWord ++ tailWord_6894842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6894842).length < 2 ^ (prefixWord ++ tailWord_6894842).sum := by decide
  have hdescent : baseEnd_6894842 < baseStart_6894842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6894842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6894850 : List Nat := [3, 4, 1, 1, 4, 1, 2, 2, 1, 1, 3]
def baseStart_6894850 : Nat := 118140960795 + 6894850 * 2 ^ 59
def prefixEnd_6894850 : Nat := 4983230072969 + 3 ^ 40 * 6894850 * 2
def baseEnd_6894850 : Nat := 3540372090652454101366169

theorem tailTrace_6894850 : CollatzResearch.WordTrace tailWord_6894850 prefixEnd_6894850 3540372090652454101366169 := by
  unfold tailWord_6894850
  simp only [CollatzResearch.WordTrace]
  refine ⟨62868959767785867868958501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167650559380762314317222669 62868959767785867868958501)
  ·
    refine ⟨11787929956459850225429719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62868959767785867868958501 11787929956459850225429719)
    ·
      refine ⟨17681894934689775338144579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11787929956459850225429719 17681894934689775338144579)
      ·
        refine ⟨26522842402034663007216869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17681894934689775338144579 26522842402034663007216869)
        ·
          refine ⟨4973032950381499313853163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26522842402034663007216869 4973032950381499313853163)
          ·
            refine ⟨7459549425572248970779745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4973032950381499313853163 7459549425572248970779745)
            ·
              refine ⟨5594662069179186728084809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7459549425572248970779745 5594662069179186728084809)
              ·
                refine ⟨4195996551884390046063607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5594662069179186728084809 4195996551884390046063607)
                ·
                  refine ⟨6293994827826585069095411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4195996551884390046063607 6293994827826585069095411)
                  ·
                    refine ⟨9440992241739877603643117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6293994827826585069095411 9440992241739877603643117)
                    ·
                      refine ⟨3540372090652454101366169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9440992241739877603643117 3540372090652454101366169)
                      ·
                        rfl

theorem cell23_6894850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_6894850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6894850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6894850 prefixEnd_6894850 := by exact prefixLift 6894850
  have htrace : WordTrace (prefixWord ++ tailWord_6894850) baseStart_6894850 baseEnd_6894850 := by
    simpa [prefixWord, tailWord_6894850, baseEnd_6894850] using wordTrace_append hprefix tailTrace_6894850
  have hstable : (prefixWord ++ tailWord_6894850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6894850).length < 2 ^ (prefixWord ++ tailWord_6894850).sum := by decide
  have hdescent : baseEnd_6894850 < baseStart_6894850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6894850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6894856 : List Nat := [2, 1, 3, 2, 4, 1, 1, 4, 1, 2, 2]
def baseStart_6894856 : Nat := 118140960795 + 6894856 * 2 ^ 59
def prefixEnd_6894856 : Nat := 4983230072969 + 3 ^ 40 * 6894856 * 2
def baseEnd_6894856 : Nat := 3540375171536381077891141

theorem tailTrace_6894856 : CollatzResearch.WordTrace tailWord_6894856 prefixEnd_6894856 3540375171536381077891141 := by
  unfold tailWord_6894856
  simp only [CollatzResearch.WordTrace]
  refine ⟨125738028954560867250276211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167650705272747823000368281 125738028954560867250276211)
  ·
    refine ⟨188607043431841300875414317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125738028954560867250276211 188607043431841300875414317)
    ·
      refine ⟨70727641286940487828280369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188607043431841300875414317 70727641286940487828280369)
      ·
        refine ⟨53045730965205365871210277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70727641286940487828280369 53045730965205365871210277)
        ·
          refine ⟨9946074555976006100851927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53045730965205365871210277 9946074555976006100851927)
          ·
            refine ⟨14919111833964009151277891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9946074555976006100851927 14919111833964009151277891)
            ·
              refine ⟨22378667750946013726916837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14919111833964009151277891 22378667750946013726916837)
              ·
                refine ⟨4196000203302377573796907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22378667750946013726916837 4196000203302377573796907)
                ·
                  refine ⟨6294000304953566360695361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4196000203302377573796907 6294000304953566360695361)
                  ·
                    refine ⟨4720500228715174770521521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6294000304953566360695361 4720500228715174770521521)
                    ·
                      refine ⟨3540375171536381077891141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4720500228715174770521521 3540375171536381077891141)
                      ·
                        rfl

theorem cell23_6894856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 4, 1, 2, 2].length) (baseStart_6894856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6894856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6894856 prefixEnd_6894856 := by exact prefixLift 6894856
  have htrace : WordTrace (prefixWord ++ tailWord_6894856) baseStart_6894856 baseEnd_6894856 := by
    simpa [prefixWord, tailWord_6894856, baseEnd_6894856] using wordTrace_append hprefix tailTrace_6894856
  have hstable : (prefixWord ++ tailWord_6894856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6894856).length < 2 ^ (prefixWord ++ tailWord_6894856).sum := by decide
  have hdescent : baseEnd_6894856 < baseStart_6894856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6894856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6894865 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 5, 3, 2]
def baseStart_6894865 : Nat := 118140960795 + 6894865 * 2 ^ 59
def prefixEnd_6894865 : Nat := 4983230072969 + 3 ^ 40 * 6894865 * 2
def baseEnd_6894865 : Nat := 3540379792862271542678599

theorem tailTrace_6894865 : CollatzResearch.WordTrace tailWord_6894865 prefixEnd_6894865 3540379792862271542678599 := by
  unfold tailWord_6894865
  simp only [CollatzResearch.WordTrace]
  refine ⟨251476386166089129037630049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167650924110726086025086699 251476386166089129037630049)
  ·
    refine ⟨188607289624566846778222537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251476386166089129037630049 188607289624566846778222537)
    ·
      refine ⟨141455467218425135083666903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188607289624566846778222537 141455467218425135083666903)
      ·
        refine ⟨212183200827637702625500355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141455467218425135083666903 212183200827637702625500355)
        ·
          refine ⟨318274801241456553938250533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212183200827637702625500355 318274801241456553938250533)
          ·
            refine ⟨59676525232773103863421975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 318274801241456553938250533 59676525232773103863421975)
            ·
              refine ⟨89514787849159655795132963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59676525232773103863421975 89514787849159655795132963)
              ·
                refine ⟨134272181773739483692699445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89514787849159655795132963 134272181773739483692699445)
                ·
                  refine ⟨12588017041288076596190573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134272181773739483692699445 12588017041288076596190573)
                  ·
                    refine ⟨4720506390483028723571465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12588017041288076596190573 4720506390483028723571465)
                    ·
                      refine ⟨3540379792862271542678599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4720506390483028723571465 3540379792862271542678599)
                      ·
                        rfl

theorem cell23_6894865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 3, 2].length) (baseStart_6894865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6894865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6894865 prefixEnd_6894865 := by exact prefixLift 6894865
  have htrace : WordTrace (prefixWord ++ tailWord_6894865) baseStart_6894865 baseEnd_6894865 := by
    simpa [prefixWord, tailWord_6894865, baseEnd_6894865] using wordTrace_append hprefix tailTrace_6894865
  have hstable : (prefixWord ++ tailWord_6894865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6894865).length < 2 ^ (prefixWord ++ tailWord_6894865).sum := by decide
  have hdescent : baseEnd_6894865 < baseStart_6894865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6894865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6894872 : List Nat := [2, 1, 2, 3, 1, 3, 2, 3, 2, 1, 3]
def baseStart_6894872 : Nat := 118140960795 + 6894872 * 2 ^ 59
def prefixEnd_6894872 : Nat := 4983230072969 + 3 ^ 40 * 6894872 * 2
def baseEnd_6894872 : Nat := 3540383387226853015291067

theorem tailTrace_6894872 : CollatzResearch.WordTrace tailWord_6894872 prefixEnd_6894872 3540383387226853015291067 := by
  unfold tailWord_6894872
  simp only [CollatzResearch.WordTrace]
  refine ⟨125738320738531884616567435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167651094318042512822089913 125738320738531884616567435)
  ·
    refine ⟨188607481107797826924851153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125738320738531884616567435 188607481107797826924851153)
    ·
      refine ⟨141455610830848370193638365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188607481107797826924851153 141455610830848370193638365)
      ·
        refine ⟨53045854061568138822614387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141455610830848370193638365 53045854061568138822614387)
        ·
          refine ⟨79568781092352208233921581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53045854061568138822614387 79568781092352208233921581)
          ·
            refine ⟨29838292909632078087720593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79568781092352208233921581 29838292909632078087720593)
            ·
              refine ⟨22378719682224058565790445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29838292909632078087720593 22378719682224058565790445)
              ·
                refine ⟨8392019880834021962171417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22378719682224058565790445 8392019880834021962171417)
                ·
                  refine ⟨6294014910625516471628563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8392019880834021962171417 6294014910625516471628563)
                  ·
                    refine ⟨9441022365938274707442845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6294014910625516471628563 9441022365938274707442845)
                    ·
                      refine ⟨3540383387226853015291067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9441022365938274707442845 3540383387226853015291067)
                      ·
                        rfl

theorem cell23_6894872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_6894872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6894872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6894872 prefixEnd_6894872 := by exact prefixLift 6894872
  have htrace : WordTrace (prefixWord ++ tailWord_6894872) baseStart_6894872 baseEnd_6894872 := by
    simpa [prefixWord, tailWord_6894872, baseEnd_6894872] using wordTrace_append hprefix tailTrace_6894872
  have hstable : (prefixWord ++ tailWord_6894872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6894872).length < 2 ^ (prefixWord ++ tailWord_6894872).sum := by decide
  have hdescent : baseEnd_6894872 < baseStart_6894872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6894872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6894899 : List Nat := [1, 1, 1, 2, 5, 2, 4, 1, 1, 3, 2]
def baseStart_6894899 : Nat := 118140960795 + 6894899 * 2 ^ 59
def prefixEnd_6894899 : Nat := 4983230072969 + 3 ^ 40 * 6894899 * 2
def baseEnd_6894899 : Nat := 3540397251204524409653443

theorem tailTrace_6894899 : CollatzResearch.WordTrace tailWord_6894899 prefixEnd_6894899 3540397251204524409653443 := by
  unfold tailWord_6894899
  simp only [CollatzResearch.WordTrace]
  refine ⟨251477626247965952844367751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167651750831977301896245167 251477626247965952844367751)
  ·
    refine ⟨377216439371948929266551627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251477626247965952844367751 377216439371948929266551627)
    ·
      refine ⟨565824659057923393899827441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377216439371948929266551627 565824659057923393899827441)
      ·
        refine ⟨424368494293442545424870581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 565824659057923393899827441 424368494293442545424870581)
        ·
          refine ⟨39784546340010238633581617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 424368494293442545424870581 39784546340010238633581617)
          ·
            refine ⟨29838409755007678975186213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39784546340010238633581617 29838409755007678975186213)
            ·
              refine ⟨5594701829063939807847415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29838409755007678975186213 5594701829063939807847415)
              ·
                refine ⟨8392052743595909711771123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5594701829063939807847415 8392052743595909711771123)
                ·
                  refine ⟨12588079115393864567656685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8392052743595909711771123 12588079115393864567656685)
                  ·
                    refine ⟨4720529668272699212871257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12588079115393864567656685 4720529668272699212871257)
                    ·
                      refine ⟨3540397251204524409653443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4720529668272699212871257 3540397251204524409653443)
                      ·
                        rfl

theorem cell23_6894899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 1, 1, 3, 2].length) (baseStart_6894899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6894899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6894899 prefixEnd_6894899 := by exact prefixLift 6894899
  have htrace : WordTrace (prefixWord ++ tailWord_6894899) baseStart_6894899 baseEnd_6894899 := by
    simpa [prefixWord, tailWord_6894899, baseEnd_6894899] using wordTrace_append hprefix tailTrace_6894899
  have hstable : (prefixWord ++ tailWord_6894899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6894899).length < 2 ^ (prefixWord ++ tailWord_6894899).sum := by decide
  have hdescent : baseEnd_6894899 < baseStart_6894899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6894899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6894912 : List Nat := [2, 1, 1, 2, 2, 1, 5, 1, 4, 2, 2]
def baseStart_6894912 : Nat := 118140960795 + 6894912 * 2 ^ 59
def prefixEnd_6894912 : Nat := 4983230072969 + 3 ^ 40 * 6894912 * 2
def baseEnd_6894912 : Nat := 3540403926453032858790883

theorem tailTrace_6894912 : CollatzResearch.WordTrace tailWord_6894912 prefixEnd_6894912 3540403926453032858790883 := by
  unfold tailWord_6894912
  simp only [CollatzResearch.WordTrace]
  refine ⟨125739050198459428032295495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167652066931279237376393993 125739050198459428032295495)
  ·
    refine ⟨188608575297689142048443243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125739050198459428032295495 188608575297689142048443243)
    ·
      refine ⟨282912862946533713072664865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188608575297689142048443243 282912862946533713072664865)
      ·
        refine ⟨212184647209900284804498649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282912862946533713072664865 212184647209900284804498649)
        ·
          refine ⟨159138485407425213603373987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212184647209900284804498649 159138485407425213603373987)
          ·
            refine ⟨238707728111137820405060981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159138485407425213603373987 238707728111137820405060981)
            ·
              refine ⟨22378849510419170662974467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 238707728111137820405060981 22378849510419170662974467)
              ·
                refine ⟨33568274265628755994461701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22378849510419170662974467 33568274265628755994461701)
                ·
                  refine ⟨6294051424805391748961569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33568274265628755994461701 6294051424805391748961569)
                  ·
                    refine ⟨4720538568604043811721177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6294051424805391748961569 4720538568604043811721177)
                    ·
                      refine ⟨3540403926453032858790883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4720538568604043811721177 3540403926453032858790883)
                      ·
                        rfl

theorem cell23_6894912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 4, 2, 2].length) (baseStart_6894912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6894912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6894912 prefixEnd_6894912 := by exact prefixLift 6894912
  have htrace : WordTrace (prefixWord ++ tailWord_6894912) baseStart_6894912 baseEnd_6894912 := by
    simpa [prefixWord, tailWord_6894912, baseEnd_6894912] using wordTrace_append hprefix tailTrace_6894912
  have hstable : (prefixWord ++ tailWord_6894912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6894912).length < 2 ^ (prefixWord ++ tailWord_6894912).sum := by decide
  have hdescent : baseEnd_6894912 < baseStart_6894912 := by decide
  rcases family_descends (prefixWord ++ tailWord_6894912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6894968 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 2, 7, 4]
def baseStart_6894968 : Nat := 118140960795 + 6894968 * 2 ^ 59
def prefixEnd_6894968 : Nat := 4983230072969 + 3 ^ 40 * 6894968 * 2
def baseEnd_6894968 : Nat := 3540432681369684639690625

theorem tailTrace_6894968 : CollatzResearch.WordTrace tailWord_6894968 prefixEnd_6894968 3540432681369684639690625 := by
  unfold tailWord_6894968
  simp only [CollatzResearch.WordTrace]
  refine ⟨125740071442357988814314779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167653428589810651752419705 125740071442357988814314779)
  ·
    refine ⟨188610107163536983221472169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125740071442357988814314779 188610107163536983221472169)
    ·
      refine ⟨141457580372652737416104127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188610107163536983221472169 141457580372652737416104127)
      ·
        refine ⟨212186370558979106124156191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141457580372652737416104127 212186370558979106124156191)
        ·
          refine ⟨318279555838468659186234287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212186370558979106124156191 318279555838468659186234287)
          ·
            refine ⟨477419333757702988779351431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318279555838468659186234287 477419333757702988779351431)
            ·
              refine ⟨716129000636554483169027147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 477419333757702988779351431 716129000636554483169027147)
              ·
                refine ⟨1074193500954831724753540721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 716129000636554483169027147 1074193500954831724753540721)
                ·
                  refine ⟨805645125716123793565155541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1074193500954831724753540721 805645125716123793565155541)
                  ·
                    refine ⟨18882307633971651411683333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 805645125716123793565155541 18882307633971651411683333)
                    ·
                      refine ⟨3540432681369684639690625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18882307633971651411683333 3540432681369684639690625)
                      ·
                        rfl

theorem cell23_6894968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 7, 4].length) (baseStart_6894968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6894968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6894968 prefixEnd_6894968 := by exact prefixLift 6894968
  have htrace : WordTrace (prefixWord ++ tailWord_6894968) baseStart_6894968 baseEnd_6894968 := by
    simpa [prefixWord, tailWord_6894968, baseEnd_6894968] using wordTrace_append hprefix tailTrace_6894968
  have hstable : (prefixWord ++ tailWord_6894968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6894968).length < 2 ^ (prefixWord ++ tailWord_6894968).sum := by decide
  have hdescent : baseEnd_6894968 < baseStart_6894968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6894968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895002 : List Nat := [3, 1, 1, 4, 1, 1, 4, 1, 2, 1, 4]
def baseStart_6895002 : Nat := 118140960795 + 6895002 * 2 ^ 59
def prefixEnd_6895002 : Nat := 4983230072969 + 3 ^ 40 * 6895002 * 2
def baseEnd_6895002 : Nat := 3540450139711937506665469

theorem tailTrace_6895002 : CollatzResearch.WordTrace tailWord_6895002 prefixEnd_6895002 3540450139711937506665469 := by
  unfold tailWord_6895002
  simp only [CollatzResearch.WordTrace]
  refine ⟨62870345741648200358841815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167654255311061867623578173 62870345741648200358841815)
  ·
    refine ⟨94305518612472300538262723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62870345741648200358841815 94305518612472300538262723)
    ·
      refine ⟨141458277918708450807394085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94305518612472300538262723 141458277918708450807394085)
      ·
        refine ⟨26523427109757834526386391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141458277918708450807394085 26523427109757834526386391)
        ·
          refine ⟨39785140664636751789579587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26523427109757834526386391 39785140664636751789579587)
          ·
            refine ⟨59677710996955127684369381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39785140664636751789579587 59677710996955127684369381)
            ·
              refine ⟨11189570811929086440819259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59677710996955127684369381 11189570811929086440819259)
              ·
                refine ⟨16784356217893629661228889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11189570811929086440819259 16784356217893629661228889)
                ·
                  refine ⟨12588267163420222245921667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16784356217893629661228889 12588267163420222245921667)
                  ·
                    refine ⟨18882400745130333368882501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12588267163420222245921667 18882400745130333368882501)
                    ·
                      refine ⟨3540450139711937506665469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18882400745130333368882501 3540450139711937506665469)
                      ·
                        rfl

theorem cell23_6895002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_6895002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895002 prefixEnd_6895002 := by exact prefixLift 6895002
  have htrace : WordTrace (prefixWord ++ tailWord_6895002) baseStart_6895002 baseEnd_6895002 := by
    simpa [prefixWord, tailWord_6895002, baseEnd_6895002] using wordTrace_append hprefix tailTrace_6895002
  have hstable : (prefixWord ++ tailWord_6895002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895002).length < 2 ^ (prefixWord ++ tailWord_6895002).sum := by decide
  have hdescent : baseEnd_6895002 < baseStart_6895002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895015 : List Nat := [1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 6]
def baseStart_6895015 : Nat := 118140960795 + 6895015 * 2 ^ 59
def prefixEnd_6895015 : Nat := 4983230072969 + 3 ^ 40 * 6895015 * 2
def baseEnd_6895015 : Nat := 3540456814960445955802909

theorem tailTrace_6895015 : CollatzResearch.WordTrace tailWord_6895015 prefixEnd_6895015 3540456814960445955802909 := by
  unfold tailWord_6895015
  simp only [CollatzResearch.WordTrace]
  refine ⟨251481857115545704655590499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167654571410363803103726999 251481857115545704655590499)
  ·
    refine ⟨377222785673318556983385749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251481857115545704655590499 377222785673318556983385749)
    ·
      refine ⟨17682318078436807358596207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 377222785673318556983385749 17682318078436807358596207)
      ·
        refine ⟨26523477117655211037894311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17682318078436807358596207 26523477117655211037894311)
        ·
          refine ⟨39785215676482816556841467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26523477117655211037894311 39785215676482816556841467)
          ·
            refine ⟨59677823514724224835262201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39785215676482816556841467 59677823514724224835262201)
            ·
              refine ⟨44758367636043168626446651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59677823514724224835262201 44758367636043168626446651)
              ·
                refine ⟨67137551454064752939669977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44758367636043168626446651 67137551454064752939669977)
                ·
                  refine ⟨50353163590548564704752483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67137551454064752939669977 50353163590548564704752483)
                  ·
                    refine ⟨75529745385822847057128725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50353163590548564704752483 75529745385822847057128725)
                    ·
                      refine ⟨3540456814960445955802909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75529745385822847057128725 3540456814960445955802909)
                      ·
                        rfl

theorem cell23_6895015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_6895015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895015 prefixEnd_6895015 := by exact prefixLift 6895015
  have htrace : WordTrace (prefixWord ++ tailWord_6895015) baseStart_6895015 baseEnd_6895015 := by
    simpa [prefixWord, tailWord_6895015, baseEnd_6895015] using wordTrace_append hprefix tailTrace_6895015
  have hstable : (prefixWord ++ tailWord_6895015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895015).length < 2 ^ (prefixWord ++ tailWord_6895015).sum := by decide
  have hdescent : baseEnd_6895015 < baseStart_6895015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895055 : List Nat := [1, 1, 2, 1, 1, 4, 4, 1, 3, 5]
def baseStart_6895055 : Nat := 118140960795 + 6895055 * 2 ^ 59
def prefixEnd_6895055 : Nat := 4983230072969 + 3 ^ 40 * 6895055 * 2
def baseEnd_6895055 : Nat := 1180159118062208599767575

theorem tailTrace_6895055 : CollatzResearch.WordTrace tailWord_6895055 prefixEnd_6895055 1180159118062208599767575 := by
  unfold tailWord_6895055
  simp only [CollatzResearch.WordTrace]
  refine ⟨251483316035400791487046619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167655544023600527658031079 251483316035400791487046619)
  ·
    refine ⟨377224974053101187230569929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251483316035400791487046619 377224974053101187230569929)
    ·
      refine ⟨282918730539825890422927447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377224974053101187230569929 282918730539825890422927447)
      ·
        refine ⟨424378095809738835634391171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282918730539825890422927447 424378095809738835634391171)
        ·
          refine ⟨636567143714608253451586757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424378095809738835634391171 636567143714608253451586757)
          ·
            refine ⟨119356339446489047522172517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 636567143714608253451586757 119356339446489047522172517)
            ·
              refine ⟨22379313646216696410407347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119356339446489047522172517 22379313646216696410407347)
              ·
                refine ⟨33568970469325044615611021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22379313646216696410407347 33568970469325044615611021)
                ·
                  refine ⟨12588363925996891730854133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33568970469325044615611021 12588363925996891730854133)
                  ·
                    refine ⟨1180159118062208599767575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12588363925996891730854133 1180159118062208599767575)
                    ·
                      rfl

theorem cell23_6895055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3, 5].length) (baseStart_6895055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895055 prefixEnd_6895055 := by exact prefixLift 6895055
  have htrace : WordTrace (prefixWord ++ tailWord_6895055) baseStart_6895055 baseEnd_6895055 := by
    simpa [prefixWord, tailWord_6895055, baseEnd_6895055] using wordTrace_append hprefix tailTrace_6895055
  have hstable : (prefixWord ++ tailWord_6895055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895055).length < 2 ^ (prefixWord ++ tailWord_6895055).sum := by decide
  have hdescent : baseEnd_6895055 < baseStart_6895055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895086 : List Nat := [4, 1, 2, 1, 2, 1, 1, 6, 1, 1, 3]
def baseStart_6895086 : Nat := 118140960795 + 6895086 * 2 ^ 59
def prefixEnd_6895086 : Nat := 4983230072969 + 3 ^ 40 * 6895086 * 2
def baseEnd_6895086 : Nat := 3540493272086915178015083

theorem tailTrace_6895086 : CollatzResearch.WordTrace tailWord_6895086 prefixEnd_6895086 3540493272086915178015083 := by
  unfold tailWord_6895086
  simp only [CollatzResearch.WordTrace]
  refine ⟨31435555837286060472678139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167656297798858989187616741 31435555837286060472678139)
  ·
    refine ⟨47153333755929090709017209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31435555837286060472678139 47153333755929090709017209)
    ·
      refine ⟨35365000316946818031762907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47153333755929090709017209 35365000316946818031762907)
      ·
        refine ⟨53047500475420227047644361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35365000316946818031762907 53047500475420227047644361)
        ·
          refine ⟨39785625356565170285733271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53047500475420227047644361 39785625356565170285733271)
          ·
            refine ⟨59678438034847755428599907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39785625356565170285733271 59678438034847755428599907)
            ·
              refine ⟨89517657052271633142899861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59678438034847755428599907 89517657052271633142899861)
              ·
                refine ⟨4196140174325232803573431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89517657052271633142899861 4196140174325232803573431)
                ·
                  refine ⟨6294210261487849205360147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4196140174325232803573431 6294210261487849205360147)
                  ·
                    refine ⟨9441315392231773808040221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6294210261487849205360147 9441315392231773808040221)
                    ·
                      refine ⟨3540493272086915178015083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9441315392231773808040221 3540493272086915178015083)
                      ·
                        rfl

theorem cell23_6895086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 6, 1, 1, 3].length) (baseStart_6895086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895086 prefixEnd_6895086 := by exact prefixLift 6895086
  have htrace : WordTrace (prefixWord ++ tailWord_6895086) baseStart_6895086 baseEnd_6895086 := by
    simpa [prefixWord, tailWord_6895086, baseEnd_6895086] using wordTrace_append hprefix tailTrace_6895086
  have hstable : (prefixWord ++ tailWord_6895086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895086).length < 2 ^ (prefixWord ++ tailWord_6895086).sum := by decide
  have hdescent : baseEnd_6895086 < baseStart_6895086 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895095 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 2, 6, 3]
def baseStart_6895095 : Nat := 118140960795 + 6895095 * 2 ^ 59
def prefixEnd_6895095 : Nat := 4983230072969 + 3 ^ 40 * 6895095 * 2
def baseEnd_6895095 : Nat := 3540497893412805642802541

theorem tailTrace_6895095 : CollatzResearch.WordTrace tailWord_6895095 prefixEnd_6895095 3540497893412805642802541 := by
  unfold tailWord_6895095
  simp only [CollatzResearch.WordTrace]
  refine ⟨251484774955255878318502739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167656516636837252212335159 251484774955255878318502739)
  ·
    refine ⟨377227162432883817477754109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251484774955255878318502739 377227162432883817477754109)
    ·
      refine ⟨141460185912331431554157791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377227162432883817477754109 141460185912331431554157791)
      ·
        refine ⟨212190278868497147331236687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141460185912331431554157791 212190278868497147331236687)
        ·
          refine ⟨318285418302745720996855031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212190278868497147331236687 318285418302745720996855031)
          ·
            refine ⟨477428127454118581495282547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318285418302745720996855031 477428127454118581495282547)
            ·
              refine ⟨716142191181177872242923821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 477428127454118581495282547 716142191181177872242923821)
              ·
                refine ⟨268553321692941702091096433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 716142191181177872242923821 268553321692941702091096433)
                ·
                  refine ⟨201414991269706276568322325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 268553321692941702091096433 201414991269706276568322325)
                  ·
                    refine ⟨9441327715767481714140109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 201414991269706276568322325 9441327715767481714140109)
                    ·
                      refine ⟨3540497893412805642802541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9441327715767481714140109 3540497893412805642802541)
                      ·
                        rfl

theorem cell23_6895095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 6, 3].length) (baseStart_6895095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895095 prefixEnd_6895095 := by exact prefixLift 6895095
  have htrace : WordTrace (prefixWord ++ tailWord_6895095) baseStart_6895095 baseEnd_6895095 := by
    simpa [prefixWord, tailWord_6895095, baseEnd_6895095] using wordTrace_append hprefix tailTrace_6895095
  have hstable : (prefixWord ++ tailWord_6895095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895095).length < 2 ^ (prefixWord ++ tailWord_6895095).sum := by decide
  have hdescent : baseEnd_6895095 < baseStart_6895095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895106 : List Nat := [3, 4, 1, 2, 1, 2, 2, 2, 1, 5]
def baseStart_6895106 : Nat := 118140960795 + 6895106 * 2 ^ 59
def prefixEnd_6895106 : Nat := 4983230072969 + 3 ^ 40 * 6895106 * 2
def baseEnd_6895106 : Nat := 1180167847233335033254997

theorem tailTrace_6895106 : CollatzResearch.WordTrace tailWord_6895106 prefixEnd_6895106 1180167847233335033254997 := by
  unfold tailWord_6895106
  simp only [CollatzResearch.WordTrace]
  refine ⟨62871294039554006799288293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167656784105477351464768781 62871294039554006799288293)
  ·
    refine ⟨11788367632416376274866555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62871294039554006799288293 11788367632416376274866555)
    ·
      refine ⟨17682551448624564412299833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11788367632416376274866555 17682551448624564412299833)
      ·
        refine ⟨13261913586468423309224875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17682551448624564412299833 13261913586468423309224875)
        ·
          refine ⟨19892870379702634963837313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13261913586468423309224875 19892870379702634963837313)
          ·
            refine ⟨14919652784776976222877985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19892870379702634963837313 14919652784776976222877985)
            ·
              refine ⟨11189739588582732167158489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14919652784776976222877985 11189739588582732167158489)
              ·
                refine ⟨8392304691437049125368867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11189739588582732167158489 8392304691437049125368867)
                ·
                  refine ⟨12588457037155573688053301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8392304691437049125368867 12588457037155573688053301)
                  ·
                    refine ⟨1180167847233335033254997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12588457037155573688053301 1180167847233335033254997)
                    ·
                      rfl

theorem cell23_6895106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_6895106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895106 prefixEnd_6895106 := by exact prefixLift 6895106
  have htrace : WordTrace (prefixWord ++ tailWord_6895106) baseStart_6895106 baseEnd_6895106 := by
    simpa [prefixWord, tailWord_6895106, baseEnd_6895106] using wordTrace_append hprefix tailTrace_6895106
  have hstable : (prefixWord ++ tailWord_6895106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895106).length < 2 ^ (prefixWord ++ tailWord_6895106).sum := by decide
  have hdescent : baseEnd_6895106 < baseStart_6895106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895112 : List Nat := [2, 1, 3, 2, 1, 1, 2, 3, 3, 2, 3]
def baseStart_6895112 : Nat := 118140960795 + 6895112 * 2 ^ 59
def prefixEnd_6895112 : Nat := 4983230072969 + 3 ^ 40 * 6895112 * 2
def baseEnd_6895112 : Nat := 3540506622583932076289963

theorem tailTrace_6895112 : CollatzResearch.WordTrace tailWord_6895112 prefixEnd_6895112 3540506622583932076289963 := by
  unfold tailWord_6895112
  simp only [CollatzResearch.WordTrace]
  refine ⟨125742697498097145110935795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167656929997462860147914393 125742697498097145110935795)
  ·
    refine ⟨188614046247145717666403693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125742697498097145110935795 188614046247145717666403693)
    ·
      refine ⟨70730267342679644124901385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188614046247145717666403693 70730267342679644124901385)
      ·
        refine ⟨53047700507009733093676039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70730267342679644124901385 53047700507009733093676039)
        ·
          refine ⟨79571550760514599640514059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53047700507009733093676039 79571550760514599640514059)
          ·
            refine ⟨119357326140771899460771089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79571550760514599640514059 119357326140771899460771089)
            ·
              refine ⟨89517994605578924595578317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119357326140771899460771089 89517994605578924595578317)
              ·
                refine ⟨33569247977092096723341869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89517994605578924595578317 33569247977092096723341869)
                ·
                  refine ⟨12588467991409536271253201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33569247977092096723341869 12588467991409536271253201)
                  ·
                    refine ⟨9441350993557152203439901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12588467991409536271253201 9441350993557152203439901)
                    ·
                      refine ⟨3540506622583932076289963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9441350993557152203439901 3540506622583932076289963)
                      ·
                        rfl

theorem cell23_6895112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_6895112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895112 prefixEnd_6895112 := by exact prefixLift 6895112
  have htrace : WordTrace (prefixWord ++ tailWord_6895112) baseStart_6895112 baseEnd_6895112 := by
    simpa [prefixWord, tailWord_6895112, baseEnd_6895112] using wordTrace_append hprefix tailTrace_6895112
  have hstable : (prefixWord ++ tailWord_6895112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895112).length < 2 ^ (prefixWord ++ tailWord_6895112).sum := by decide
  have hdescent : baseEnd_6895112 < baseStart_6895112 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895152 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 2, 7, 2]
def baseStart_6895152 : Nat := 118140960795 + 6895152 * 2 ^ 59
def prefixEnd_6895152 : Nat := 4983230072969 + 3 ^ 40 * 6895152 * 2
def baseEnd_6895152 : Nat := 3540527161810111919789779

theorem tailTrace_6895152 : CollatzResearch.WordTrace tailWord_6895152 prefixEnd_6895152 3540527161810111919789779 := by
  unfold tailWord_6895152
  simp only [CollatzResearch.WordTrace]
  refine ⟨125743426958024688526663855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167657902610699584702218473 125743426958024688526663855)
  ·
    refine ⟨188615140437037032789995783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125743426958024688526663855 188615140437037032789995783)
    ·
      refine ⟨282922710655555549184993675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188615140437037032789995783 282922710655555549184993675)
      ·
        refine ⟨424384065983333323777490513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282922710655555549184993675 424384065983333323777490513)
        ·
          refine ⟨318288049487499992833117885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 424384065983333323777490513 318288049487499992833117885)
          ·
            refine ⟨119358018557812497312419207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 318288049487499992833117885 119358018557812497312419207)
            ·
              refine ⟨179037027836718745968628811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119358018557812497312419207 179037027836718745968628811)
              ·
                refine ⟨268555541755078118952943217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179037027836718745968628811 268555541755078118952943217)
                ·
                  refine ⟨201416656316308589214707413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 268555541755078118952943217 201416656316308589214707413)
                  ·
                    refine ⟨4720702882413482559719705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 201416656316308589214707413 4720702882413482559719705)
                    ·
                      refine ⟨3540527161810111919789779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4720702882413482559719705 3540527161810111919789779)
                      ·
                        rfl

theorem cell23_6895152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 2, 7, 2].length) (baseStart_6895152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895152 prefixEnd_6895152 := by exact prefixLift 6895152
  have htrace : WordTrace (prefixWord ++ tailWord_6895152) baseStart_6895152 baseEnd_6895152 := by
    simpa [prefixWord, tailWord_6895152, baseEnd_6895152] using wordTrace_append hprefix tailTrace_6895152
  have hstable : (prefixWord ++ tailWord_6895152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895152).length < 2 ^ (prefixWord ++ tailWord_6895152).sum := by decide
  have hdescent : baseEnd_6895152 < baseStart_6895152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895216 : List Nat := [2, 1, 1, 1, 6, 2, 2, 1, 1, 4, 2]
def baseStart_6895216 : Nat := 118140960795 + 6895216 * 2 ^ 59
def prefixEnd_6895216 : Nat := 4983230072969 + 3 ^ 40 * 6895216 * 2
def baseEnd_6895216 : Nat := 3540560024571999669389485

theorem tailTrace_6895216 : CollatzResearch.WordTrace tailWord_6895216 prefixEnd_6895216 3540560024571999669389485 := by
  unfold tailWord_6895216
  simp only [CollatzResearch.WordTrace]
  refine ⟨125744594093908757991828751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167659458791878343989105001 125744594093908757991828751)
  ·
    refine ⟨188616891140863136987743127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125744594093908757991828751 188616891140863136987743127)
    ·
      refine ⟨282925336711294705481614691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188616891140863136987743127 282925336711294705481614691)
      ·
        refine ⟨424388005066942058222422037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282925336711294705481614691 424388005066942058222422037)
        ·
          refine ⟨19893187737512908979176033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 424388005066942058222422037 19893187737512908979176033)
          ·
            refine ⟨14919890803134681734382025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19893187737512908979176033 14919890803134681734382025)
            ·
              refine ⟨11189918102351011300786519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14919890803134681734382025 11189918102351011300786519)
              ·
                refine ⟨16784877153526516951179779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11189918102351011300786519 16784877153526516951179779)
                ·
                  refine ⟨25177315730289775426769669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16784877153526516951179779 25177315730289775426769669)
                  ·
                    refine ⟨4720746699429332892519313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25177315730289775426769669 4720746699429332892519313)
                    ·
                      refine ⟨3540560024571999669389485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4720746699429332892519313 3540560024571999669389485)
                      ·
                        rfl

theorem cell23_6895216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 1, 4, 2].length) (baseStart_6895216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895216 prefixEnd_6895216 := by exact prefixLift 6895216
  have htrace : WordTrace (prefixWord ++ tailWord_6895216) baseStart_6895216 baseEnd_6895216 := by
    simpa [prefixWord, tailWord_6895216, baseEnd_6895216] using wordTrace_append hprefix tailTrace_6895216
  have hstable : (prefixWord ++ tailWord_6895216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895216).length < 2 ^ (prefixWord ++ tailWord_6895216).sum := by decide
  have hdescent : baseEnd_6895216 < baseStart_6895216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895232 : List Nat := [2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 3]
def baseStart_6895232 : Nat := 118140960795 + 6895232 * 2 ^ 59
def prefixEnd_6895232 : Nat := 4983230072969 + 3 ^ 40 * 6895232 * 2
def baseEnd_6895232 : Nat := 3540568240262471606789411

theorem tailTrace_6895232 : CollatzResearch.WordTrace tailWord_6895232 prefixEnd_6895232 3540568240262471606789411 := by
  unfold tailWord_6895232
  simp only [CollatzResearch.WordTrace]
  refine ⟨125744885877879775358119975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167659847837173033810826633 125744885877879775358119975)
  ·
    refine ⟨188617328816819663037179963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125744885877879775358119975 188617328816819663037179963)
    ·
      refine ⟨282925993225229494555769945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188617328816819663037179963 282925993225229494555769945)
      ·
        refine ⟨212194494918922120916827459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282925993225229494555769945 212194494918922120916827459)
        ·
          refine ⟨318291742378383181375241189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212194494918922120916827459 318291742378383181375241189)
          ·
            refine ⟨59679701695946846507857723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 318291742378383181375241189 59679701695946846507857723)
            ·
              refine ⟨89519552543920269761786585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59679701695946846507857723 89519552543920269761786585)
              ·
                refine ⟨67139664407940202321339939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89519552543920269761786585 67139664407940202321339939)
                ·
                  refine ⟨100709496611910303482009909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67139664407940202321339939 100709496611910303482009909)
                  ·
                    refine ⟨9441515307366590951438429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 100709496611910303482009909 9441515307366590951438429)
                    ·
                      refine ⟨3540568240262471606789411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9441515307366590951438429 3540568240262471606789411)
                      ·
                        rfl

theorem cell23_6895232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 3].length) (baseStart_6895232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895232 prefixEnd_6895232 := by exact prefixLift 6895232
  have htrace : WordTrace (prefixWord ++ tailWord_6895232) baseStart_6895232 baseEnd_6895232 := by
    simpa [prefixWord, tailWord_6895232, baseEnd_6895232] using wordTrace_append hprefix tailTrace_6895232
  have hstable : (prefixWord ++ tailWord_6895232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895232).length < 2 ^ (prefixWord ++ tailWord_6895232).sum := by decide
  have hdescent : baseEnd_6895232 < baseStart_6895232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895239 : List Nat := [1, 1, 4, 2, 1, 3, 1, 5, 5]
def baseStart_6895239 : Nat := 118140960795 + 6895239 * 2 ^ 59
def prefixEnd_6895239 : Nat := 4983230072969 + 3 ^ 40 * 6895239 * 2
def baseEnd_6895239 : Nat := 393396870514117008822431

theorem tailTrace_6895239 : CollatzResearch.WordTrace tailWord_6895239 prefixEnd_6895239 393396870514117008822431 := by
  unfold tailWord_6895239
  simp only [CollatzResearch.WordTrace]
  refine ⟨251490027066734190911744771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167660018044489460607829847 251490027066734190911744771)
  ·
    refine ⟨377235040600101286367617157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251490027066734190911744771 377235040600101286367617157)
    ·
      refine ⟨70731570112518991193928217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 377235040600101286367617157 70731570112518991193928217)
      ·
        refine ⟨53048677584389243395446163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70731570112518991193928217 53048677584389243395446163)
        ·
          refine ⟨79573016376583865093169245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53048677584389243395446163 79573016376583865093169245)
          ·
            refine ⟨29839881141218949409938467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79573016376583865093169245 29839881141218949409938467)
            ·
              refine ⟨44759821711828424114907701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29839881141218949409938467 44759821711828424114907701)
              ·
                refine ⟨4196233285483914760772597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44759821711828424114907701 4196233285483914760772597)
                ·
                  refine ⟨393396870514117008822431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4196233285483914760772597 393396870514117008822431)
                  ·
                    rfl

theorem cell23_6895239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 5, 5].length) (baseStart_6895239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895239 prefixEnd_6895239 := by exact prefixLift 6895239
  have htrace : WordTrace (prefixWord ++ tailWord_6895239) baseStart_6895239 baseEnd_6895239 := by
    simpa [prefixWord, tailWord_6895239, baseEnd_6895239] using wordTrace_append hprefix tailTrace_6895239
  have hstable : (prefixWord ++ tailWord_6895239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895239).length < 2 ^ (prefixWord ++ tailWord_6895239).sum := by decide
  have hdescent : baseEnd_6895239 < baseStart_6895239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895286 : List Nat := [5, 1, 3, 1, 1, 1, 2, 1, 1, 7]
def baseStart_6895286 : Nat := 118140960795 + 6895286 * 2 ^ 59
def prefixEnd_6895286 : Nat := 4983230072969 + 3 ^ 40 * 6895286 * 2
def baseEnd_6895286 : Nat := 1180198656072604798504721

theorem tailTrace_6895286 : CollatzResearch.WordTrace tailWord_6895286 prefixEnd_6895286 1180198656072604798504721 := by
  unfold tailWord_6895286
  simp only [CollatzResearch.WordTrace]
  refine ⟨15718233831097744871169107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167661160865042611959137141 15718233831097744871169107)
  ·
    refine ⟨23577350746646617306753661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15718233831097744871169107 23577350746646617306753661)
    ·
      refine ⟨8841506529992481490032623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23577350746646617306753661 8841506529992481490032623)
      ·
        refine ⟨13262259794988722235048935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8841506529992481490032623 13262259794988722235048935)
        ·
          refine ⟨19893389692483083352573403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13262259794988722235048935 19893389692483083352573403)
          ·
            refine ⟨29840084538724625028860105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19893389692483083352573403 29840084538724625028860105)
            ·
              refine ⟨22380063404043468771645079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29840084538724625028860105 22380063404043468771645079)
              ·
                refine ⟨33570095106065203157467619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22380063404043468771645079 33570095106065203157467619)
                ·
                  refine ⟨50355142659097804736201429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33570095106065203157467619 50355142659097804736201429)
                  ·
                    refine ⟨1180198656072604798504721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50355142659097804736201429 1180198656072604798504721)
                    ·
                      rfl

theorem cell23_6895286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_6895286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895286 prefixEnd_6895286 := by exact prefixLift 6895286
  have htrace : WordTrace (prefixWord ++ tailWord_6895286) baseStart_6895286 baseEnd_6895286 := by
    simpa [prefixWord, tailWord_6895286, baseEnd_6895286] using wordTrace_append hprefix tailTrace_6895286
  have hstable : (prefixWord ++ tailWord_6895286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895286).length < 2 ^ (prefixWord ++ tailWord_6895286).sum := by decide
  have hdescent : baseEnd_6895286 < baseStart_6895286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895289 : List Nat := [1, 2, 1, 4, 1, 1, 2, 2, 1, 6, 2]
def baseStart_6895289 : Nat := 118140960795 + 6895289 * 2 ^ 59
def prefixEnd_6895289 : Nat := 4983230072969 + 3 ^ 40 * 6895289 * 2
def baseEnd_6895289 : Nat := 3540597508659777883776649

theorem tailTrace_6895289 : CollatzResearch.WordTrace tailWord_6895289 prefixEnd_6895289 3540597508659777883776649 := by
  unfold tailWord_6895289
  simp only [CollatzResearch.WordTrace]
  refine ⟨251491850716553049451064921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167661233811035366300709947 251491850716553049451064921)
  ·
    refine ⟨188618888037414787088298691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251491850716553049451064921 188618888037414787088298691)
    ·
      refine ⟨282928332056122180632448037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188618888037414787088298691 282928332056122180632448037)
      ·
        refine ⟨53049062260522908868584007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 282928332056122180632448037 53049062260522908868584007)
        ·
          refine ⟨79573593390784363302876011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53049062260522908868584007 79573593390784363302876011)
          ·
            refine ⟨119360390086176544954314017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79573593390784363302876011 119360390086176544954314017)
            ·
              refine ⟨89520292564632408715735513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119360390086176544954314017 89520292564632408715735513)
              ·
                refine ⟨67140219423474306536801635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89520292564632408715735513 67140219423474306536801635)
                ·
                  refine ⟨100710329135211459805202453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67140219423474306536801635 100710329135211459805202453)
                  ·
                    refine ⟨4720796678213037178368865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 100710329135211459805202453 4720796678213037178368865)
                    ·
                      refine ⟨3540597508659777883776649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4720796678213037178368865 3540597508659777883776649)
                      ·
                        rfl

theorem cell23_6895289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 6, 2].length) (baseStart_6895289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895289 prefixEnd_6895289 := by exact prefixLift 6895289
  have htrace : WordTrace (prefixWord ++ tailWord_6895289) baseStart_6895289 baseEnd_6895289 := by
    simpa [prefixWord, tailWord_6895289, baseEnd_6895289] using wordTrace_append hprefix tailTrace_6895289
  have hstable : (prefixWord ++ tailWord_6895289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895289).length < 2 ^ (prefixWord ++ tailWord_6895289).sum := by decide
  have hdescent : baseEnd_6895289 < baseStart_6895289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895306 : List Nat := [3, 1, 2, 1, 5, 1, 1, 2, 2, 1, 4]
def baseStart_6895306 : Nat := 118140960795 + 6895306 * 2 ^ 59
def prefixEnd_6895306 : Nat := 4983230072969 + 3 ^ 40 * 6895306 * 2
def baseEnd_6895306 : Nat := 3540606237830904317264071

theorem tailTrace_6895306 : CollatzResearch.WordTrace tailWord_6895306 prefixEnd_6895306 3540606237830904317264071 := by
  unfold tailWord_6895306
  simp only [CollatzResearch.WordTrace]
  refine ⟨62873117689372865338608443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167661647171660974236289181 62873117689372865338608443)
  ·
    refine ⟨94309676534059298007912665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62873117689372865338608443 94309676534059298007912665)
    ·
      refine ⟨70732257400544473505934499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94309676534059298007912665 70732257400544473505934499)
      ·
        refine ⟨106098386100816710258901749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70732257400544473505934499 106098386100816710258901749)
        ·
          refine ⟨9946723696951566586772039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106098386100816710258901749 9946723696951566586772039)
          ·
            refine ⟨14920085545427349880158059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9946723696951566586772039 14920085545427349880158059)
            ·
              refine ⟨22380128318141024820237089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14920085545427349880158059 22380128318141024820237089)
              ·
                refine ⟨16785096238605768615177817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22380128318141024820237089 16785096238605768615177817)
                ·
                  refine ⟨12588822178954326461383363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16785096238605768615177817 12588822178954326461383363)
                  ·
                    refine ⟨18883233268431489692075045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12588822178954326461383363 18883233268431489692075045)
                    ·
                      refine ⟨3540606237830904317264071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18883233268431489692075045 3540606237830904317264071)
                      ·
                        rfl

theorem cell23_6895306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 2, 1, 4].length) (baseStart_6895306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895306 prefixEnd_6895306 := by exact prefixLift 6895306
  have htrace : WordTrace (prefixWord ++ tailWord_6895306) baseStart_6895306 baseEnd_6895306 := by
    simpa [prefixWord, tailWord_6895306, baseEnd_6895306] using wordTrace_append hprefix tailTrace_6895306
  have hstable : (prefixWord ++ tailWord_6895306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895306).length < 2 ^ (prefixWord ++ tailWord_6895306).sum := by decide
  have hdescent : baseEnd_6895306 < baseStart_6895306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895352 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 2, 4, 5]
def baseStart_6895352 : Nat := 118140960795 + 6895352 * 2 ^ 59
def prefixEnd_6895352 : Nat := 4983230072969 + 3 ^ 40 * 6895352 * 2
def baseEnd_6895352 : Nat := 3540629857941011137288859

theorem tailTrace_6895352 : CollatzResearch.WordTrace tailWord_6895352 prefixEnd_6895352 3540629857941011137288859 := by
  unfold tailWord_6895352
  simp only [CollatzResearch.WordTrace]
  refine ⟨125747074257662405605304155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167662765676883207473738873 125747074257662405605304155)
  ·
    refine ⟨188620611386493608407956233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125747074257662405605304155 188620611386493608407956233)
    ·
      refine ⟨141465458539870206305967175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188620611386493608407956233 141465458539870206305967175)
      ·
        refine ⟨212198187809805309458950763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141465458539870206305967175 212198187809805309458950763)
        ·
          refine ⟨318297281714707964188426145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212198187809805309458950763 318297281714707964188426145)
          ·
            refine ⟨238722961286030973141319609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318297281714707964188426145 238722961286030973141319609)
            ·
              refine ⟨179042220964523229855989707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238722961286030973141319609 179042220964523229855989707)
              ·
                refine ⟨268563331446784844783984561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179042220964523229855989707 268563331446784844783984561)
                ·
                  refine ⟨201422498585088633587988421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 268563331446784844783984561 201422498585088633587988421)
                  ·
                    refine ⟨37766718484704118797747829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 201422498585088633587988421 37766718484704118797747829)
                    ·
                      refine ⟨3540629857941011137288859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37766718484704118797747829 3540629857941011137288859)
                      ·
                        rfl

theorem cell23_6895352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_6895352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895352 prefixEnd_6895352 := by exact prefixLift 6895352
  have htrace : WordTrace (prefixWord ++ tailWord_6895352) baseStart_6895352 baseEnd_6895352 := by
    simpa [prefixWord, tailWord_6895352, baseEnd_6895352] using wordTrace_append hprefix tailTrace_6895352
  have hstable : (prefixWord ++ tailWord_6895352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895352).length < 2 ^ (prefixWord ++ tailWord_6895352).sum := by decide
  have hdescent : baseEnd_6895352 < baseStart_6895352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895359 : List Nat := [1, 1, 2, 2, 1, 3, 2, 5, 1, 5]
def baseStart_6895359 : Nat := 118140960795 + 6895359 * 2 ^ 59
def prefixEnd_6895359 : Nat := 4983230072969 + 3 ^ 40 * 6895359 * 2
def baseEnd_6895359 : Nat := 1180211150768530869967109

theorem tailTrace_6895359 : CollatzResearch.WordTrace tailWord_6895359 prefixEnd_6895359 1180211150768530869967109 := by
  unfold tailWord_6895359
  simp only [CollatzResearch.WordTrace]
  refine ⟨251494403826299451406113131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167662935884199634270742087 251494403826299451406113131)
  ·
    refine ⟨377241605739449177109169697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251494403826299451406113131 377241605739449177109169697)
    ·
      refine ⟨282931204304586882831877273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377241605739449177109169697 282931204304586882831877273)
      ·
        refine ⟨212198403228440162123907955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282931204304586882831877273 212198403228440162123907955)
        ·
          refine ⟨318297604842660243185861933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212198403228440162123907955 318297604842660243185861933)
          ·
            refine ⟨119361601815997591194698225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 318297604842660243185861933 119361601815997591194698225)
            ·
              refine ⟨89521201361998193396023669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119361601815997591194698225 89521201361998193396023669)
              ·
                refine ⟨8392612627687330630877219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89521201361998193396023669 8392612627687330630877219)
                ·
                  refine ⟨12588918941530995946315829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8392612627687330630877219 12588918941530995946315829)
                  ·
                    refine ⟨1180211150768530869967109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12588918941530995946315829 1180211150768530869967109)
                    ·
                      rfl

theorem cell23_6895359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5, 1, 5].length) (baseStart_6895359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895359 prefixEnd_6895359 := by exact prefixLift 6895359
  have htrace : WordTrace (prefixWord ++ tailWord_6895359) baseStart_6895359 baseEnd_6895359 := by
    simpa [prefixWord, tailWord_6895359, baseEnd_6895359] using wordTrace_append hprefix tailTrace_6895359
  have hstable : (prefixWord ++ tailWord_6895359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895359).length < 2 ^ (prefixWord ++ tailWord_6895359).sum := by decide
  have hdescent : baseEnd_6895359 < baseStart_6895359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895367 : List Nat := [1, 1, 4, 4, 2, 2, 2, 2, 1, 4]
def baseStart_6895367 : Nat := 118140960795 + 6895367 * 2 ^ 59
def prefixEnd_6895367 : Nat := 4983230072969 + 3 ^ 40 * 6895367 * 2
def baseEnd_6895367 : Nat := 1180212520050276192867097

theorem tailTrace_6895367 : CollatzResearch.WordTrace tailWord_6895367 prefixEnd_6895367 1180212520050276192867097 := by
  unfold tailWord_6895367
  simp only [CollatzResearch.WordTrace]
  refine ⟨251494695610270468772404355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167663130406846979181602903 251494695610270468772404355)
  ·
    refine ⟨377242043415405703158606533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251494695610270468772404355 377242043415405703158606533)
    ·
      refine ⟨70732883140388569342238725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 377242043415405703158606533 70732883140388569342238725)
      ·
        refine ⟨13262415588822856751669761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70732883140388569342238725 13262415588822856751669761)
        ·
          refine ⟨9946811691617142563752321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13262415588822856751669761 9946811691617142563752321)
          ·
            refine ⟨7460108768712856922814241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9946811691617142563752321 7460108768712856922814241)
            ·
              refine ⟨5595081576534642692110681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7460108768712856922814241 5595081576534642692110681)
              ·
                refine ⟨4196311182400982019083011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5595081576534642692110681 4196311182400982019083011)
                ·
                  refine ⟨6294466773601473028624517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4196311182400982019083011 6294466773601473028624517)
                  ·
                    refine ⟨1180212520050276192867097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6294466773601473028624517 1180212520050276192867097)
                    ·
                      rfl

theorem cell23_6895367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 2, 1, 4].length) (baseStart_6895367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895367 prefixEnd_6895367 := by exact prefixLift 6895367
  have htrace : WordTrace (prefixWord ++ tailWord_6895367) baseStart_6895367 baseEnd_6895367 := by
    simpa [prefixWord, tailWord_6895367, baseEnd_6895367] using wordTrace_append hprefix tailTrace_6895367
  have hstable : (prefixWord ++ tailWord_6895367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895367).length < 2 ^ (prefixWord ++ tailWord_6895367).sum := by decide
  have hdescent : baseEnd_6895367 < baseStart_6895367 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895396 : List Nat := [2, 3, 1, 3, 2, 1, 2, 1, 3, 1, 4]
def baseStart_6895396 : Nat := 118140960795 + 6895396 * 2 ^ 59
def prefixEnd_6895396 : Nat := 4983230072969 + 3 ^ 40 * 6895396 * 2
def baseEnd_6895396 : Nat := 3540652451089808965138657

theorem tailTrace_6895396 : CollatzResearch.WordTrace tailWord_6895396 prefixEnd_6895396 3540652451089808965138657 := by
  unfold tailWord_6895396
  simp only [CollatzResearch.WordTrace]
  refine ⟨125747876663582703362605021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167663835551443604483473361 125747876663582703362605021)
  ·
    refine ⟨47155453748843513760976883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125747876663582703362605021 47155453748843513760976883)
    ·
      refine ⟨70733180623265270641465325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47155453748843513760976883 70733180623265270641465325)
      ·
        refine ⟨26524942733724476490549497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70733180623265270641465325 26524942733724476490549497)
        ·
          refine ⟨19893707050293357367912123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26524942733724476490549497 19893707050293357367912123)
          ·
            refine ⟨29840560575440036051868185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19893707050293357367912123 29840560575440036051868185)
            ·
              refine ⟨22380420431580027038901139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29840560575440036051868185 22380420431580027038901139)
              ·
                refine ⟨33570630647370040558351709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22380420431580027038901139 33570630647370040558351709)
                ·
                  refine ⟨12588986492763765209381891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33570630647370040558351709 12588986492763765209381891)
                  ·
                    refine ⟨18883479739145647814072837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12588986492763765209381891 18883479739145647814072837)
                    ·
                      refine ⟨3540652451089808965138657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18883479739145647814072837 3540652451089808965138657)
                      ·
                        rfl

theorem cell23_6895396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_6895396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895396 prefixEnd_6895396 := by exact prefixLift 6895396
  have htrace : WordTrace (prefixWord ++ tailWord_6895396) baseStart_6895396 baseEnd_6895396 := by
    simpa [prefixWord, tailWord_6895396, baseEnd_6895396] using wordTrace_append hprefix tailTrace_6895396
  have hstable : (prefixWord ++ tailWord_6895396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895396).length < 2 ^ (prefixWord ++ tailWord_6895396).sum := by decide
  have hdescent : baseEnd_6895396 < baseStart_6895396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895400 : List Nat := [2, 1, 5, 1, 1, 4, 1, 1, 2, 3, 2]
def baseStart_6895400 : Nat := 118140960795 + 6895400 * 2 ^ 59
def prefixEnd_6895400 : Nat := 4983230072969 + 3 ^ 40 * 6895400 * 2
def baseEnd_6895400 : Nat := 3540654505012426949488639

theorem tailTrace_6895400 : CollatzResearch.WordTrace tailWord_6895400 prefixEnd_6895400 3540654505012426949488639 := by
  unfold tailWord_6895400
  simp only [CollatzResearch.WordTrace]
  refine ⟨125747949609575457704177827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167663932812767276938903769 125747949609575457704177827)
  ·
    refine ⟨188621924414363186556266741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125747949609575457704177827 188621924414363186556266741)
    ·
      refine ⟨17683305413846548739650007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 188621924414363186556266741 17683305413846548739650007)
      ·
        refine ⟨26524958120769823109475011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17683305413846548739650007 26524958120769823109475011)
        ·
          refine ⟨39787437181154734664212517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26524958120769823109475011 39787437181154734664212517)
          ·
            refine ⟨7460144471466512749539847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39787437181154734664212517 7460144471466512749539847)
            ·
              refine ⟨11190216707199769124309771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7460144471466512749539847 11190216707199769124309771)
              ·
                refine ⟨16785325060799653686464657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11190216707199769124309771 16785325060799653686464657)
                ·
                  refine ⟨12588993795599740264848493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16785325060799653686464657 12588993795599740264848493)
                  ·
                    refine ⟨4720872673349902599318185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12588993795599740264848493 4720872673349902599318185)
                    ·
                      refine ⟨3540654505012426949488639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4720872673349902599318185 3540654505012426949488639)
                      ·
                        rfl

theorem cell23_6895400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_6895400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895400 prefixEnd_6895400 := by exact prefixLift 6895400
  have htrace : WordTrace (prefixWord ++ tailWord_6895400) baseStart_6895400 baseEnd_6895400 := by
    simpa [prefixWord, tailWord_6895400, baseEnd_6895400] using wordTrace_append hprefix tailTrace_6895400
  have hstable : (prefixWord ++ tailWord_6895400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895400).length < 2 ^ (prefixWord ++ tailWord_6895400).sum := by decide
  have hdescent : baseEnd_6895400 < baseStart_6895400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895413 : List Nat := [1, 3, 3, 1, 4, 1, 1, 3, 1, 1, 4]
def baseStart_6895413 : Nat := 118140960795 + 6895413 * 2 ^ 59
def prefixEnd_6895413 : Nat := 4983230072969 + 3 ^ 40 * 6895413 * 2
def baseEnd_6895413 : Nat := 3540661180260935398626079

theorem tailTrace_6895413 : CollatzResearch.WordTrace tailWord_6895413 prefixEnd_6895413 3540661180260935398626079 := by
  unfold tailWord_6895413
  simp only [CollatzResearch.WordTrace]
  refine ⟨251496373368103818628578893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167664248912069212419052595 251496373368103818628578893)
  ·
    refine ⟨94311140013038931985717085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251496373368103818628578893 94311140013038931985717085)
    ·
      refine ⟨35366677504889599494643907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94311140013038931985717085 35366677504889599494643907)
      ·
        refine ⟨53050016257334399241965861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35366677504889599494643907 53050016257334399241965861)
        ·
          refine ⟨9946878048250199857868599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53050016257334399241965861 9946878048250199857868599)
          ·
            refine ⟨14920317072375299786802899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9946878048250199857868599 14920317072375299786802899)
            ·
              refine ⟨22380475608562949680204349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14920317072375299786802899 22380475608562949680204349)
              ·
                refine ⟨8392678353211106130076631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22380475608562949680204349 8392678353211106130076631)
                ·
                  refine ⟨12589017529816659195114947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8392678353211106130076631 12589017529816659195114947)
                  ·
                    refine ⟨18883526294724988792672421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12589017529816659195114947 18883526294724988792672421)
                    ·
                      refine ⟨3540661180260935398626079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18883526294724988792672421 3540661180260935398626079)
                      ·
                        rfl

theorem cell23_6895413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_6895413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895413 prefixEnd_6895413 := by exact prefixLift 6895413
  have htrace : WordTrace (prefixWord ++ tailWord_6895413) baseStart_6895413 baseEnd_6895413 := by
    simpa [prefixWord, tailWord_6895413, baseEnd_6895413] using wordTrace_append hprefix tailTrace_6895413
  have hstable : (prefixWord ++ tailWord_6895413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895413).length < 2 ^ (prefixWord ++ tailWord_6895413).sum := by decide
  have hdescent : baseEnd_6895413 < baseStart_6895413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895473 : List Nat := [1, 2, 2, 2, 1, 3, 1, 5, 1, 3, 2]
def baseStart_6895473 : Nat := 118140960795 + 6895473 * 2 ^ 59
def prefixEnd_6895473 : Nat := 4983230072969 + 3 ^ 40 * 6895473 * 2
def baseEnd_6895473 : Nat := 3540691989100205163875803

theorem tailTrace_6895473 : CollatzResearch.WordTrace tailWord_6895473 prefixEnd_6895473 3540691989100205163875803 := by
  unfold tailWord_6895473
  simp only [CollatzResearch.WordTrace]
  refine ⟨251498561747886448875763073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167665707831924299250508715 251498561747886448875763073)
  ·
    refine ⟨188623921310914836656822305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251498561747886448875763073 188623921310914836656822305)
    ·
      refine ⟨141467940983186127492616729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188623921310914836656822305 141467940983186127492616729)
      ·
        refine ⟨106100955737389595619462547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141467940983186127492616729 106100955737389595619462547)
        ·
          refine ⟨159151433606084393429193821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106100955737389595619462547 159151433606084393429193821)
          ·
            refine ⟨59681787602281647535947683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159151433606084393429193821 59681787602281647535947683)
            ·
              refine ⟨89522681403422471303921525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59681787602281647535947683 89522681403422471303921525)
              ·
                refine ⟨8392751381570856684742643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89522681403422471303921525 8392751381570856684742643)
                ·
                  refine ⟨12589127072356285027113965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8392751381570856684742643 12589127072356285027113965)
                  ·
                    refine ⟨4720922652133606885167737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12589127072356285027113965 4720922652133606885167737)
                    ·
                      refine ⟨3540691989100205163875803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4720922652133606885167737 3540691989100205163875803)
                      ·
                        rfl

theorem cell23_6895473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5, 1, 3, 2].length) (baseStart_6895473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895473 prefixEnd_6895473 := by exact prefixLift 6895473
  have htrace : WordTrace (prefixWord ++ tailWord_6895473) baseStart_6895473 baseEnd_6895473 := by
    simpa [prefixWord, tailWord_6895473, baseEnd_6895473] using wordTrace_append hprefix tailTrace_6895473
  have hstable : (prefixWord ++ tailWord_6895473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895473).length < 2 ^ (prefixWord ++ tailWord_6895473).sum := by decide
  have hdescent : baseEnd_6895473 < baseStart_6895473 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895499 : List Nat := [1, 1, 1, 1, 4, 2, 1, 3, 1, 4, 4]
def baseStart_6895499 : Nat := 118140960795 + 6895499 * 2 ^ 59
def prefixEnd_6895499 : Nat := 4983230072969 + 3 ^ 40 * 6895499 * 2
def baseEnd_6895499 : Nat := 3540705339597222062150683

theorem tailTrace_6895499 : CollatzResearch.WordTrace tailWord_6895499 prefixEnd_6895499 3540705339597222062150683 := by
  unfold tailWord_6895499
  simp only [CollatzResearch.WordTrace]
  refine ⟨251499510045792255316209551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167666340030528170210806367 251499510045792255316209551)
  ·
    refine ⟨377249265068688382974314327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251499510045792255316209551 377249265068688382974314327)
    ·
      refine ⟨565873897603032574461471491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377249265068688382974314327 565873897603032574461471491)
      ·
        refine ⟨848810846404548861692207237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565873897603032574461471491 848810846404548861692207237)
        ·
          refine ⟨159152033700852911567288857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 848810846404548861692207237 159152033700852911567288857)
          ·
            refine ⟨119364025275639683675466643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159152033700852911567288857 119364025275639683675466643)
            ·
              refine ⟨179046037913459525513199965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119364025275639683675466643 179046037913459525513199965)
              ·
                refine ⟨67142264217547322067449987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179046037913459525513199965 67142264217547322067449987)
                ·
                  refine ⟨100713396326320983101174981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67142264217547322067449987 100713396326320983101174981)
                  ·
                    refine ⟨18883761811185184331470309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 100713396326320983101174981 18883761811185184331470309)
                    ·
                      refine ⟨3540705339597222062150683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18883761811185184331470309 3540705339597222062150683)
                      ·
                        rfl

theorem cell23_6895499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4, 4].length) (baseStart_6895499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895499 prefixEnd_6895499 := by exact prefixLift 6895499
  have htrace : WordTrace (prefixWord ++ tailWord_6895499) baseStart_6895499 baseEnd_6895499 := by
    simpa [prefixWord, tailWord_6895499, baseEnd_6895499] using wordTrace_append hprefix tailTrace_6895499
  have hstable : (prefixWord ++ tailWord_6895499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895499).length < 2 ^ (prefixWord ++ tailWord_6895499).sum := by decide
  have hdescent : baseEnd_6895499 < baseStart_6895499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895509 : List Nat := [1, 3, 2, 1, 1, 3, 2, 1, 9]
def baseStart_6895509 : Nat := 118140960795 + 6895509 * 2 ^ 59
def prefixEnd_6895509 : Nat := 4983230072969 + 3 ^ 40 * 6895509 * 2
def baseEnd_6895509 : Nat := 393412274933751891447293

theorem tailTrace_6895509 : CollatzResearch.WordTrace tailWord_6895509 prefixEnd_6895509 393412274933751891447293 := by
  unfold tailWord_6895509
  simp only [CollatzResearch.WordTrace]
  refine ⟨251499874775756027024073581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167666583183837351349382387 251499874775756027024073581)
  ·
    refine ⟨94312453040908510134027593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251499874775756027024073581 94312453040908510134027593)
    ·
      refine ⟨70734339780681382600520695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94312453040908510134027593 70734339780681382600520695)
      ·
        refine ⟨106101509671022073900781043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70734339780681382600520695 106101509671022073900781043)
        ·
          refine ⟨159152264506533110851171565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106101509671022073900781043 159152264506533110851171565)
          ·
            refine ⟨59682099189949916569189337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159152264506533110851171565 59682099189949916569189337)
            ·
              refine ⟨44761574392462437426892003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59682099189949916569189337 44761574392462437426892003)
              ·
                refine ⟨67142361588693656140338005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44761574392462437426892003 67142361588693656140338005)
                ·
                  refine ⟨393412274933751891447293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67142361588693656140338005 393412274933751891447293)
                  ·
                    rfl

theorem cell23_6895509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 9].length) (baseStart_6895509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895509 prefixEnd_6895509 := by exact prefixLift 6895509
  have htrace : WordTrace (prefixWord ++ tailWord_6895509) baseStart_6895509 baseEnd_6895509 := by
    simpa [prefixWord, tailWord_6895509, baseEnd_6895509] using wordTrace_append hprefix tailTrace_6895509
  have hstable : (prefixWord ++ tailWord_6895509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895509).length < 2 ^ (prefixWord ++ tailWord_6895509).sum := by decide
  have hdescent : baseEnd_6895509 < baseStart_6895509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895537 : List Nat := [1, 2, 2, 4, 2, 2, 2, 2, 2, 2, 2]
def baseStart_6895537 : Nat := 118140960795 + 6895537 * 2 ^ 59
def prefixEnd_6895537 : Nat := 4983230072969 + 3 ^ 40 * 6895537 * 2
def baseEnd_6895537 : Nat := 3540724851862092913475509

theorem tailTrace_6895537 : CollatzResearch.WordTrace tailWord_6895537 prefixEnd_6895537 3540724851862092913475509 := by
  unfold tailWord_6895537
  simp only [CollatzResearch.WordTrace]
  refine ⟨251500896019654587806092865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167667264013103058537395243 251500896019654587806092865)
  ·
    refine ⟨188625672014740940854569649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251500896019654587806092865 188625672014740940854569649)
    ·
      refine ⟨141469254011055705640927237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188625672014740940854569649 141469254011055705640927237)
      ·
        refine ⟨26525485127072944807673857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141469254011055705640927237 26525485127072944807673857)
        ·
          refine ⟨19894113845304708605755393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26525485127072944807673857 19894113845304708605755393)
          ·
            refine ⟨14920585383978531454316545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19894113845304708605755393 14920585383978531454316545)
            ·
              refine ⟨11190439037983898590737409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14920585383978531454316545 11190439037983898590737409)
              ·
                refine ⟨8392829278487923943053057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11190439037983898590737409 8392829278487923943053057)
                ·
                  refine ⟨6294621958865942957289793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8392829278487923943053057 6294621958865942957289793)
                  ·
                    refine ⟨4720966469149457217967345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6294621958865942957289793 4720966469149457217967345)
                    ·
                      refine ⟨3540724851862092913475509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4720966469149457217967345 3540724851862092913475509)
                      ·
                        rfl

theorem cell23_6895537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_6895537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895537 prefixEnd_6895537 := by exact prefixLift 6895537
  have htrace : WordTrace (prefixWord ++ tailWord_6895537) baseStart_6895537 baseEnd_6895537 := by
    simpa [prefixWord, tailWord_6895537, baseEnd_6895537] using wordTrace_append hprefix tailTrace_6895537
  have hstable : (prefixWord ++ tailWord_6895537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895537).length < 2 ^ (prefixWord ++ tailWord_6895537).sum := by decide
  have hdescent : baseEnd_6895537 < baseStart_6895537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895569 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 1, 10]
def baseStart_6895569 : Nat := 118140960795 + 6895569 * 2 ^ 59
def prefixEnd_6895569 : Nat := 4983230072969 + 3 ^ 40 * 6895569 * 2
def baseEnd_6895569 : Nat := 1180247094414345596091787

theorem tailTrace_6895569 : CollatzResearch.WordTrace tailWord_6895569 prefixEnd_6895569 1180247094414345596091787 := by
  unfold tailWord_6895569
  simp only [CollatzResearch.WordTrace]
  refine ⟨251502063155538657271257761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167668042103692438180838507 251502063155538657271257761)
  ·
    refine ⟨188626547366653992953443321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251502063155538657271257761 188626547366653992953443321)
    ·
      refine ⟨141469910524990494715082491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188626547366653992953443321 141469910524990494715082491)
      ·
        refine ⟨212204865787485742072623737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141469910524990494715082491 212204865787485742072623737)
        ·
          refine ⟨159153649340614306554467803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212204865787485742072623737 159153649340614306554467803)
          ·
            refine ⟨238730474010921459831701705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159153649340614306554467803 238730474010921459831701705)
            ·
              refine ⟨179047855508191094873776279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238730474010921459831701705 179047855508191094873776279)
              ·
                refine ⟨268571783262286642310664419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179047855508191094873776279 268571783262286642310664419)
                ·
                  refine ⟨402857674893429963465996629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 268571783262286642310664419 402857674893429963465996629)
                  ·
                    refine ⟨1180247094414345596091787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 402857674893429963465996629 1180247094414345596091787)
                    ·
                      rfl

theorem cell23_6895569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 10].length) (baseStart_6895569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895569 prefixEnd_6895569 := by exact prefixLift 6895569
  have htrace : WordTrace (prefixWord ++ tailWord_6895569) baseStart_6895569 baseEnd_6895569 := by
    simpa [prefixWord, tailWord_6895569, baseEnd_6895569] using wordTrace_append hprefix tailTrace_6895569
  have hstable : (prefixWord ++ tailWord_6895569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895569).length < 2 ^ (prefixWord ++ tailWord_6895569).sum := by decide
  have hdescent : baseEnd_6895569 < baseStart_6895569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895573 : List Nat := [1, 3, 2, 3, 2, 1, 3, 1, 2, 5]
def baseStart_6895573 : Nat := 118140960795 + 6895573 * 2 ^ 59
def prefixEnd_6895573 : Nat := 4983230072969 + 3 ^ 40 * 6895573 * 2
def baseEnd_6895573 : Nat := 1180247779055218257541781

theorem tailTrace_6895573 : CollatzResearch.WordTrace tailWord_6895573 prefixEnd_6895573 1180247779055218257541781 := by
  unfold tailWord_6895573
  simp only [CollatzResearch.WordTrace]
  refine ⟨251502209047524165954403373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167668139365016110636268915 251502209047524165954403373)
  ·
    refine ⟨94313328392821562232901265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251502209047524165954403373 94313328392821562232901265)
    ·
      refine ⟨70734996294616171674675949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94313328392821562232901265 70734996294616171674675949)
      ·
        refine ⟨26525623610481064378003481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70734996294616171674675949 26525623610481064378003481)
        ·
          refine ⟨19894217707860798283502611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26525623610481064378003481 19894217707860798283502611)
          ·
            refine ⟨29841326561791197425253917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19894217707860798283502611 29841326561791197425253917)
            ·
              refine ⟨11190497460671699034470219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29841326561791197425253917 11190497460671699034470219)
              ·
                refine ⟨16785746191007548551705329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11190497460671699034470219 16785746191007548551705329)
                ·
                  refine ⟨12589309643255661413778997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16785746191007548551705329 12589309643255661413778997)
                  ·
                    refine ⟨1180247779055218257541781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12589309643255661413778997 1180247779055218257541781)
                    ·
                      rfl

theorem cell23_6895573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 2, 5].length) (baseStart_6895573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895573 prefixEnd_6895573 := by exact prefixLift 6895573
  have htrace : WordTrace (prefixWord ++ tailWord_6895573) baseStart_6895573 baseEnd_6895573 := by
    simpa [prefixWord, tailWord_6895573, baseEnd_6895573] using wordTrace_append hprefix tailTrace_6895573
  have hstable : (prefixWord ++ tailWord_6895573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895573).length < 2 ^ (prefixWord ++ tailWord_6895573).sum := by decide
  have hdescent : baseEnd_6895573 < baseStart_6895573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895576 : List Nat := [2, 1, 2, 2, 2, 2, 3, 1, 1, 3, 4]
def baseStart_6895576 : Nat := 118140960795 + 6895576 * 2 ^ 59
def prefixEnd_6895576 : Nat := 4983230072969 + 3 ^ 40 * 6895576 * 2
def baseEnd_6895576 : Nat := 3540744877607618260887829

theorem tailTrace_6895576 : CollatzResearch.WordTrace tailWord_6895576 prefixEnd_6895576 3540744877607618260887829 := by
  unfold tailWord_6895576
  simp only [CollatzResearch.WordTrace]
  refine ⟨125751159233256648733381291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167668212311008864977841721 125751159233256648733381291)
  ·
    refine ⟨188626738849884973100071937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125751159233256648733381291 188626738849884973100071937)
    ·
      refine ⟨141470054137413729825053953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188626738849884973100071937 141470054137413729825053953)
      ·
        refine ⟨106102540603060297368790465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141470054137413729825053953 106102540603060297368790465)
        ·
          refine ⟨79576905452295223026592849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106102540603060297368790465 79576905452295223026592849)
          ·
            refine ⟨59682679089221417269944637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79576905452295223026592849 59682679089221417269944637)
            ·
              refine ⟨22381004658458031476229239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59682679089221417269944637 22381004658458031476229239)
              ·
                refine ⟨33571506987687047214343859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22381004658458031476229239 33571506987687047214343859)
                ·
                  refine ⟨50357260481530570821515789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33571506987687047214343859 50357260481530570821515789)
                  ·
                    refine ⟨18883972680573964058068421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50357260481530570821515789 18883972680573964058068421)
                    ·
                      refine ⟨3540744877607618260887829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18883972680573964058068421 3540744877607618260887829)
                      ·
                        rfl

theorem cell23_6895576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_6895576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895576 prefixEnd_6895576 := by exact prefixLift 6895576
  have htrace : WordTrace (prefixWord ++ tailWord_6895576) baseStart_6895576 baseEnd_6895576 := by
    simpa [prefixWord, tailWord_6895576, baseEnd_6895576] using wordTrace_append hprefix tailTrace_6895576
  have hstable : (prefixWord ++ tailWord_6895576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895576).length < 2 ^ (prefixWord ++ tailWord_6895576).sum := by decide
  have hdescent : baseEnd_6895576 < baseStart_6895576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895680 : List Nat := [2, 1, 1, 2, 2, 6, 1, 2, 1, 5]
def baseStart_6895680 : Nat := 118140960795 + 6895680 * 2 ^ 59
def prefixEnd_6895680 : Nat := 4983230072969 + 3 ^ 40 * 6895680 * 2
def baseEnd_6895680 : Nat := 1180266093198561951329117

theorem tailTrace_6895680 : CollatzResearch.WordTrace tailWord_6895680 prefixEnd_6895680 1180266093198561951329117 := by
  unfold tailWord_6895680
  simp only [CollatzResearch.WordTrace]
  refine ⟨125753055829068261614274247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167670741105424348819032329 125753055829068261614274247)
  ·
    refine ⟨188629583743602392421411371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125753055829068261614274247 188629583743602392421411371)
    ·
      refine ⟨282944375615403588632117057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188629583743602392421411371 282944375615403588632117057)
      ·
        refine ⟨212208281711552691474087793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282944375615403588632117057 212208281711552691474087793)
        ·
          refine ⟨159156211283664518605565845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212208281711552691474087793 159156211283664518605565845)
          ·
            refine ⟨7460447403921774309635899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 159156211283664518605565845 7460447403921774309635899)
            ·
              refine ⟨11190671105882661464453849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7460447403921774309635899 11190671105882661464453849)
              ·
                refine ⟨8393003329411996098340387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11190671105882661464453849 8393003329411996098340387)
                ·
                  refine ⟨12589504994117994147510581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8393003329411996098340387 12589504994117994147510581)
                  ·
                    refine ⟨1180266093198561951329117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12589504994117994147510581 1180266093198561951329117)
                    ·
                      rfl

theorem cell23_6895680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 2, 1, 5].length) (baseStart_6895680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895680 prefixEnd_6895680 := by exact prefixLift 6895680
  have htrace : WordTrace (prefixWord ++ tailWord_6895680) baseStart_6895680 baseEnd_6895680 := by
    simpa [prefixWord, tailWord_6895680, baseEnd_6895680] using wordTrace_append hprefix tailTrace_6895680
  have hstable : (prefixWord ++ tailWord_6895680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895680).length < 2 ^ (prefixWord ++ tailWord_6895680).sum := by decide
  have hdescent : baseEnd_6895680 < baseStart_6895680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895683 : List Nat := [1, 1, 1, 3, 1, 2, 2, 6, 1, 1, 4]
def baseStart_6895683 : Nat := 118140960795 + 6895683 * 2 ^ 59
def prefixEnd_6895683 : Nat := 4983230072969 + 3 ^ 40 * 6895683 * 2
def baseEnd_6895683 : Nat := 3540799820037649342249837

theorem tailTrace_6895683 : CollatzResearch.WordTrace tailWord_6895683 prefixEnd_6895683 3540799820037649342249837 := by
  unfold tailWord_6895683
  simp only [CollatzResearch.WordTrace]
  refine ⟨251506221077125654740907703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167670814051417103160605135 251506221077125654740907703)
  ·
    refine ⟨377259331615688482111361555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251506221077125654740907703 377259331615688482111361555)
    ·
      refine ⟨565888997423532723167042333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377259331615688482111361555 565888997423532723167042333)
      ·
        refine ⟨212208374033824771187640875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 565888997423532723167042333 212208374033824771187640875)
        ·
          refine ⟨318312561050737156781461313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212208374033824771187640875 318312561050737156781461313)
          ·
            refine ⟨238734420788052867586095985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318312561050737156781461313 238734420788052867586095985)
            ·
              refine ⟨179050815591039650689571989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238734420788052867586095985 179050815591039650689571989)
              ·
                refine ⟨8393006980829983626073687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 179050815591039650689571989 8393006980829983626073687)
                ·
                  refine ⟨12589510471244975439110531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8393006980829983626073687 12589510471244975439110531)
                  ·
                    refine ⟨18884265706867463158665797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12589510471244975439110531 18884265706867463158665797)
                    ·
                      refine ⟨3540799820037649342249837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18884265706867463158665797 3540799820037649342249837)
                      ·
                        rfl

theorem cell23_6895683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6, 1, 1, 4].length) (baseStart_6895683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895683 prefixEnd_6895683 := by exact prefixLift 6895683
  have htrace : WordTrace (prefixWord ++ tailWord_6895683) baseStart_6895683 baseEnd_6895683 := by
    simpa [prefixWord, tailWord_6895683, baseEnd_6895683] using wordTrace_append hprefix tailTrace_6895683
  have hstable : (prefixWord ++ tailWord_6895683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895683).length < 2 ^ (prefixWord ++ tailWord_6895683).sum := by decide
  have hdescent : baseEnd_6895683 < baseStart_6895683 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895703 : List Nat := [1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 5]
def baseStart_6895703 : Nat := 118140960795 + 6895703 * 2 ^ 59
def prefixEnd_6895703 : Nat := 4983230072969 + 3 ^ 40 * 6895703 * 2
def baseEnd_6895703 : Nat := 3540810089650739263999745

theorem tailTrace_6895703 : CollatzResearch.WordTrace tailWord_6895703 prefixEnd_6895703 3540810089650739263999745 := by
  unfold tailWord_6895703
  simp only [CollatzResearch.WordTrace]
  refine ⟨251506950537053198156635763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167671300358035465437757175 251506950537053198156635763)
  ·
    refine ⟨377260425805579797234953645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251506950537053198156635763 377260425805579797234953645)
    ·
      refine ⟨141472659677092423963107617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377260425805579797234953645 141472659677092423963107617)
      ·
        refine ⟨106104494757819317972330713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141472659677092423963107617 106104494757819317972330713)
        ·
          refine ⟨79578371068364488479248035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106104494757819317972330713 79578371068364488479248035)
          ·
            refine ⟨119367556602546732718872053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79578371068364488479248035 119367556602546732718872053)
            ·
              refine ⟨11190708431488756192394255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119367556602546732718872053 11190708431488756192394255)
              ·
                refine ⟨16786062647233134288591383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11190708431488756192394255 16786062647233134288591383)
                ·
                  refine ⟨25179093970849701432887075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16786062647233134288591383 25179093970849701432887075)
                  ·
                    refine ⟨37768640956274552149330613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25179093970849701432887075 37768640956274552149330613)
                    ·
                      refine ⟨3540810089650739263999745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37768640956274552149330613 3540810089650739263999745)
                      ·
                        rfl

theorem cell23_6895703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 5].length) (baseStart_6895703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895703 prefixEnd_6895703 := by exact prefixLift 6895703
  have htrace : WordTrace (prefixWord ++ tailWord_6895703) baseStart_6895703 baseEnd_6895703 := by
    simpa [prefixWord, tailWord_6895703, baseEnd_6895703] using wordTrace_append hprefix tailTrace_6895703
  have hstable : (prefixWord ++ tailWord_6895703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895703).length < 2 ^ (prefixWord ++ tailWord_6895703).sum := by decide
  have hdescent : baseEnd_6895703 < baseStart_6895703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895730 : List Nat := [3, 2, 1, 2, 2, 3, 2, 1, 1, 2, 4]
def baseStart_6895730 : Nat := 118140960795 + 6895730 * 2 ^ 59
def prefixEnd_6895730 : Nat := 4983230072969 + 3 ^ 40 * 6895730 * 2
def baseEnd_6895730 : Nat := 3540823953628410658362121

theorem tailTrace_6895730 : CollatzResearch.WordTrace tailWord_6895730 prefixEnd_6895730 3540823953628410658362121 := by
  unfold tailWord_6895730
  simp only [CollatzResearch.WordTrace]
  refine ⟨62876983826988845441967161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167671956871970254511912429 62876983826988845441967161)
  ·
    refine ⟨47157737870241634081475371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62876983826988845441967161 47157737870241634081475371)
    ·
      refine ⟨70736606805362451122213057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47157737870241634081475371 70736606805362451122213057)
      ·
        refine ⟨53052455104021838341659793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70736606805362451122213057 53052455104021838341659793)
        ·
          refine ⟨39789341328016378756244845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53052455104021838341659793 39789341328016378756244845)
          ·
            refine ⟨14921002998006142033591817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39789341328016378756244845 14921002998006142033591817)
            ·
              refine ⟨11190752248504606525193863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14921002998006142033591817 11190752248504606525193863)
              ·
                refine ⟨16786128372756909787790795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11190752248504606525193863 16786128372756909787790795)
                ·
                  refine ⟨25179192559135364681686193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16786128372756909787790795 25179192559135364681686193)
                  ·
                    refine ⟨18884394419351523511264645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25179192559135364681686193 18884394419351523511264645)
                    ·
                      refine ⟨3540823953628410658362121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18884394419351523511264645 3540823953628410658362121)
                      ·
                        rfl

theorem cell23_6895730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_6895730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895730 prefixEnd_6895730 := by exact prefixLift 6895730
  have htrace : WordTrace (prefixWord ++ tailWord_6895730) baseStart_6895730 baseEnd_6895730 := by
    simpa [prefixWord, tailWord_6895730, baseEnd_6895730] using wordTrace_append hprefix tailTrace_6895730
  have hstable : (prefixWord ++ tailWord_6895730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895730).length < 2 ^ (prefixWord ++ tailWord_6895730).sum := by decide
  have hdescent : baseEnd_6895730 < baseStart_6895730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895734 : List Nat := [5, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2]
def baseStart_6895734 : Nat := 118140960795 + 6895734 * 2 ^ 59
def prefixEnd_6895734 : Nat := 4983230072969 + 3 ^ 40 * 6895734 * 2
def baseEnd_6895734 : Nat := 3540826007551028642712103

theorem tailTrace_6895734 : CollatzResearch.WordTrace tailWord_6895734 prefixEnd_6895734 3540826007551028642712103 := by
  unfold tailWord_6895734
  simp only [CollatzResearch.WordTrace]
  refine ⟨15719255074996305653188391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167672054133293926967342837 15719255074996305653188391)
  ·
    refine ⟨23578882612494458479782587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15719255074996305653188391 23578882612494458479782587)
    ·
      refine ⟨35368323918741687719673881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23578882612494458479782587 35368323918741687719673881)
      ·
        refine ⟨26526242939056265789755411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35368323918741687719673881 26526242939056265789755411)
        ·
          refine ⟨39789364408584398684633117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26526242939056265789755411 39789364408584398684633117)
          ·
            refine ⟨14921011653219149506737419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39789364408584398684633117 14921011653219149506737419)
            ·
              refine ⟨22381517479828724260106129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14921011653219149506737419 22381517479828724260106129)
              ·
                refine ⟨16786138109871543195079597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22381517479828724260106129 16786138109871543195079597)
                ·
                  refine ⟨6294801791201828698154849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16786138109871543195079597 6294801791201828698154849)
                  ·
                    refine ⟨4721101343401371523616137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6294801791201828698154849 4721101343401371523616137)
                    ·
                      refine ⟨3540826007551028642712103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4721101343401371523616137 3540826007551028642712103)
                      ·
                        rfl

theorem cell23_6895734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_6895734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895734 prefixEnd_6895734 := by exact prefixLift 6895734
  have htrace : WordTrace (prefixWord ++ tailWord_6895734) baseStart_6895734 baseEnd_6895734 := by
    simpa [prefixWord, tailWord_6895734, baseEnd_6895734] using wordTrace_append hprefix tailTrace_6895734
  have hstable : (prefixWord ++ tailWord_6895734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895734).length < 2 ^ (prefixWord ++ tailWord_6895734).sum := by decide
  have hdescent : baseEnd_6895734 < baseStart_6895734 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895736 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 4, 7]
def baseStart_6895736 : Nat := 118140960795 + 6895736 * 2 ^ 59
def prefixEnd_6895736 : Nat := 4983230072969 + 3 ^ 40 * 6895736 * 2
def baseEnd_6895736 : Nat := 1180275678170779211629031

theorem tailTrace_6895736 : CollatzResearch.WordTrace tailWord_6895736 prefixEnd_6895736 1180275678170779211629031 := by
  unfold tailWord_6895736
  simp only [CollatzResearch.WordTrace]
  refine ⟨125754077072966822396293531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167672102763955763195058041 125754077072966822396293531)
  ·
    refine ⟨188631115609450233594440297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125754077072966822396293531 188631115609450233594440297)
    ·
      refine ⟨141473336707087675195830223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188631115609450233594440297 141473336707087675195830223)
      ·
        refine ⟨212210005060631512793745335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141473336707087675195830223 212210005060631512793745335)
        ·
          refine ⟨318315007590947269190618003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212210005060631512793745335 318315007590947269190618003)
          ·
            refine ⟨477472511386420903785927005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318315007590947269190618003 477472511386420903785927005)
            ·
              refine ⟨179052191769907838919722627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 477472511386420903785927005 179052191769907838919722627)
              ·
                refine ⟨268578287654861758379583941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179052191769907838919722627 268578287654861758379583941)
                ·
                  refine ⟨50358428935286579696171989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 268578287654861758379583941 50358428935286579696171989)
                  ·
                    refine ⟨1180275678170779211629031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50358428935286579696171989 1180275678170779211629031)
                    ·
                      rfl

theorem cell23_6895736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 4, 7].length) (baseStart_6895736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895736 prefixEnd_6895736 := by exact prefixLift 6895736
  have htrace : WordTrace (prefixWord ++ tailWord_6895736) baseStart_6895736 baseEnd_6895736 := by
    simpa [prefixWord, tailWord_6895736, baseEnd_6895736] using wordTrace_append hprefix tailTrace_6895736
  have hstable : (prefixWord ++ tailWord_6895736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895736).length < 2 ^ (prefixWord ++ tailWord_6895736).sum := by decide
  have hdescent : baseEnd_6895736 < baseStart_6895736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895754 : List Nat := [3, 1, 2, 3, 1, 4, 2, 1, 1, 2, 3]
def baseStart_6895754 : Nat := 118140960795 + 6895754 * 2 ^ 59
def prefixEnd_6895754 : Nat := 4983230072969 + 3 ^ 40 * 6895754 * 2
def baseEnd_6895754 : Nat := 3540836277164118564462011

theorem tailTrace_6895754 : CollatzResearch.WordTrace tailWord_6895754 prefixEnd_6895754 3540836277164118564462011 := by
  unfold tailWord_6895754
  simp only [CollatzResearch.WordTrace]
  refine ⟨62877202664967108466685579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167672540439912289244494877 62877202664967108466685579)
  ·
    refine ⟨94315803997450662700028369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62877202664967108466685579 94315803997450662700028369)
    ·
      refine ⟨70736852998087997025021277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94315803997450662700028369 70736852998087997025021277)
      ·
        refine ⟨26526319874282998884382979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70736852998087997025021277 26526319874282998884382979)
        ·
          refine ⟨39789479811424498326574469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26526319874282998884382979 39789479811424498326574469)
          ·
            refine ⟨7460527464642093436232713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39789479811424498326574469 7460527464642093436232713)
            ·
              refine ⟨5595395598481570077174535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7460527464642093436232713 5595395598481570077174535)
              ·
                refine ⟨8393093397722355115761803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5595395598481570077174535 8393093397722355115761803)
                ·
                  refine ⟨12589640096583532673642705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8393093397722355115761803 12589640096583532673642705)
                  ·
                    refine ⟨9442230072437649505232029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12589640096583532673642705 9442230072437649505232029)
                    ·
                      refine ⟨3540836277164118564462011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9442230072437649505232029 3540836277164118564462011)
                      ·
                        rfl

theorem cell23_6895754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_6895754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895754 prefixEnd_6895754 := by exact prefixLift 6895754
  have htrace : WordTrace (prefixWord ++ tailWord_6895754) baseStart_6895754 baseEnd_6895754 := by
    simpa [prefixWord, tailWord_6895754, baseEnd_6895754] using wordTrace_append hprefix tailTrace_6895754
  have hstable : (prefixWord ++ tailWord_6895754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895754).length < 2 ^ (prefixWord ++ tailWord_6895754).sum := by decide
  have hdescent : baseEnd_6895754 < baseStart_6895754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895767 : List Nat := [1, 1, 3, 3, 4, 1, 1, 1, 4, 1, 3]
def baseStart_6895767 : Nat := 118140960795 + 6895767 * 2 ^ 59
def prefixEnd_6895767 : Nat := 4983230072969 + 3 ^ 40 * 6895767 * 2
def baseEnd_6895767 : Nat := 3540842952412627013599451

theorem tailTrace_6895767 : CollatzResearch.WordTrace tailWord_6895767 prefixEnd_6895767 3540842952412627013599451 := by
  unfold tailWord_6895767
  simp only [CollatzResearch.WordTrace]
  refine ⟨251509284808821337086965555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167672856539214224724643703 251509284808821337086965555)
  ·
    refine ⟨377263927213232005630448333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251509284808821337086965555 377263927213232005630448333)
    ·
      refine ⟨141473972704962002111418125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377263927213232005630448333 141473972704962002111418125)
      ·
        refine ⟨53052739764360750791781797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141473972704962002111418125 53052739764360750791781797)
        ·
          refine ⟨9947388705817640773459087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53052739764360750791781797 9947388705817640773459087)
          ·
            refine ⟨14921083058726461160188631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9947388705817640773459087 14921083058726461160188631)
            ·
              refine ⟨22381624588089691740282947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14921083058726461160188631 22381624588089691740282947)
              ·
                refine ⟨33572436882134537610424421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22381624588089691740282947 33572436882134537610424421)
                ·
                  refine ⟨6294831915400225801954579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33572436882134537610424421 6294831915400225801954579)
                  ·
                    refine ⟨9442247873100338702931869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6294831915400225801954579 9442247873100338702931869)
                    ·
                      refine ⟨3540842952412627013599451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9442247873100338702931869 3540842952412627013599451)
                      ·
                        rfl

theorem cell23_6895767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_6895767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895767 prefixEnd_6895767 := by exact prefixLift 6895767
  have htrace : WordTrace (prefixWord ++ tailWord_6895767) baseStart_6895767 baseEnd_6895767 := by
    simpa [prefixWord, tailWord_6895767, baseEnd_6895767] using wordTrace_append hprefix tailTrace_6895767
  have hstable : (prefixWord ++ tailWord_6895767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895767).length < 2 ^ (prefixWord ++ tailWord_6895767).sum := by decide
  have hdescent : baseEnd_6895767 < baseStart_6895767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895870 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5]
def baseStart_6895870 : Nat := 118140960795 + 6895870 * 2 ^ 59
def prefixEnd_6895870 : Nat := 4983230072969 + 3 ^ 40 * 6895870 * 2
def baseEnd_6895870 : Nat := 3540895840920040110611477

theorem tailTrace_6895870 : CollatzResearch.WordTrace tailWord_6895870 prefixEnd_6895870 3540895840920040110611477 := by
  unfold tailWord_6895870
  simp only [CollatzResearch.WordTrace]
  refine ⟨31439130190931023209745633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167675361018298790451976709 31439130190931023209745633)
  ·
    refine ⟨23579347643198267407309225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31439130190931023209745633 23579347643198267407309225)
    ·
      refine ⟨17684510732398700555481919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23579347643198267407309225 17684510732398700555481919)
      ·
        refine ⟨26526766098598050833222879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17684510732398700555481919 26526766098598050833222879)
        ·
          refine ⟨39790149147897076249834319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26526766098598050833222879 39790149147897076249834319)
          ·
            refine ⟨59685223721845614374751479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39790149147897076249834319 59685223721845614374751479)
            ·
              refine ⟨89527835582768421562127219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59685223721845614374751479 89527835582768421562127219)
              ·
                refine ⟨134291753374152632343190829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89527835582768421562127219 134291753374152632343190829)
                ·
                  refine ⟨50359407515307237128696561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134291753374152632343190829 50359407515307237128696561)
                  ·
                    refine ⟨37769555636480427846522421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50359407515307237128696561 37769555636480427846522421)
                    ·
                      refine ⟨3540895840920040110611477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37769555636480427846522421 3540895840920040110611477)
                      ·
                        rfl

theorem cell23_6895870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_6895870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895870 prefixEnd_6895870 := by exact prefixLift 6895870
  have htrace : WordTrace (prefixWord ++ tailWord_6895870) baseStart_6895870 baseEnd_6895870 := by
    simpa [prefixWord, tailWord_6895870, baseEnd_6895870] using wordTrace_append hprefix tailTrace_6895870
  have hstable : (prefixWord ++ tailWord_6895870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895870).length < 2 ^ (prefixWord ++ tailWord_6895870).sum := by decide
  have hdescent : baseEnd_6895870 < baseStart_6895870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895883 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 5]
def baseStart_6895883 : Nat := 118140960795 + 6895883 * 2 ^ 59
def prefixEnd_6895883 : Nat := 4983230072969 + 3 ^ 40 * 6895883 * 2
def baseEnd_6895883 : Nat := 3540902516168548559748917

theorem tailTrace_6895883 : CollatzResearch.WordTrace tailWord_6895883 prefixEnd_6895883 3540902516168548559748917 := by
  unfold tailWord_6895883
  simp only [CollatzResearch.WordTrace]
  refine ⟨251513515676401088898188303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167675677117600725932125535 251513515676401088898188303)
  ·
    refine ⟨377270273514601633347282455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251513515676401088898188303 377270273514601633347282455)
    ·
      refine ⟨565905410271902450020923683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377270273514601633347282455 565905410271902450020923683)
      ·
        refine ⟨848858115407853675031385525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565905410271902450020923683 848858115407853675031385525)
        ·
          refine ⟨79580448319486282034192393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 848858115407853675031385525 79580448319486282034192393)
          ·
            refine ⟨59685336239614711525644295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79580448319486282034192393 59685336239614711525644295)
            ·
              refine ⟨89528004359422067288466443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59685336239614711525644295 89528004359422067288466443)
              ·
                refine ⟨134292006539133100932699665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89528004359422067288466443 134292006539133100932699665)
                ·
                  refine ⟨100719004904349825699524749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134292006539133100932699665 100719004904349825699524749)
                  ·
                    refine ⟨37769626839131184637321781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100719004904349825699524749 37769626839131184637321781)
                    ·
                      refine ⟨3540902516168548559748917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37769626839131184637321781 3540902516168548559748917)
                      ·
                        rfl

theorem cell23_6895883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 5].length) (baseStart_6895883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895883 prefixEnd_6895883 := by exact prefixLift 6895883
  have htrace : WordTrace (prefixWord ++ tailWord_6895883) baseStart_6895883 baseEnd_6895883 := by
    simpa [prefixWord, tailWord_6895883, baseEnd_6895883] using wordTrace_append hprefix tailTrace_6895883
  have hstable : (prefixWord ++ tailWord_6895883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895883).length < 2 ^ (prefixWord ++ tailWord_6895883).sum := by decide
  have hdescent : baseEnd_6895883 < baseStart_6895883 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895900 : List Nat := [2, 2, 3, 1, 1, 1, 1, 4, 1, 4, 3]
def baseStart_6895900 : Nat := 118140960795 + 6895900 * 2 ^ 59
def prefixEnd_6895900 : Nat := 4983230072969 + 3 ^ 40 * 6895900 * 2
def baseEnd_6895900 : Nat := 3540911245339674993236339

theorem tailTrace_6895900 : CollatzResearch.WordTrace tailWord_6895900 prefixEnd_6895900 3540911245339674993236339 := by
  unfold tailWord_6895900
  simp only [CollatzResearch.WordTrace]
  refine ⟨125757067858669750400778577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167676090478226333867704769 125757067858669750400778577)
  ·
    refine ⟨94317800894002312800583933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125757067858669750400778577 94317800894002312800583933)
    ·
      refine ⟨35369175335250867300218975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94317800894002312800583933 35369175335250867300218975)
      ·
        refine ⟨53053763002876300950328463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35369175335250867300218975 53053763002876300950328463)
        ·
          refine ⟨79580644504314451425492695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53053763002876300950328463 79580644504314451425492695)
          ·
            refine ⟨119370966756471677138239043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79580644504314451425492695 119370966756471677138239043)
            ·
              refine ⟨179056450134707515707358565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119370966756471677138239043 179056450134707515707358565)
              ·
                refine ⟨33573084400257659195129731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 179056450134707515707358565 33573084400257659195129731)
                ·
                  refine ⟨50359626600386488792694597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33573084400257659195129731 50359626600386488792694597)
                  ·
                    refine ⟨9442429987572466648630237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50359626600386488792694597 9442429987572466648630237)
                    ·
                      refine ⟨3540911245339674993236339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9442429987572466648630237 3540911245339674993236339)
                      ·
                        rfl

theorem cell23_6895900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_6895900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895900 prefixEnd_6895900 := by exact prefixLift 6895900
  have htrace : WordTrace (prefixWord ++ tailWord_6895900) baseStart_6895900 baseEnd_6895900 := by
    simpa [prefixWord, tailWord_6895900, baseEnd_6895900] using wordTrace_append hprefix tailTrace_6895900
  have hstable : (prefixWord ++ tailWord_6895900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895900).length < 2 ^ (prefixWord ++ tailWord_6895900).sum := by decide
  have hdescent : baseEnd_6895900 < baseStart_6895900 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895937 : List Nat := [1, 2, 5, 2, 2, 1, 1, 1, 8]
def baseStart_6895937 : Nat := 118140960795 + 6895937 * 2 ^ 59
def prefixEnd_6895937 : Nat := 4983230072969 + 3 ^ 40 * 6895937 * 2
def baseEnd_6895937 : Nat := 393436693791543483163741

theorem tailTrace_6895937 : CollatzResearch.WordTrace tailWord_6895937 prefixEnd_6895937 393436693791543483163741 := by
  unfold tailWord_6895937
  simp only [CollatzResearch.WordTrace]
  refine ⟨251515485218205456120654065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167676990145470304080436043 251515485218205456120654065)
  ·
    refine ⟨188636613913654092090490549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251515485218205456120654065 188636613913654092090490549)
    ·
      refine ⟨17684682554405071133483489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 188636613913654092090490549 17684682554405071133483489)
      ·
        refine ⟨13263511915803803350112617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17684682554405071133483489 13263511915803803350112617)
        ·
          refine ⟨9947633936852852512584463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13263511915803803350112617 9947633936852852512584463)
          ·
            refine ⟨14921450905279278768876695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9947633936852852512584463 14921450905279278768876695)
            ·
              refine ⟨22382176357918918153315043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14921450905279278768876695 22382176357918918153315043)
              ·
                refine ⟨33573264536878377229972565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22382176357918918153315043 33573264536878377229972565)
                ·
                  refine ⟨393436693791543483163741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33573264536878377229972565 393436693791543483163741)
                  ·
                    rfl

theorem cell23_6895937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 8].length) (baseStart_6895937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895937 prefixEnd_6895937 := by exact prefixLift 6895937
  have htrace : WordTrace (prefixWord ++ tailWord_6895937) baseStart_6895937 baseEnd_6895937 := by
    simpa [prefixWord, tailWord_6895937, baseEnd_6895937] using wordTrace_append hprefix tailTrace_6895937
  have hstable : (prefixWord ++ tailWord_6895937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895937).length < 2 ^ (prefixWord ++ tailWord_6895937).sum := by decide
  have hdescent : baseEnd_6895937 < baseStart_6895937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895950 : List Nat := [4, 1, 1, 1, 1, 1, 2, 4, 3, 5]
def baseStart_6895950 : Nat := 118140960795 + 6895950 * 2 ^ 59
def prefixEnd_6895950 : Nat := 4983230072969 + 3 ^ 40 * 6895950 * 2
def baseEnd_6895950 : Nat := 1180312306457466599203703

theorem tailTrace_6895950 : CollatzResearch.WordTrace tailWord_6895950 prefixEnd_6895950 1180312306457466599203703 := by
  unfold tailWord_6895950
  simp only [CollatzResearch.WordTrace]
  refine ⟨31439494920894794917609663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167677306244772239560584869 31439494920894794917609663)
  ·
    refine ⟨47159242381342192376414495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31439494920894794917609663 47159242381342192376414495)
    ·
      refine ⟨70738863572013288564621743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47159242381342192376414495 70738863572013288564621743)
      ·
        refine ⟨106108295358019932846932615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70738863572013288564621743 106108295358019932846932615)
        ·
          refine ⟨159162443037029899270398923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106108295358019932846932615 159162443037029899270398923)
          ·
            refine ⟨238743664555544848905598385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159162443037029899270398923 238743664555544848905598385)
            ·
              refine ⟨179057748416658636679198789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238743664555544848905598385 179057748416658636679198789)
              ·
                refine ⟨33573327828123494377349773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 179057748416658636679198789 33573327828123494377349773)
                ·
                  refine ⟨12589997935546310391506165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33573327828123494377349773 12589997935546310391506165)
                  ·
                    refine ⟨1180312306457466599203703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12589997935546310391506165 1180312306457466599203703)
                    ·
                      rfl

theorem cell23_6895950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_6895950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895950 prefixEnd_6895950 := by exact prefixLift 6895950
  have htrace : WordTrace (prefixWord ++ tailWord_6895950) baseStart_6895950 baseEnd_6895950 := by
    simpa [prefixWord, tailWord_6895950, baseEnd_6895950] using wordTrace_append hprefix tailTrace_6895950
  have hstable : (prefixWord ++ tailWord_6895950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895950).length < 2 ^ (prefixWord ++ tailWord_6895950).sum := by decide
  have hdescent : baseEnd_6895950 < baseStart_6895950 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6895997 : List Nat := [1, 4, 1, 1, 2, 3, 2, 1, 4, 4]
def baseStart_6895997 : Nat := 118140960795 + 6895997 * 2 ^ 59
def prefixEnd_6895997 : Nat := 4983230072969 + 3 ^ 40 * 6895997 * 2
def baseEnd_6895997 : Nat := 1180320350987720371241131

theorem tailTrace_6895997 : CollatzResearch.WordTrace tailWord_6895997 prefixEnd_6895997 1180320350987720371241131 := by
  unfold tailWord_6895997
  simp only [CollatzResearch.WordTrace]
  refine ⟨251517673597988086367838245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167678449065325390911892163 251517673597988086367838245)
  ·
    refine ⟨47159563799622766193969671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 251517673597988086367838245 47159563799622766193969671)
    ·
      refine ⟨70739345699434149290954507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47159563799622766193969671 70739345699434149290954507)
      ·
        refine ⟨106109018549151223936431761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70739345699434149290954507 106109018549151223936431761)
        ·
          refine ⟨79581763911863417952323821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106109018549151223936431761 79581763911863417952323821)
          ·
            refine ⟨29843161466948781732121433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79581763911863417952323821 29843161466948781732121433)
            ·
              refine ⟨22382371100211586299091075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29843161466948781732121433 22382371100211586299091075)
              ·
                refine ⟨33573556650317379448636613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22382371100211586299091075 33573556650317379448636613)
                ·
                  refine ⟨6295041871934508646619365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33573556650317379448636613 6295041871934508646619365)
                  ·
                    refine ⟨1180320350987720371241131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6295041871934508646619365 1180320350987720371241131)
                    ·
                      rfl

theorem cell23_6895997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 4, 4].length) (baseStart_6895997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6895997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6895997 prefixEnd_6895997 := by exact prefixLift 6895997
  have htrace : WordTrace (prefixWord ++ tailWord_6895997) baseStart_6895997 baseEnd_6895997 := by
    simpa [prefixWord, tailWord_6895997, baseEnd_6895997] using wordTrace_append hprefix tailTrace_6895997
  have hstable : (prefixWord ++ tailWord_6895997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6895997).length < 2 ^ (prefixWord ++ tailWord_6895997).sum := by decide
  have hdescent : baseEnd_6895997 < baseStart_6895997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6895997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
