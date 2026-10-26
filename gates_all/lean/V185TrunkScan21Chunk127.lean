import V185TrunkScan21Chunk126

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1546129 : List Nat := [1, 2, 2, 1, 1, 1, 13]
def baseStart_1546129 : Nat := 118140960795 + 1546129 * 2 ^ 59
def prefixEnd_1546129 : Nat := 4983230072969 + 3 ^ 40 * 1546129 * 2
def baseEnd_1546129 : Nat := 39205300289159827006271

theorem tailTrace_1546129 : CollatzResearch.WordTrace tailWord_1546129 prefixEnd_1546129 39205300289159827006271 := by
  unfold tailWord_1546129
  simp only [CollatzResearch.WordTrace]
  refine ⟨56391957415646165655593441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37594638277097443770395627 56391957415646165655593441)
  ·
    refine ⟨42293968061734624241695081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56391957415646165655593441 42293968061734624241695081)
    ·
      refine ⟨31720476046300968181271311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42293968061734624241695081 31720476046300968181271311)
      ·
        refine ⟨47580714069451452271906967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31720476046300968181271311 47580714069451452271906967)
        ·
          refine ⟨71371071104177178407860451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47580714069451452271906967 71371071104177178407860451)
          ·
            refine ⟨107056606656265767611790677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71371071104177178407860451 107056606656265767611790677)
            ·
              refine ⟨39205300289159827006271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 107056606656265767611790677 39205300289159827006271)
              ·
                rfl

theorem cell21_1546129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 13].length) (baseStart_1546129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1546129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1546129 prefixEnd_1546129 := by exact prefixLift 1546129
  have htrace : WordTrace (prefixWord ++ tailWord_1546129) baseStart_1546129 baseEnd_1546129 := by
    simpa [prefixWord, tailWord_1546129, baseEnd_1546129] using wordTrace_append hprefix tailTrace_1546129
  have hstable : (prefixWord ++ tailWord_1546129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546129).length < 2 ^ (prefixWord ++ tailWord_1546129).sum := by decide
  have hdescent : baseEnd_1546129 < baseStart_1546129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546132 : List Nat := [2, 4, 2, 1, 1, 2, 2, 1, 6]
def baseStart_1546132 : Nat := 118140960795 + 1546132 * 2 ^ 59
def prefixEnd_1546132 : Nat := 4983230072969 + 3 ^ 40 * 1546132 * 2
def baseEnd_1546132 : Nat := 352848387243311104506433

theorem tailTrace_1546132 : CollatzResearch.WordTrace tailWord_1546132 prefixEnd_1546132 352848387243311104506433 := by
  unfold tailWord_1546132
  simp only [CollatzResearch.WordTrace]
  refine ⟨28196033417317648583976325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37594711223090198111968433 28196033417317648583976325)
  ·
    refine ⟨5286756265747059109495561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28196033417317648583976325 5286756265747059109495561)
    ·
      refine ⟨3965067199310294332121671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5286756265747059109495561 3965067199310294332121671)
      ·
        refine ⟨5947600798965441498182507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3965067199310294332121671 5947600798965441498182507)
        ·
          refine ⟨8921401198448162247273761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5947600798965441498182507 8921401198448162247273761)
          ·
            refine ⟨6691050898836121685455321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8921401198448162247273761 6691050898836121685455321)
            ·
              refine ⟨5018288174127091264091491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6691050898836121685455321 5018288174127091264091491)
              ·
                refine ⟨7527432261190636896137237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5018288174127091264091491 7527432261190636896137237)
                ·
                  refine ⟨352848387243311104506433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7527432261190636896137237 352848387243311104506433)
                  ·
                    rfl

theorem cell21_1546132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_1546132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1546132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1546132 prefixEnd_1546132 := by exact prefixLift 1546132
  have htrace : WordTrace (prefixWord ++ tailWord_1546132) baseStart_1546132 baseEnd_1546132 := by
    simpa [prefixWord, tailWord_1546132, baseEnd_1546132] using wordTrace_append hprefix tailTrace_1546132
  have hstable : (prefixWord ++ tailWord_1546132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546132).length < 2 ^ (prefixWord ++ tailWord_1546132).sum := by decide
  have hdescent : baseEnd_1546132 < baseStart_1546132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546135 : List Nat := [1, 1, 3, 3, 1, 4, 3, 2, 3]
def baseStart_1546135 : Nat := 118140960795 + 1546135 * 2 ^ 59
def prefixEnd_1546135 : Nat := 4983230072969 + 3 ^ 40 * 1546135 * 2
def baseEnd_1546135 : Nat := 352849071884183765956427

theorem tailTrace_1546135 : CollatzResearch.WordTrace tailWord_1546135 prefixEnd_1546135 352849071884183765956427 := by
  unfold tailWord_1546135
  simp only [CollatzResearch.WordTrace]
  refine ⟨56392176253624428680311859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37594784169082952453541239 56392176253624428680311859)
  ·
    refine ⟨84588264380436643020467789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56392176253624428680311859 84588264380436643020467789)
    ·
      refine ⟨31720599142663741132675421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84588264380436643020467789 31720599142663741132675421)
      ·
        refine ⟨11895224678498902924753283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31720599142663741132675421 11895224678498902924753283)
        ·
          refine ⟨17842837017748354387129925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11895224678498902924753283 17842837017748354387129925)
          ·
            refine ⟨3345531940827816447586861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17842837017748354387129925 3345531940827816447586861)
            ·
              refine ⟨1254574477810431167845073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3345531940827816447586861 1254574477810431167845073)
              ·
                refine ⟨940930858357823375883805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1254574477810431167845073 940930858357823375883805)
                ·
                  refine ⟨352849071884183765956427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 940930858357823375883805 352849071884183765956427)
                  ·
                    rfl

theorem cell21_1546135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 2, 3].length) (baseStart_1546135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1546135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1546135 prefixEnd_1546135 := by exact prefixLift 1546135
  have htrace : WordTrace (prefixWord ++ tailWord_1546135) baseStart_1546135 baseEnd_1546135 := by
    simpa [prefixWord, tailWord_1546135, baseEnd_1546135] using wordTrace_append hprefix tailTrace_1546135
  have hstable : (prefixWord ++ tailWord_1546135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546135).length < 2 ^ (prefixWord ++ tailWord_1546135).sum := by decide
  have hdescent : baseEnd_1546135 < baseStart_1546135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546236 : List Nat := [2, 2, 2, 1, 2, 2, 1, 2, 7]
def baseStart_1546236 : Nat := 118140960795 + 1546236 * 2 ^ 59
def prefixEnd_1546236 : Nat := 4983230072969 + 3 ^ 40 * 1546236 * 2
def baseEnd_1546236 : Nat := 352872121460230034772887

theorem tailTrace_1546236 : CollatzResearch.WordTrace tailWord_1546236 prefixEnd_1546236 352872121460230034772887 := by
  unfold tailWord_1546236
  simp only [CollatzResearch.WordTrace]
  refine ⟨28197930013129261464869281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37597240017505681953159041 28197930013129261464869281)
  ·
    refine ⟨21148447509846946098651961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28197930013129261464869281 21148447509846946098651961)
    ·
      refine ⟨15861335632385209573988971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21148447509846946098651961 15861335632385209573988971)
      ·
        refine ⟨23792003448577814360983457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15861335632385209573988971 23792003448577814360983457)
        ·
          refine ⟨17844002586433360770737593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23792003448577814360983457 17844002586433360770737593)
          ·
            refine ⟨13383001939825020578053195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17844002586433360770737593 13383001939825020578053195)
            ·
              refine ⟨20074502909737530867079793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13383001939825020578053195 20074502909737530867079793)
              ·
                refine ⟨15055877182303148150309845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20074502909737530867079793 15055877182303148150309845)
                ·
                  refine ⟨352872121460230034772887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15055877182303148150309845 352872121460230034772887)
                  ·
                    rfl

theorem cell21_1546236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_1546236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1546236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1546236 prefixEnd_1546236 := by exact prefixLift 1546236
  have htrace : WordTrace (prefixWord ++ tailWord_1546236) baseStart_1546236 baseEnd_1546236 := by
    simpa [prefixWord, tailWord_1546236, baseEnd_1546236] using wordTrace_append hprefix tailTrace_1546236
  have hstable : (prefixWord ++ tailWord_1546236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546236).length < 2 ^ (prefixWord ++ tailWord_1546236).sum := by decide
  have hdescent : baseEnd_1546236 < baseStart_1546236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546312 : List Nat := [2, 1, 3, 1, 1, 1, 2, 5, 5]
def baseStart_1546312 : Nat := 118140960795 + 1546312 * 2 ^ 59
def prefixEnd_1546312 : Nat := 4983230072969 + 3 ^ 40 * 1546312 * 2
def baseEnd_1546312 : Nat := 352889465695670791506065

theorem tailTrace_1546312 : CollatzResearch.WordTrace tailWord_1546312 prefixEnd_1546312 352889465695670791506065 := by
  unfold tailWord_1546312
  simp only [CollatzResearch.WordTrace]
  refine ⟨28199315986991593954752595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37599087982655458606336793 28199315986991593954752595)
  ·
    refine ⟨42298973980487390932128893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28199315986991593954752595 42298973980487390932128893)
    ·
      refine ⟨15862115242682771599548335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42298973980487390932128893 15862115242682771599548335)
      ·
        refine ⟨23793172864024157399322503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15862115242682771599548335 23793172864024157399322503)
        ·
          refine ⟨35689759296036236098983755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23793172864024157399322503 35689759296036236098983755)
          ·
            refine ⟨53534638944054354148475633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35689759296036236098983755 53534638944054354148475633)
            ·
              refine ⟨40150979208040765611356725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53534638944054354148475633 40150979208040765611356725)
              ·
                refine ⟨3764154300753821776064693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40150979208040765611356725 3764154300753821776064693)
                ·
                  refine ⟨352889465695670791506065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3764154300753821776064693 352889465695670791506065)
                  ·
                    rfl

theorem cell21_1546312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 5].length) (baseStart_1546312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1546312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1546312 prefixEnd_1546312 := by exact prefixLift 1546312
  have htrace : WordTrace (prefixWord ++ tailWord_1546312) baseStart_1546312 baseEnd_1546312 := by
    simpa [prefixWord, tailWord_1546312, baseEnd_1546312] using wordTrace_append hprefix tailTrace_1546312
  have hstable : (prefixWord ++ tailWord_1546312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546312).length < 2 ^ (prefixWord ++ tailWord_1546312).sum := by decide
  have hdescent : baseEnd_1546312 < baseStart_1546312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546357 : List Nat := [1, 3, 4, 13]
def baseStart_1546357 : Nat := 118140960795 + 1546357 * 2 ^ 59
def prefixEnd_1546357 : Nat := 4983230072969 + 3 ^ 40 * 1546357 * 2
def baseEnd_1546357 : Nat := 1452262285221237503111

theorem tailTrace_1546357 : CollatzResearch.WordTrace tailWord_1546357 prefixEnd_1546357 1452262285221237503111 := by
  unfold tailWord_1546357
  simp only [CollatzResearch.WordTrace]
  refine ⟨56400273258820160594893325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37600182172546773729928883 56400273258820160594893325)
  ·
    refine ⟨21150102472057560223084997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56400273258820160594893325 21150102472057560223084997)
    ·
      refine ⟨3965644213510792541828437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21150102472057560223084997 3965644213510792541828437)
      ·
        refine ⟨1452262285221237503111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 3965644213510792541828437 1452262285221237503111)
        ·
          rfl

theorem cell21_1546357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 13].length) (baseStart_1546357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1546357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1546357 prefixEnd_1546357 := by exact prefixLift 1546357
  have htrace : WordTrace (prefixWord ++ tailWord_1546357) baseStart_1546357 baseEnd_1546357 := by
    simpa [prefixWord, tailWord_1546357, baseEnd_1546357] using wordTrace_append hprefix tailTrace_1546357
  have hstable : (prefixWord ++ tailWord_1546357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546357).length < 2 ^ (prefixWord ++ tailWord_1546357).sum := by decide
  have hdescent : baseEnd_1546357 < baseStart_1546357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546391 : List Nat := [1, 1, 3, 3, 4, 1, 3, 5]
def baseStart_1546391 : Nat := 118140960795 + 1546391 * 2 ^ 59
def prefixEnd_1546391 : Nat := 4983230072969 + 3 ^ 40 * 1546391 * 2
def baseEnd_1546391 : Nat := 117635831523994736563079

theorem tailTrace_1546391 : CollatzResearch.WordTrace tailWord_1546391 prefixEnd_1546391 117635831523994736563079 := by
  unfold tailWord_1546391
  simp only [CollatzResearch.WordTrace]
  refine ⟨56401513340696984401631027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37601008893797989601087351 56401513340696984401631027)
  ·
    refine ⟨84602270011045476602446541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56401513340696984401631027 84602270011045476602446541)
    ·
      refine ⟨31725851254142053725917453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84602270011045476602446541 31725851254142053725917453)
      ·
        refine ⟨11897194220303270147219045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31725851254142053725917453 11897194220303270147219045)
        ·
          refine ⟨2230723916306863152603571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11897194220303270147219045 2230723916306863152603571)
          ·
            refine ⟨3346085874460294728905357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2230723916306863152603571 3346085874460294728905357)
            ·
              refine ⟨1254782202922610523339509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3346085874460294728905357 1254782202922610523339509)
              ·
                refine ⟨117635831523994736563079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1254782202922610523339509 117635831523994736563079)
                ·
                  rfl

theorem cell21_1546391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 5].length) (baseStart_1546391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1546391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1546391 prefixEnd_1546391 := by exact prefixLift 1546391
  have htrace : WordTrace (prefixWord ++ tailWord_1546391) baseStart_1546391 baseEnd_1546391 := by
    simpa [prefixWord, tailWord_1546391, baseEnd_1546391] using wordTrace_append hprefix tailTrace_1546391
  have hstable : (prefixWord ++ tailWord_1546391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546391).length < 2 ^ (prefixWord ++ tailWord_1546391).sum := by decide
  have hdescent : baseEnd_1546391 < baseStart_1546391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546450 : List Nat := [3, 2, 2, 2, 1, 3, 1, 7]
def baseStart_1546450 : Nat := 118140960795 + 1546450 * 2 ^ 59
def prefixEnd_1546450 : Nat := 4983230072969 + 3 ^ 40 * 1546450 * 2
def baseEnd_1546450 : Nat := 117640319725271072735261

theorem tailTrace_1546450 : CollatzResearch.WordTrace tailWord_1546450 prefixEnd_1546450 117640319725271072735261 := by
  unfold tailWord_1546450
  simp only [CollatzResearch.WordTrace]
  refine ⟨14100916311870809369507201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37602443498322158318685869 14100916311870809369507201)
  ·
    refine ⟨10575687233903107027130401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14100916311870809369507201 10575687233903107027130401)
    ·
      refine ⟨7931765425427330270347801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10575687233903107027130401 7931765425427330270347801)
      ·
        refine ⟨5948824069070497702760851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7931765425427330270347801 5948824069070497702760851)
        ·
          refine ⟨8923236103605746554141277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5948824069070497702760851 8923236103605746554141277)
          ·
            refine ⟨3346213538852154957802979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8923236103605746554141277 3346213538852154957802979)
            ·
              refine ⟨5019320308278232436704469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3346213538852154957802979 5019320308278232436704469)
              ·
                refine ⟨117640319725271072735261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5019320308278232436704469 117640319725271072735261)
                ·
                  rfl

theorem cell21_1546450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 7].length) (baseStart_1546450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1546450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1546450 prefixEnd_1546450 := by exact prefixLift 1546450
  have htrace : WordTrace (prefixWord ++ tailWord_1546450) baseStart_1546450 baseEnd_1546450 := by
    simpa [prefixWord, tailWord_1546450, baseEnd_1546450] using wordTrace_append hprefix tailTrace_1546450
  have hstable : (prefixWord ++ tailWord_1546450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546450).length < 2 ^ (prefixWord ++ tailWord_1546450).sum := by decide
  have hdescent : baseEnd_1546450 < baseStart_1546450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546467 : List Nat := [1, 1, 1, 8, 1, 2, 7]
def baseStart_1546467 : Nat := 118140960795 + 1546467 * 2 ^ 59
def prefixEnd_1546467 : Nat := 4983230072969 + 3 ^ 40 * 1546467 * 2
def baseEnd_1546467 : Nat := 39213870978602774046935

theorem tailTrace_1546467 : CollatzResearch.WordTrace tailWord_1546467 prefixEnd_1546467 39213870978602774046935 := by
  unfold tailWord_1546467
  simp only [CollatzResearch.WordTrace]
  refine ⟨56404285288421649381397655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37602856858947766254265103 56404285288421649381397655)
  ·
    refine ⟨84606427932632474072096483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56404285288421649381397655 84606427932632474072096483)
    ·
      refine ⟨126909641898948711108144725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84606427932632474072096483 126909641898948711108144725)
      ·
        refine ⟨1487222366003305208298571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 126909641898948711108144725 1487222366003305208298571)
        ·
          refine ⟨2230833549004957812447857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1487222366003305208298571 2230833549004957812447857)
          ·
            refine ⟨1673125161753718359335893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2230833549004957812447857 1673125161753718359335893)
            ·
              refine ⟨39213870978602774046935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1673125161753718359335893 39213870978602774046935)
              ·
                rfl

theorem cell21_1546467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 7].length) (baseStart_1546467 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1546467 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1546467 prefixEnd_1546467 := by exact prefixLift 1546467
  have htrace : WordTrace (prefixWord ++ tailWord_1546467) baseStart_1546467 baseEnd_1546467 := by
    simpa [prefixWord, tailWord_1546467, baseEnd_1546467] using wordTrace_append hprefix tailTrace_1546467
  have hstable : (prefixWord ++ tailWord_1546467).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546467).length < 2 ^ (prefixWord ++ tailWord_1546467).sum := by decide
  have hdescent : baseEnd_1546467 < baseStart_1546467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546481 : List Nat := [1, 2, 2, 2, 2, 1, 2, 6, 3]
def baseStart_1546481 : Nat := 118140960795 + 1546481 * 2 ^ 59
def prefixEnd_1546481 : Nat := 4983230072969 + 3 ^ 40 * 1546481 * 2
def baseEnd_1546481 : Nat := 352928033798164053189053

theorem tailTrace_1546481 : CollatzResearch.WordTrace tailWord_1546481 prefixEnd_1546481 352928033798164053189053 := by
  unfold tailWord_1546481
  simp only [CollatzResearch.WordTrace]
  refine ⟨56404795910370929772407297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37603197273580619848271531 56404795910370929772407297)
  ·
    refine ⟨42303596932778197329305473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56404795910370929772407297 42303596932778197329305473)
    ·
      refine ⟨31727697699583647996979105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42303596932778197329305473 31727697699583647996979105)
      ·
        refine ⟨23795773274687735997734329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31727697699583647996979105 23795773274687735997734329)
        ·
          refine ⟨17846829956015801998300747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23795773274687735997734329 17846829956015801998300747)
          ·
            refine ⟨26770244934023702997451121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17846829956015801998300747 26770244934023702997451121)
            ·
              refine ⟨20077683700517777248088341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26770244934023702997451121 20077683700517777248088341)
              ·
                refine ⟨941141423461770808504141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20077683700517777248088341 941141423461770808504141)
                ·
                  refine ⟨352928033798164053189053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 941141423461770808504141 352928033798164053189053)
                  ·
                    rfl

theorem cell21_1546481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 6, 3].length) (baseStart_1546481 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1546481 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1546481 prefixEnd_1546481 := by exact prefixLift 1546481
  have htrace : WordTrace (prefixWord ++ tailWord_1546481) baseStart_1546481 baseEnd_1546481 := by
    simpa [prefixWord, tailWord_1546481, baseEnd_1546481] using wordTrace_append hprefix tailTrace_1546481
  have hstable : (prefixWord ++ tailWord_1546481).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546481).length < 2 ^ (prefixWord ++ tailWord_1546481).sum := by decide
  have hdescent : baseEnd_1546481 < baseStart_1546481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546495 : List Nat := [1, 1, 2, 2, 1, 4, 3, 3, 4]
def baseStart_1546495 : Nat := 118140960795 + 1546495 * 2 ^ 59
def prefixEnd_1546495 : Nat := 4983230072969 + 3 ^ 40 * 1546495 * 2
def baseEnd_1546495 : Nat := 352931228788903139955691

theorem tailTrace_1546495 : CollatzResearch.WordTrace tailWord_1546495 prefixEnd_1546495 352931228788903139955691 := by
  unfold tailWord_1546495
  simp only [CollatzResearch.WordTrace]
  refine ⟨56405306532320210163416939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37603537688213473442277959 56405306532320210163416939)
  ·
    refine ⟨84607959798480315245125409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56405306532320210163416939 84607959798480315245125409)
    ·
      refine ⟨63455969848860236433844057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84607959798480315245125409 63455969848860236433844057)
      ·
        refine ⟨47591977386645177325383043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63455969848860236433844057 47591977386645177325383043)
        ·
          refine ⟨71387966079967765988074565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47591977386645177325383043 71387966079967765988074565)
          ·
            refine ⟨13385243639993956122763981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71387966079967765988074565 13385243639993956122763981)
            ·
              refine ⟨5019466364997733546036493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13385243639993956122763981 5019466364997733546036493)
              ·
                refine ⟨1882299886874150079763685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5019466364997733546036493 1882299886874150079763685)
                ·
                  refine ⟨352931228788903139955691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1882299886874150079763685 352931228788903139955691)
                  ·
                    rfl

theorem cell21_1546495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3, 4].length) (baseStart_1546495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1546495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1546495 prefixEnd_1546495 := by exact prefixLift 1546495
  have htrace : WordTrace (prefixWord ++ tailWord_1546495) baseStart_1546495 baseEnd_1546495 := by
    simpa [prefixWord, tailWord_1546495, baseEnd_1546495] using wordTrace_append hprefix tailTrace_1546495
  have hstable : (prefixWord ++ tailWord_1546495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546495).length < 2 ^ (prefixWord ++ tailWord_1546495).sum := by decide
  have hdescent : baseEnd_1546495 < baseStart_1546495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546661 : List Nat := [1, 3, 1, 2, 1, 1, 6, 6]
def baseStart_1546661 : Nat := 118140960795 + 1546661 * 2 ^ 59
def prefixEnd_1546661 : Nat := 4983230072969 + 3 ^ 40 * 1546661 * 2
def baseEnd_1546661 : Nat := 117656370750174580062895

theorem tailTrace_1546661 : CollatzResearch.WordTrace tailWord_1546661 prefixEnd_1546661 117656370750174580062895 := by
  unfold tailWord_1546661
  simp only [CollatzResearch.WordTrace]
  refine ⟨56411361049718820513959837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37607574033145880342639891 56411361049718820513959837)
  ·
    refine ⟨21154260393644557692734939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56411361049718820513959837 21154260393644557692734939)
    ·
      refine ⟨31731390590466836539102409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21154260393644557692734939 31731390590466836539102409)
      ·
        refine ⟨23798542942850127404326807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31731390590466836539102409 23798542942850127404326807)
        ·
          refine ⟨35697814414275191106490211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23798542942850127404326807 35697814414275191106490211)
          ·
            refine ⟨53546721621412786659735317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35697814414275191106490211 53546721621412786659735317)
            ·
              refine ⟨2510002576003724374675093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 53546721621412786659735317 2510002576003724374675093)
              ·
                refine ⟨117656370750174580062895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2510002576003724374675093 117656370750174580062895)
                ·
                  rfl

theorem cell21_1546661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 6].length) (baseStart_1546661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1546661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1546661 prefixEnd_1546661 := by exact prefixLift 1546661
  have htrace : WordTrace (prefixWord ++ tailWord_1546661) baseStart_1546661 baseEnd_1546661 := by
    simpa [prefixWord, tailWord_1546661, baseEnd_1546661] using wordTrace_append hprefix tailTrace_1546661
  have hstable : (prefixWord ++ tailWord_1546661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546661).length < 2 ^ (prefixWord ++ tailWord_1546661).sum := by decide
  have hdescent : baseEnd_1546661 < baseStart_1546661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546751 : List Nat := [1, 1, 2, 2, 1, 2, 3, 2, 7]
def baseStart_1546751 : Nat := 118140960795 + 1546751 * 2 ^ 59
def prefixEnd_1546751 : Nat := 4983230072969 + 3 ^ 40 * 1546751 * 2
def baseEnd_1546751 : Nat := 352989651476703583688501

theorem tailTrace_1546751 : CollatzResearch.WordTrace tailWord_1546751 prefixEnd_1546751 352989651476703583688501 := by
  unfold tailWord_1546751
  simp only [CollatzResearch.WordTrace]
  refine ⟨56414643619392765884736107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37609762412928510589824071 56414643619392765884736107)
  ·
    refine ⟨84621965429089148827104161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56414643619392765884736107 84621965429089148827104161)
    ·
      refine ⟨63466474071816861620328121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84621965429089148827104161 63466474071816861620328121)
      ·
        refine ⟨47599855553862646215246091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63466474071816861620328121 47599855553862646215246091)
        ·
          refine ⟨71399783330793969322869137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47599855553862646215246091 71399783330793969322869137)
          ·
            refine ⟨53549837498095476992151853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71399783330793969322869137 53549837498095476992151853)
            ·
              refine ⟨20081189061785803872056945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53549837498095476992151853 20081189061785803872056945)
              ·
                refine ⟨15060891796339352904042709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20081189061785803872056945 15060891796339352904042709)
                ·
                  refine ⟨352989651476703583688501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15060891796339352904042709 352989651476703583688501)
                  ·
                    rfl

theorem cell21_1546751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 7].length) (baseStart_1546751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1546751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1546751 prefixEnd_1546751 := by exact prefixLift 1546751
  have htrace : WordTrace (prefixWord ++ tailWord_1546751) baseStart_1546751 baseEnd_1546751 := by
    simpa [prefixWord, tailWord_1546751, baseEnd_1546751] using wordTrace_append hprefix tailTrace_1546751
  have hstable : (prefixWord ++ tailWord_1546751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546751).length < 2 ^ (prefixWord ++ tailWord_1546751).sum := by decide
  have hdescent : baseEnd_1546751 < baseStart_1546751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546788 : List Nat := [2, 3, 1, 5, 1, 2, 2, 5]
def baseStart_1546788 : Nat := 118140960795 + 1546788 * 2 ^ 59
def prefixEnd_1546788 : Nat := 4983230072969 + 3 ^ 40 * 1546788 * 2
def baseEnd_1546788 : Nat := 117666031793599913857253

theorem tailTrace_1546788 : CollatzResearch.WordTrace tailWord_1546788 prefixEnd_1546788 117666031793599913857253 := by
  unfold tailWord_1546788
  simp only [CollatzResearch.WordTrace]
  refine ⟨28207996560129360601916509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37610662080172480802555345 28207996560129360601916509)
  ·
    refine ⟨10577998710048510225718691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28207996560129360601916509 10577998710048510225718691)
    ·
      refine ⟨15866998065072765338578037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10577998710048510225718691 15866998065072765338578037)
      ·
        refine ⟨1487531068600571750491691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15866998065072765338578037 1487531068600571750491691)
        ·
          refine ⟨2231296602900857625737537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1487531068600571750491691 2231296602900857625737537)
          ·
            refine ⟨1673472452175643219303153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2231296602900857625737537 1673472452175643219303153)
            ·
              refine ⟨1255104339131732414477365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1673472452175643219303153 1255104339131732414477365)
              ·
                refine ⟨117666031793599913857253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1255104339131732414477365 117666031793599913857253)
                ·
                  rfl

theorem cell21_1546788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 5].length) (baseStart_1546788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1546788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1546788 prefixEnd_1546788 := by exact prefixLift 1546788
  have htrace : WordTrace (prefixWord ++ tailWord_1546788) baseStart_1546788 baseEnd_1546788 := by
    simpa [prefixWord, tailWord_1546788, baseEnd_1546788] using wordTrace_append hprefix tailTrace_1546788
  have hstable : (prefixWord ++ tailWord_1546788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546788).length < 2 ^ (prefixWord ++ tailWord_1546788).sum := by decide
  have hdescent : baseEnd_1546788 < baseStart_1546788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546813 : List Nat := [1, 4, 1, 3, 2, 1, 9]
def baseStart_1546813 : Nat := 118140960795 + 1546813 * 2 ^ 59
def prefixEnd_1546813 : Nat := 4983230072969 + 3 ^ 40 * 1546813 * 2
def baseEnd_1546813 : Nat := 39222644524600583739449

theorem tailTrace_1546813 : CollatzResearch.WordTrace tailWord_1546813 prefixEnd_1546813 39222644524600583739449 := by
  unfold tailWord_1546813
  simp only [CollatzResearch.WordTrace]
  refine ⟨56416904945168150473493093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37611269963445433648995395 56416904945168150473493093)
  ·
    refine ⟨10578169677219028213779955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56416904945168150473493093 10578169677219028213779955)
    ·
      refine ⟨15867254515828542320669933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10578169677219028213779955 15867254515828542320669933)
      ·
        refine ⟨5950220443435703370251225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15867254515828542320669933 5950220443435703370251225)
        ·
          refine ⟨4462665332576777527688419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5950220443435703370251225 4462665332576777527688419)
          ·
            refine ⟨6693997998865166291532629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4462665332576777527688419 6693997998865166291532629)
            ·
              refine ⟨39222644524600583739449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6693997998865166291532629 39222644524600583739449)
              ·
                rfl

theorem cell21_1546813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 9].length) (baseStart_1546813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1546813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1546813 prefixEnd_1546813 := by exact prefixLift 1546813
  have htrace : WordTrace (prefixWord ++ tailWord_1546813) baseStart_1546813 baseEnd_1546813 := by
    simpa [prefixWord, tailWord_1546813, baseEnd_1546813] using wordTrace_append hprefix tailTrace_1546813
  have hstable : (prefixWord ++ tailWord_1546813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546813).length < 2 ^ (prefixWord ++ tailWord_1546813).sum := by decide
  have hdescent : baseEnd_1546813 < baseStart_1546813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546957 : List Nat := [1, 6, 2, 1, 3, 1, 2, 5]
def baseStart_1546957 : Nat := 118140960795 + 1546957 * 2 ^ 59
def prefixEnd_1546957 : Nat := 4983230072969 + 3 ^ 40 * 1546957 * 2
def baseEnd_1546957 : Nat := 117678887827764334418249

theorem tailTrace_1546957 : CollatzResearch.WordTrace tailWord_1546957 prefixEnd_1546957 117678887827764334418249 := by
  unfold tailWord_1546957
  simp only [CollatzResearch.WordTrace]
  refine ⟨56422157056646463066735125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37614771371097642044490083 56422157056646463066735125)
  ·
    refine ⟨2644788612030302956253209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 56422157056646463066735125 2644788612030302956253209)
    ·
      refine ⟨1983591459022727217189907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2644788612030302956253209 1983591459022727217189907)
      ·
        refine ⟨2975387188534090825784861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1983591459022727217189907 2975387188534090825784861)
        ·
          refine ⟨1115770195700284059669323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2975387188534090825784861 1115770195700284059669323)
          ·
            refine ⟨1673655293550426089503985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1115770195700284059669323 1673655293550426089503985)
            ·
              refine ⟨1255241470162819567127989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1673655293550426089503985 1255241470162819567127989)
              ·
                refine ⟨117678887827764334418249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1255241470162819567127989 117678887827764334418249)
                ·
                  rfl

theorem cell21_1546957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 5].length) (baseStart_1546957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1546957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1546957 prefixEnd_1546957 := by exact prefixLift 1546957
  have htrace : WordTrace (prefixWord ++ tailWord_1546957) baseStart_1546957 baseEnd_1546957 := by
    simpa [prefixWord, tailWord_1546957, baseEnd_1546957] using wordTrace_append hprefix tailTrace_1546957
  have hstable : (prefixWord ++ tailWord_1546957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546957).length < 2 ^ (prefixWord ++ tailWord_1546957).sum := by decide
  have hdescent : baseEnd_1546957 < baseStart_1546957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547044 : List Nat := [2, 3, 1, 3, 3, 1, 2, 2, 4]
def baseStart_1547044 : Nat := 118140960795 + 1547044 * 2 ^ 59
def prefixEnd_1547044 : Nat := 4983230072969 + 3 ^ 40 * 1547044 * 2
def baseEnd_1547044 : Nat := 353056518068600185304569

theorem tailTrace_1547044 : CollatzResearch.WordTrace tailWord_1547044 prefixEnd_1547044 353056518068600185304569 := by
  unfold tailWord_1547044
  simp only [CollatzResearch.WordTrace]
  refine ⟨28212665103665638462576093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37616886804887517950101457 28212665103665638462576093)
  ·
    refine ⟨10579749413874614423466035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28212665103665638462576093 10579749413874614423466035)
    ·
      refine ⟨15869624120811921635199053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10579749413874614423466035 15869624120811921635199053)
      ·
        refine ⟨5951109045304470613199645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15869624120811921635199053 5951109045304470613199645)
        ·
          refine ⟨2231665891989176479949867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5951109045304470613199645 2231665891989176479949867)
          ·
            refine ⟨3347498837983764719924801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2231665891989176479949867 3347498837983764719924801)
            ·
              refine ⟨2510624128487823539943601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3347498837983764719924801 2510624128487823539943601)
              ·
                refine ⟨1882968096365867654957701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2510624128487823539943601 1882968096365867654957701)
                ·
                  refine ⟨353056518068600185304569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1882968096365867654957701 353056518068600185304569)
                  ·
                    rfl

theorem cell21_1547044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_1547044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1547044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1547044 prefixEnd_1547044 := by exact prefixLift 1547044
  have htrace : WordTrace (prefixWord ++ tailWord_1547044) baseStart_1547044 baseEnd_1547044 := by
    simpa [prefixWord, tailWord_1547044, baseEnd_1547044] using wordTrace_append hprefix tailTrace_1547044
  have hstable : (prefixWord ++ tailWord_1547044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547044).length < 2 ^ (prefixWord ++ tailWord_1547044).sum := by decide
  have hdescent : baseEnd_1547044 < baseStart_1547044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547131 : List Nat := [1, 1, 1, 1, 1, 5, 4, 2, 5]
def baseStart_1547131 : Nat := 118140960795 + 1547131 * 2 ^ 59
def prefixEnd_1547131 : Nat := 4983230072969 + 3 ^ 40 * 1547131 * 2
def baseEnd_1547131 : Nat := 353076372653907367354391

theorem tailTrace_1547131 : CollatzResearch.WordTrace tailWord_1547131 prefixEnd_1547131 353076372653907367354391 := by
  unfold tailWord_1547131
  simp only [CollatzResearch.WordTrace]
  refine ⟨56428503358016090783569247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37619002238677393855712831 56428503358016090783569247)
  ·
    refine ⟨84642755037024136175353871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56428503358016090783569247 84642755037024136175353871)
    ·
      refine ⟨126964132555536204263030807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84642755037024136175353871 126964132555536204263030807)
      ·
        refine ⟨190446198833304306394546211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126964132555536204263030807 190446198833304306394546211)
        ·
          refine ⟨285669298249956459591819317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190446198833304306394546211 285669298249956459591819317)
          ·
            refine ⟨26781496710933418086733061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 285669298249956459591819317 26781496710933418086733061)
            ·
              refine ⟨5021530633300015891262449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26781496710933418086733061 5021530633300015891262449)
              ·
                refine ⟨3766147974975011918446837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5021530633300015891262449 3766147974975011918446837)
                ·
                  refine ⟨353076372653907367354391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3766147974975011918446837 353076372653907367354391)
                  ·
                    rfl

theorem cell21_1547131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 5].length) (baseStart_1547131 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1547131 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1547131 prefixEnd_1547131 := by exact prefixLift 1547131
  have htrace : WordTrace (prefixWord ++ tailWord_1547131) baseStart_1547131 baseEnd_1547131 := by
    simpa [prefixWord, tailWord_1547131, baseEnd_1547131] using wordTrace_append hprefix tailTrace_1547131
  have hstable : (prefixWord ++ tailWord_1547131).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547131).length < 2 ^ (prefixWord ++ tailWord_1547131).sum := by decide
  have hdescent : baseEnd_1547131 < baseStart_1547131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547300 : List Nat := [2, 3, 1, 4, 1, 1, 2, 2, 5]
def baseStart_1547300 : Nat := 118140960795 + 1547300 * 2 ^ 59
def prefixEnd_1547300 : Nat := 4983230072969 + 3 ^ 40 * 1547300 * 2
def baseEnd_1547300 : Nat := 353114940756400629037379

theorem tailTrace_1547300 : CollatzResearch.WordTrace tailWord_1547300 prefixEnd_1547300 353114940756400629037379 := by
  unfold tailWord_1547300
  simp only [CollatzResearch.WordTrace]
  refine ⟨28217333647201916323235677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37623111529602555097647569 28217333647201916323235677)
  ·
    refine ⟨10581500117700718621213379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28217333647201916323235677 10581500117700718621213379)
    ·
      refine ⟨15872250176551077931820069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10581500117700718621213379 15872250176551077931820069)
      ·
        refine ⟨2976046908103327112216263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15872250176551077931820069 2976046908103327112216263)
        ·
          refine ⟨4464070362154990668324395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2976046908103327112216263 4464070362154990668324395)
          ·
            refine ⟨6696105543232486002486593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4464070362154990668324395 6696105543232486002486593)
            ·
              refine ⟨5022079157424364501864945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6696105543232486002486593 5022079157424364501864945)
              ·
                refine ⟨3766559368068273376398709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5022079157424364501864945 3766559368068273376398709)
                ·
                  refine ⟨353114940756400629037379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3766559368068273376398709 353114940756400629037379)
                  ·
                    rfl

theorem cell21_1547300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_1547300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1547300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1547300 prefixEnd_1547300 := by exact prefixLift 1547300
  have htrace : WordTrace (prefixWord ++ tailWord_1547300) baseStart_1547300 baseEnd_1547300 := by
    simpa [prefixWord, tailWord_1547300, baseEnd_1547300] using wordTrace_append hprefix tailTrace_1547300
  have hstable : (prefixWord ++ tailWord_1547300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547300).length < 2 ^ (prefixWord ++ tailWord_1547300).sum := by decide
  have hdescent : baseEnd_1547300 < baseStart_1547300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547303 : List Nat := [1, 1, 7, 1, 1, 3, 2, 5]
def baseStart_1547303 : Nat := 118140960795 + 1547303 * 2 ^ 59
def prefixEnd_1547303 : Nat := 4983230072969 + 3 ^ 40 * 1547303 * 2
def baseEnd_1547303 : Nat := 117705208465757763495791

theorem tailTrace_1547303 : CollatzResearch.WordTrace tailWord_1547303 prefixEnd_1547303 117705208465757763495791 := by
  unfold tailWord_1547303
  simp only [CollatzResearch.WordTrace]
  refine ⟨56434776713392964158830563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37623184475595309439220375 56434776713392964158830563)
  ·
    refine ⟨84652165070089446238245845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56434776713392964158830563 84652165070089446238245845)
    ·
      refine ⟨1984035118830221396208887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 84652165070089446238245845 1984035118830221396208887)
      ·
        refine ⟨2976052678245332094313331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1984035118830221396208887 2976052678245332094313331)
        ·
          refine ⟨4464079017367998141469997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2976052678245332094313331 4464079017367998141469997)
          ·
            refine ⟨1674029631512999303051249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4464079017367998141469997 1674029631512999303051249)
            ·
              refine ⟨1255522223634749477288437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1674029631512999303051249 1255522223634749477288437)
              ·
                refine ⟨117705208465757763495791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1255522223634749477288437 117705208465757763495791)
                ·
                  rfl

theorem cell21_1547303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 5].length) (baseStart_1547303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1547303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1547303 prefixEnd_1547303 := by exact prefixLift 1547303
  have htrace : WordTrace (prefixWord ++ tailWord_1547303) baseStart_1547303 baseEnd_1547303 := by
    simpa [prefixWord, tailWord_1547303, baseEnd_1547303] using wordTrace_append hprefix tailTrace_1547303
  have hstable : (prefixWord ++ tailWord_1547303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547303).length < 2 ^ (prefixWord ++ tailWord_1547303).sum := by decide
  have hdescent : baseEnd_1547303 < baseStart_1547303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547334 : List Nat := [6, 1, 1, 1, 1, 4, 1, 1, 5]
def baseStart_1547334 : Nat := 118140960795 + 1547334 * 2 ^ 59
def prefixEnd_1547334 : Nat := 4983230072969 + 3 ^ 40 * 1547334 * 2
def baseEnd_1547334 : Nat := 353122700019624125470643

theorem tailTrace_1547334 : CollatzResearch.WordTrace tailWord_1547334 prefixEnd_1547334 353122700019624125470643 := by
  unfold tailWord_1547334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1763622105508770514162783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37623938250853770968806037 1763622105508770514162783)
  ·
    refine ⟨2645433158263155771244175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1763622105508770514162783 2645433158263155771244175)
    ·
      refine ⟨3968149737394733656866263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2645433158263155771244175 3968149737394733656866263)
      ·
        refine ⟨5952224606092100485299395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3968149737394733656866263 5952224606092100485299395)
        ·
          refine ⟨8928336909138150727949093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5952224606092100485299395 8928336909138150727949093)
          ·
            refine ⟨1674063170463403261490455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8928336909138150727949093 1674063170463403261490455)
            ·
              refine ⟨2511094755695104892235683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1674063170463403261490455 2511094755695104892235683)
              ·
                refine ⟨3766642133542657338353525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2511094755695104892235683 3766642133542657338353525)
                ·
                  refine ⟨353122700019624125470643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3766642133542657338353525 353122700019624125470643)
                  ·
                    rfl

theorem cell21_1547334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_1547334 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1547334 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1547334 prefixEnd_1547334 := by exact prefixLift 1547334
  have htrace : WordTrace (prefixWord ++ tailWord_1547334) baseStart_1547334 baseEnd_1547334 := by
    simpa [prefixWord, tailWord_1547334, baseEnd_1547334] using wordTrace_append hprefix tailTrace_1547334
  have hstable : (prefixWord ++ tailWord_1547334).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547334).length < 2 ^ (prefixWord ++ tailWord_1547334).sum := by decide
  have hdescent : baseEnd_1547334 < baseStart_1547334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547376 : List Nat := [2, 1, 1, 1, 5, 1, 2, 5, 3]
def baseStart_1547376 : Nat := 118140960795 + 1547376 * 2 ^ 59
def prefixEnd_1547376 : Nat := 4983230072969 + 3 ^ 40 * 1547376 * 2
def baseEnd_1547376 : Nat := 353132284991841385770557

theorem tailTrace_1547376 : CollatzResearch.WordTrace tailWord_1547376 prefixEnd_1547376 353132284991841385770557 := by
  unfold tailWord_1547376
  simp only [CollatzResearch.WordTrace]
  refine ⟨28218719621064248813118991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37624959494752331750825321 28218719621064248813118991)
  ·
    refine ⟨42328079431596373219678487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28218719621064248813118991 42328079431596373219678487)
    ·
      refine ⟨63492119147394559829517731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42328079431596373219678487 63492119147394559829517731)
      ·
        refine ⟨95238178721091839744276597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63492119147394559829517731 95238178721091839744276597)
        ·
          refine ⟨8928579255102359976025931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95238178721091839744276597 8928579255102359976025931)
          ·
            refine ⟨13392868882653539964038897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8928579255102359976025931 13392868882653539964038897)
            ·
              refine ⟨10044651661990154973029173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13392868882653539964038897 10044651661990154973029173)
              ·
                refine ⟨941686093311577028721485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10044651661990154973029173 941686093311577028721485)
                ·
                  refine ⟨353132284991841385770557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 941686093311577028721485 353132284991841385770557)
                  ·
                    rfl

theorem cell21_1547376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 5, 3].length) (baseStart_1547376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1547376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1547376 prefixEnd_1547376 := by exact prefixLift 1547376
  have htrace : WordTrace (prefixWord ++ tailWord_1547376) baseStart_1547376 baseEnd_1547376 := by
    simpa [prefixWord, tailWord_1547376, baseEnd_1547376] using wordTrace_append hprefix tailTrace_1547376
  have hstable : (prefixWord ++ tailWord_1547376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547376).length < 2 ^ (prefixWord ++ tailWord_1547376).sum := by decide
  have hdescent : baseEnd_1547376 < baseStart_1547376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547393 : List Nat := [1, 2, 4, 2, 2, 2, 1, 4, 3]
def baseStart_1547393 : Nat := 118140960795 + 1547393 * 2 ^ 59
def prefixEnd_1547393 : Nat := 4983230072969 + 3 ^ 40 * 1547393 * 2
def baseEnd_1547393 : Nat := 353136164623453133987189

theorem tailTrace_1547393 : CollatzResearch.WordTrace tailWord_1547393 prefixEnd_1547393 353136164623453133987189 := by
  unfold tailWord_1547393
  simp only [CollatzResearch.WordTrace]
  refine ⟨56438059283066909529606833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37625372855377939686404555 56438059283066909529606833)
  ·
    refine ⟨42328544462300182147205125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56438059283066909529606833 42328544462300182147205125)
    ·
      refine ⟨7936602086681284152600961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42328544462300182147205125 7936602086681284152600961)
      ·
        refine ⟨5952451565010963114450721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7936602086681284152600961 5952451565010963114450721)
        ·
          refine ⟨4464338673758222335838041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5952451565010963114450721 4464338673758222335838041)
          ·
            refine ⟨3348254005318666751878531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4464338673758222335838041 3348254005318666751878531)
            ·
              refine ⟨5022381007978000127817797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3348254005318666751878531 5022381007978000127817797)
              ·
                refine ⟨941696438995875023965837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5022381007978000127817797 941696438995875023965837)
                ·
                  refine ⟨353136164623453133987189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 941696438995875023965837 353136164623453133987189)
                  ·
                    rfl

theorem cell21_1547393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 4, 3].length) (baseStart_1547393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1547393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1547393 prefixEnd_1547393 := by exact prefixLift 1547393
  have htrace : WordTrace (prefixWord ++ tailWord_1547393) baseStart_1547393 baseEnd_1547393 := by
    simpa [prefixWord, tailWord_1547393, baseEnd_1547393] using wordTrace_append hprefix tailTrace_1547393
  have hstable : (prefixWord ++ tailWord_1547393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547393).length < 2 ^ (prefixWord ++ tailWord_1547393).sum := by decide
  have hdescent : baseEnd_1547393 < baseStart_1547393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547421 : List Nat := [1, 4, 2, 1, 1, 2, 5, 5]
def baseStart_1547421 : Nat := 118140960795 + 1547421 * 2 ^ 59
def prefixEnd_1547421 : Nat := 4983230072969 + 3 ^ 40 * 1547421 * 2
def baseEnd_1547421 : Nat := 117714184868310435840155

theorem tailTrace_1547421 : CollatzResearch.WordTrace tailWord_1547421 prefixEnd_1547421 117714184868310435840155 := by
  unfold tailWord_1547421
  simp only [CollatzResearch.WordTrace]
  refine ⟨56439080526965470311626117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37626053684643646874417411 56439080526965470311626117)
  ·
    refine ⟨10582327598806025683429897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56439080526965470311626117 10582327598806025683429897)
    ·
      refine ⟨7936745699104519262572423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10582327598806025683429897 7936745699104519262572423)
      ·
        refine ⟨11905118548656778893858635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7936745699104519262572423 11905118548656778893858635)
        ·
          refine ⟨17857677822985168340787953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11905118548656778893858635 17857677822985168340787953)
          ·
            refine ⟨13393258367238876255590965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17857677822985168340787953 13393258367238876255590965)
            ·
              refine ⟨1255617971928644648961653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13393258367238876255590965 1255617971928644648961653)
              ·
                refine ⟨117714184868310435840155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1255617971928644648961653 117714184868310435840155)
                ·
                  rfl

theorem cell21_1547421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 5].length) (baseStart_1547421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1547421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1547421 prefixEnd_1547421 := by exact prefixLift 1547421
  have htrace : WordTrace (prefixWord ++ tailWord_1547421) baseStart_1547421 baseEnd_1547421 := by
    simpa [prefixWord, tailWord_1547421, baseEnd_1547421] using wordTrace_append hprefix tailTrace_1547421
  have hstable : (prefixWord ++ tailWord_1547421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547421).length < 2 ^ (prefixWord ++ tailWord_1547421).sum := by decide
  have hdescent : baseEnd_1547421 < baseStart_1547421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547452 : List Nat := [2, 2, 2, 3, 2, 2, 2, 1, 5]
def baseStart_1547452 : Nat := 118140960795 + 1547452 * 2 ^ 59
def prefixEnd_1547452 : Nat := 4983230072969 + 3 ^ 40 * 1547452 * 2
def baseEnd_1547452 : Nat := 353149629227282142503735

theorem tailTrace_1547452 : CollatzResearch.WordTrace tailWord_1547452 prefixEnd_1547452 353149629227282142503735 := by
  unfold tailWord_1547452
  simp only [CollatzResearch.WordTrace]
  refine ⟨28220105594926581303002305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37626807459902108404003073 28220105594926581303002305)
  ·
    refine ⟨21165079196194935977251729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28220105594926581303002305 21165079196194935977251729)
    ·
      refine ⟨15873809397146201982938797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21165079196194935977251729 15873809397146201982938797)
      ·
        refine ⟨5952678523929825743602049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15873809397146201982938797 5952678523929825743602049)
        ·
          refine ⟨4464508892947369307701537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5952678523929825743602049 4464508892947369307701537)
          ·
            refine ⟨3348381669710526980776153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4464508892947369307701537 3348381669710526980776153)
            ·
              refine ⟨2511286252282895235582115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3348381669710526980776153 2511286252282895235582115)
              ·
                refine ⟨3766929378424342853373173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2511286252282895235582115 3766929378424342853373173)
                ·
                  refine ⟨353149629227282142503735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3766929378424342853373173 353149629227282142503735)
                  ·
                    rfl

theorem cell21_1547452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 5].length) (baseStart_1547452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1547452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1547452 prefixEnd_1547452 := by exact prefixLift 1547452
  have htrace : WordTrace (prefixWord ++ tailWord_1547452) baseStart_1547452 baseEnd_1547452 := by
    simpa [prefixWord, tailWord_1547452, baseEnd_1547452] using wordTrace_append hprefix tailTrace_1547452
  have hstable : (prefixWord ++ tailWord_1547452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547452).length < 2 ^ (prefixWord ++ tailWord_1547452).sum := by decide
  have hdescent : baseEnd_1547452 < baseStart_1547452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547458 : List Nat := [3, 5, 1, 1, 2, 1, 3, 1, 4]
def baseStart_1547458 : Nat := 118140960795 + 1547458 * 2 ^ 59
def prefixEnd_1547458 : Nat := 4983230072969 + 3 ^ 40 * 1547458 * 2
def baseEnd_1547458 : Nat := 353150998509027465403723

theorem tailTrace_1547458 : CollatzResearch.WordTrace tailWord_1547458 prefixEnd_1547458 353150998509027465403723 := by
  unfold tailWord_1547458
  simp only [CollatzResearch.WordTrace]
  refine ⟨14110107506957856407680757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37626953351887617087148685 14110107506957856407680757)
  ·
    refine ⟨1322822578777299038220071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14110107506957856407680757 1322822578777299038220071)
    ·
      refine ⟨1984233868165948557330107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1322822578777299038220071 1984233868165948557330107)
      ·
        refine ⟨2976350802248922835995161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1984233868165948557330107 2976350802248922835995161)
        ·
          refine ⟨2232263101686692126996371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2976350802248922835995161 2232263101686692126996371)
          ·
            refine ⟨3348394652530038190494557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2232263101686692126996371 3348394652530038190494557)
            ·
              refine ⟨1255647994698764321435459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3348394652530038190494557 1255647994698764321435459)
              ·
                refine ⟨1883471992048146482153189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1255647994698764321435459 1883471992048146482153189)
                ·
                  refine ⟨353150998509027465403723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1883471992048146482153189 353150998509027465403723)
                  ·
                    rfl

theorem cell21_1547458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_1547458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1547458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1547458 prefixEnd_1547458 := by exact prefixLift 1547458
  have htrace : WordTrace (prefixWord ++ tailWord_1547458) baseStart_1547458 baseEnd_1547458 := by
    simpa [prefixWord, tailWord_1547458, baseEnd_1547458] using wordTrace_append hprefix tailTrace_1547458
  have hstable : (prefixWord ++ tailWord_1547458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547458).length < 2 ^ (prefixWord ++ tailWord_1547458).sum := by decide
  have hdescent : baseEnd_1547458 < baseStart_1547458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547562 : List Nat := [3, 1, 4, 2, 1, 1, 4, 2, 3]
def baseStart_1547562 : Nat := 118140960795 + 1547562 * 2 ^ 59
def prefixEnd_1547562 : Nat := 4983230072969 + 3 ^ 40 * 1547562 * 2
def baseEnd_1547562 : Nat := 353174732725946395670177

theorem tailTrace_1547562 : CollatzResearch.WordTrace tailWord_1547562 prefixEnd_1547562 353174732725946395670177 := by
  unfold tailWord_1547562
  simp only [CollatzResearch.WordTrace]
  refine ⟨14111055804863662848127235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37629482146303100928339293 14111055804863662848127235)
  ·
    refine ⟨21166583707295494272190853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14111055804863662848127235 21166583707295494272190853)
    ·
      refine ⟨3968734445117905176035785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21166583707295494272190853 3968734445117905176035785)
      ·
        refine ⟨2976550833838428882026839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3968734445117905176035785 2976550833838428882026839)
        ·
          refine ⟨4464826250757643323040259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2976550833838428882026839 4464826250757643323040259)
          ·
            refine ⟨6697239376136464984560389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4464826250757643323040259 6697239376136464984560389)
            ·
              refine ⟨1255732383025587184605073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6697239376136464984560389 1255732383025587184605073)
              ·
                refine ⟨941799287269190388453805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1255732383025587184605073 941799287269190388453805)
                ·
                  refine ⟨353174732725946395670177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 941799287269190388453805 353174732725946395670177)
                  ·
                    rfl

theorem cell21_1547562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 2, 3].length) (baseStart_1547562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1547562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1547562 prefixEnd_1547562 := by exact prefixLift 1547562
  have htrace : WordTrace (prefixWord ++ tailWord_1547562) baseStart_1547562 baseEnd_1547562 := by
    simpa [prefixWord, tailWord_1547562, baseEnd_1547562] using wordTrace_append hprefix tailTrace_1547562
  have hstable : (prefixWord ++ tailWord_1547562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547562).length < 2 ^ (prefixWord ++ tailWord_1547562).sum := by decide
  have hdescent : baseEnd_1547562 < baseStart_1547562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547573 : List Nat := [1, 3, 3, 1, 2, 4, 1, 6]
def baseStart_1547573 : Nat := 118140960795 + 1547573 * 2 ^ 59
def prefixEnd_1547573 : Nat := 4983230072969 + 3 ^ 40 * 1547573 * 2
def baseEnd_1547573 : Nat := 117725747691937606995607

theorem tailTrace_1547573 : CollatzResearch.WordTrace tailWord_1547573 prefixEnd_1547573 117725747691937606995607 := by
  unfold tailWord_1547573
  simp only [CollatzResearch.WordTrace]
  refine ⟨56444624422414800271159373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37629749614943200180772915 56444624422414800271159373)
  ·
    refine ⟨21166734158405550101684765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56444624422414800271159373 21166734158405550101684765)
    ·
      refine ⟨7937525309402081288131787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21166734158405550101684765 7937525309402081288131787)
      ·
        refine ⟨11906287964103121932197681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7937525309402081288131787 11906287964103121932197681)
        ·
          refine ⟨8929715973077341449148261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11906287964103121932197681 8929715973077341449148261)
          ·
            refine ⟨1674321744952001521715299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8929715973077341449148261 1674321744952001521715299)
            ·
              refine ⟨2511482617428002282572949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1674321744952001521715299 2511482617428002282572949)
              ·
                refine ⟨117725747691937606995607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2511482617428002282572949 117725747691937606995607)
                ·
                  rfl

theorem cell21_1547573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 6].length) (baseStart_1547573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1547573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1547573 prefixEnd_1547573 := by exact prefixLift 1547573
  have htrace : WordTrace (prefixWord ++ tailWord_1547573) baseStart_1547573 baseEnd_1547573 := by
    simpa [prefixWord, tailWord_1547573, baseEnd_1547573] using wordTrace_append hprefix tailTrace_1547573
  have hstable : (prefixWord ++ tailWord_1547573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547573).length < 2 ^ (prefixWord ++ tailWord_1547573).sum := by decide
  have hdescent : baseEnd_1547573 < baseStart_1547573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547601 : List Nat := [1, 2, 2, 1, 4, 1, 2, 2, 6]
def baseStart_1547601 : Nat := 118140960795 + 1547601 * 2 ^ 59
def prefixEnd_1547601 : Nat := 4983230072969 + 3 ^ 40 * 1547601 * 2
def baseEnd_1547601 : Nat := 353183633057290994520097

theorem tailTrace_1547601 : CollatzResearch.WordTrace tailWord_1547601 prefixEnd_1547601 353183633057290994520097 := by
  unfold tailWord_1547601
  simp only [CollatzResearch.WordTrace]
  refine ⟨56445645666313361053178657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37630430444208907368785771 56445645666313361053178657)
  ·
    refine ⟨42334234249735020789883993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56445645666313361053178657 42334234249735020789883993)
    ·
      refine ⟨31750675687301265592412995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42334234249735020789883993 31750675687301265592412995)
      ·
        refine ⟨47626013530951898388619493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31750675687301265592412995 47626013530951898388619493)
        ·
          refine ⟨8929877537053480947866155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47626013530951898388619493 8929877537053480947866155)
          ·
            refine ⟨13394816305580221421799233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8929877537053480947866155 13394816305580221421799233)
            ·
              refine ⟨10046112229185166066349425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13394816305580221421799233 10046112229185166066349425)
              ·
                refine ⟨7534584171888874549762069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10046112229185166066349425 7534584171888874549762069)
                ·
                  refine ⟨353183633057290994520097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7534584171888874549762069 353183633057290994520097)
                  ·
                    rfl

theorem cell21_1547601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 6].length) (baseStart_1547601 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1547601 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1547601 prefixEnd_1547601 := by exact prefixLift 1547601
  have htrace : WordTrace (prefixWord ++ tailWord_1547601) baseStart_1547601 baseEnd_1547601 := by
    simpa [prefixWord, tailWord_1547601, baseEnd_1547601] using wordTrace_append hprefix tailTrace_1547601
  have hstable : (prefixWord ++ tailWord_1547601).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547601).length < 2 ^ (prefixWord ++ tailWord_1547601).sum := by decide
  have hdescent : baseEnd_1547601 < baseStart_1547601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547618 : List Nat := [3, 3, 2, 1, 1, 1, 3, 1, 6]
def baseStart_1547618 : Nat := 118140960795 + 1547618 * 2 ^ 59
def prefixEnd_1547618 : Nat := 4983230072969 + 3 ^ 40 * 1547618 * 2
def baseEnd_1547618 : Nat := 353187512688902742736729

theorem tailTrace_1547618 : CollatzResearch.WordTrace tailWord_1547618 prefixEnd_1547618 353187512688902742736729 := by
  unfold tailWord_1547618
  simp only [CollatzResearch.WordTrace]
  refine ⟨14111566426812943239136877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37630843804834515304365005 14111566426812943239136877)
  ·
    refine ⟨5291837410054853714676329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14111566426812943239136877 5291837410054853714676329)
    ·
      refine ⟨3968878057541140286007247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5291837410054853714676329 3968878057541140286007247)
      ·
        refine ⟨5953317086311710429010871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3968878057541140286007247 5953317086311710429010871)
        ·
          refine ⟨8929975629467565643516307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5953317086311710429010871 8929975629467565643516307)
          ·
            refine ⟨13394963444201348465274461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8929975629467565643516307 13394963444201348465274461)
            ·
              refine ⟨5023111291575505674477923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13394963444201348465274461 5023111291575505674477923)
              ·
                refine ⟨7534666937363258511716885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5023111291575505674477923 7534666937363258511716885)
                ·
                  refine ⟨353187512688902742736729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7534666937363258511716885 353187512688902742736729)
                  ·
                    rfl

theorem cell21_1547618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_1547618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1547618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1547618 prefixEnd_1547618 := by exact prefixLift 1547618
  have htrace : WordTrace (prefixWord ++ tailWord_1547618) baseStart_1547618 baseEnd_1547618 := by
    simpa [prefixWord, tailWord_1547618, baseEnd_1547618] using wordTrace_append hprefix tailTrace_1547618
  have hstable : (prefixWord ++ tailWord_1547618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547618).length < 2 ^ (prefixWord ++ tailWord_1547618).sum := by decide
  have hdescent : baseEnd_1547618 < baseStart_1547618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547649 : List Nat := [1, 2, 4, 3, 2, 1, 1, 7]
def baseStart_1547649 : Nat := 118140960795 + 1547649 * 2 ^ 59
def prefixEnd_1547649 : Nat := 4983230072969 + 3 ^ 40 * 1547649 * 2
def baseEnd_1547649 : Nat := 117731529103751192573333

theorem tailTrace_1547649 : CollatzResearch.WordTrace tailWord_1547649 prefixEnd_1547649 117731529103751192573333 := by
  unfold tailWord_1547649
  simp only [CollatzResearch.WordTrace]
  refine ⟨56447396370139465250926001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37631597580092976833950667 56447396370139465250926001)
  ·
    refine ⟨42335547277604598938194501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56447396370139465250926001 42335547277604598938194501)
    ·
      refine ⟨7937915114550862300911469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42335547277604598938194501 7937915114550862300911469)
      ·
        refine ⟨2976718167956573362841801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7937915114550862300911469 2976718167956573362841801)
        ·
          refine ⟨2232538625967430022131351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2976718167956573362841801 2232538625967430022131351)
          ·
            refine ⟨3348807938951145033197027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2232538625967430022131351 3348807938951145033197027)
            ·
              refine ⟨5023211908426717549795541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3348807938951145033197027 5023211908426717549795541)
              ·
                refine ⟨117731529103751192573333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5023211908426717549795541 117731529103751192573333)
                ·
                  rfl

theorem cell21_1547649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 7].length) (baseStart_1547649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1547649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1547649 prefixEnd_1547649 := by exact prefixLift 1547649
  have htrace : WordTrace (prefixWord ++ tailWord_1547649) baseStart_1547649 baseEnd_1547649 := by
    simpa [prefixWord, tailWord_1547649, baseEnd_1547649] using wordTrace_append hprefix tailTrace_1547649
  have hstable : (prefixWord ++ tailWord_1547649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547649).length < 2 ^ (prefixWord ++ tailWord_1547649).sum := by decide
  have hdescent : baseEnd_1547649 < baseStart_1547649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547666 : List Nat := [3, 2, 3, 3, 1, 2, 7]
def baseStart_1547666 : Nat := 118140960795 + 1547666 * 2 ^ 59
def prefixEnd_1547666 : Nat := 4983230072969 + 3 ^ 40 * 1547666 * 2
def baseEnd_1547666 : Nat := 39244274104762813992959

theorem tailTrace_1547666 : CollatzResearch.WordTrace tailWord_1547666 prefixEnd_1547666 39244274104762813992959 := by
  unfold tailWord_1547666
  simp only [CollatzResearch.WordTrace]
  refine ⟨14112004102769469288573713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37632010940718584769529901 14112004102769469288573713)
  ·
    refine ⟨10584003077077101966430285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14112004102769469288573713 10584003077077101966430285)
    ·
      refine ⟨3969001153903913237411357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10584003077077101966430285 3969001153903913237411357)
      ·
        refine ⟨1488375432713967464029259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3969001153903913237411357 1488375432713967464029259)
        ·
          refine ⟨2232563149070951196043889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1488375432713967464029259 2232563149070951196043889)
          ·
            refine ⟨1674422361803213397032917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2232563149070951196043889 1674422361803213397032917)
            ·
              refine ⟨39244274104762813992959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1674422361803213397032917 39244274104762813992959)
              ·
                rfl

theorem cell21_1547666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 7].length) (baseStart_1547666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1547666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1547666 prefixEnd_1547666 := by exact prefixLift 1547666
  have htrace : WordTrace (prefixWord ++ tailWord_1547666) baseStart_1547666 baseEnd_1547666 := by
    simpa [prefixWord, tailWord_1547666, baseEnd_1547666] using wordTrace_append hprefix tailTrace_1547666
  have hstable : (prefixWord ++ tailWord_1547666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547666).length < 2 ^ (prefixWord ++ tailWord_1547666).sum := by decide
  have hdescent : baseEnd_1547666 < baseStart_1547666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547787 : List Nat := [1, 1, 1, 1, 8, 2, 1, 2, 4]
def baseStart_1547787 : Nat := 118140960795 + 1547787 * 2 ^ 59
def prefixEnd_1547787 : Nat := 4983230072969 + 3 ^ 40 * 1547787 * 2
def baseEnd_1547787 : Nat := 353226080791396004419717

theorem tailTrace_1547787 : CollatzResearch.WordTrace tailWord_1547787 prefixEnd_1547787 353226080791396004419717 := by
  unfold tailWord_1547787
  simp only [CollatzResearch.WordTrace]
  refine ⟨56452429643639514819449615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37634953095759676546299743 56452429643639514819449615)
  ·
    refine ⟨84678644465459272229174423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56452429643639514819449615 84678644465459272229174423)
    ·
      refine ⟨127017966698188908343761635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84678644465459272229174423 127017966698188908343761635)
      ·
        refine ⟨190526950047283362515642453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127017966698188908343761635 190526950047283362515642453)
        ·
          refine ⟨2232737695866601904480185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 190526950047283362515642453 2232737695866601904480185)
          ·
            refine ⟨1674553271899951428360139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2232737695866601904480185 1674553271899951428360139)
            ·
              refine ⟨2511829907849927142540209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1674553271899951428360139 2511829907849927142540209)
              ·
                refine ⟨1883872430887445356905157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2511829907849927142540209 1883872430887445356905157)
                ·
                  refine ⟨353226080791396004419717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1883872430887445356905157 353226080791396004419717)
                  ·
                    rfl

theorem cell21_1547787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 2, 4].length) (baseStart_1547787 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1547787 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1547787 prefixEnd_1547787 := by exact prefixLift 1547787
  have htrace : WordTrace (prefixWord ++ tailWord_1547787) baseStart_1547787 baseEnd_1547787 := by
    simpa [prefixWord, tailWord_1547787, baseEnd_1547787] using wordTrace_append hprefix tailTrace_1547787
  have hstable : (prefixWord ++ tailWord_1547787).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547787).length < 2 ^ (prefixWord ++ tailWord_1547787).sum := by decide
  have hdescent : baseEnd_1547787 < baseStart_1547787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547829 : List Nat := [1, 3, 3, 1, 1, 3, 1, 2, 6]
def baseStart_1547829 : Nat := 118140960795 + 1547829 * 2 ^ 59
def prefixEnd_1547829 : Nat := 4983230072969 + 3 ^ 40 * 1547829 * 2
def baseEnd_1547829 : Nat := 353235665763613264719631

theorem tailTrace_1547829 : CollatzResearch.WordTrace tailWord_1547829 prefixEnd_1547829 353235665763613264719631 := by
  unfold tailWord_1547829
  simp only [CollatzResearch.WordTrace]
  refine ⟨56453961509487355992478541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37635974339658237328319027 56453961509487355992478541)
  ·
    refine ⟨21170235566057758497179453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56453961509487355992478541 21170235566057758497179453)
    ·
      refine ⟨7938838337271659436442295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21170235566057758497179453 7938838337271659436442295)
      ·
        refine ⟨11908257505907489154663443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7938838337271659436442295 11908257505907489154663443)
        ·
          refine ⟨17862386258861233731995165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11908257505907489154663443 17862386258861233731995165)
          ·
            refine ⟨6698394847072962649498187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17862386258861233731995165 6698394847072962649498187)
            ·
              refine ⟨10047592270609443974247281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6698394847072962649498187 10047592270609443974247281)
              ·
                refine ⟨7535694202957082980685461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10047592270609443974247281 7535694202957082980685461)
                ·
                  refine ⟨353235665763613264719631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7535694202957082980685461 353235665763613264719631)
                  ·
                    rfl

theorem cell21_1547829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_1547829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1547829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1547829 prefixEnd_1547829 := by exact prefixLift 1547829
  have htrace : WordTrace (prefixWord ++ tailWord_1547829) baseStart_1547829 baseEnd_1547829 := by
    simpa [prefixWord, tailWord_1547829, baseEnd_1547829] using wordTrace_append hprefix tailTrace_1547829
  have hstable : (prefixWord ++ tailWord_1547829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547829).length < 2 ^ (prefixWord ++ tailWord_1547829).sum := by decide
  have hdescent : baseEnd_1547829 < baseStart_1547829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547832 : List Nat := [2, 1, 2, 1, 4, 2, 3, 3, 3]
def baseStart_1547832 : Nat := 118140960795 + 1547832 * 2 ^ 59
def prefixEnd_1547832 : Nat := 4983230072969 + 3 ^ 40 * 1547832 * 2
def baseEnd_1547832 : Nat := 353236350404485926169625

theorem tailTrace_1547832 : CollatzResearch.WordTrace tailWord_1547832 prefixEnd_1547832 353236350404485926169625 := by
  unfold tailWord_1547832
  simp only [CollatzResearch.WordTrace]
  refine ⟨28227035464238243752418875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37636047285650991669891833 28227035464238243752418875)
  ·
    refine ⟨42340553196357365628628313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28227035464238243752418875 42340553196357365628628313)
    ·
      refine ⟨31755414897268024221471235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42340553196357365628628313 31755414897268024221471235)
      ·
        refine ⟨47633122345902036332206853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31755414897268024221471235 47633122345902036332206853)
        ·
          refine ⟨8931210439856631812288785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47633122345902036332206853 8931210439856631812288785)
          ·
            refine ⟨6698407829892473859216589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8931210439856631812288785 6698407829892473859216589)
            ·
              refine ⟨2511902936209677697206221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6698407829892473859216589 2511902936209677697206221)
              ·
                refine ⟨941963601078629136452333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2511902936209677697206221 941963601078629136452333)
                ·
                  refine ⟨353236350404485926169625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 941963601078629136452333 353236350404485926169625)
                  ·
                    rfl

theorem cell21_1547832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 3, 3].length) (baseStart_1547832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1547832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1547832 prefixEnd_1547832 := by exact prefixLift 1547832
  have htrace : WordTrace (prefixWord ++ tailWord_1547832) baseStart_1547832 baseEnd_1547832 := by
    simpa [prefixWord, tailWord_1547832, baseEnd_1547832] using wordTrace_append hprefix tailTrace_1547832
  have hstable : (prefixWord ++ tailWord_1547832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547832).length < 2 ^ (prefixWord ++ tailWord_1547832).sum := by decide
  have hdescent : baseEnd_1547832 < baseStart_1547832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547860 : List Nat := [2, 4, 1, 1, 1, 2, 4, 6]
def baseStart_1547860 : Nat := 118140960795 + 1547860 * 2 ^ 59
def prefixEnd_1547860 : Nat := 4983230072969 + 3 ^ 40 * 1547860 * 2
def baseEnd_1547860 : Nat := 117747580128654699900967

theorem tailTrace_1547860 : CollatzResearch.WordTrace tailWord_1547860 prefixEnd_1547860 117747580128654699900967 := by
  unfold tailWord_1547860
  simp only [CollatzResearch.WordTrace]
  refine ⟨28227546086187524143428517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37636728114916698857904689 28227546086187524143428517)
  ·
    refine ⟨5292664891160160776892847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28227546086187524143428517 5292664891160160776892847)
    ·
      refine ⟨7938997336740241165339271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5292664891160160776892847 7938997336740241165339271)
      ·
        refine ⟨11908496005110361748008907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7938997336740241165339271 11908496005110361748008907)
        ·
          refine ⟨17862744007665542622013361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11908496005110361748008907 17862744007665542622013361)
          ·
            refine ⟨13397058005749156966510021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17862744007665542622013361 13397058005749156966510021)
            ·
              refine ⟨2511948376077966931220629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13397058005749156966510021 2511948376077966931220629)
              ·
                refine ⟨117747580128654699900967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2511948376077966931220629 117747580128654699900967)
                ·
                  rfl

theorem cell21_1547860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 6].length) (baseStart_1547860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1547860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1547860 prefixEnd_1547860 := by exact prefixLift 1547860
  have htrace : WordTrace (prefixWord ++ tailWord_1547860) baseStart_1547860 baseEnd_1547860 := by
    simpa [prefixWord, tailWord_1547860, baseEnd_1547860] using wordTrace_append hprefix tailTrace_1547860
  have hstable : (prefixWord ++ tailWord_1547860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547860).length < 2 ^ (prefixWord ++ tailWord_1547860).sum := by decide
  have hdescent : baseEnd_1547860 < baseStart_1547860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547863 : List Nat := [1, 1, 3, 2, 2, 5, 2, 1, 4]
def baseStart_1547863 : Nat := 118140960795 + 1547863 * 2 ^ 59
def prefixEnd_1547863 : Nat := 4983230072969 + 3 ^ 40 * 1547863 * 2
def baseEnd_1547863 : Nat := 353243425026836761152895

theorem tailTrace_1547863 : CollatzResearch.WordTrace tailWord_1547863 prefixEnd_1547863 353243425026836761152895 := by
  unfold tailWord_1547863
  simp only [CollatzResearch.WordTrace]
  refine ⟨56455201591364179799216243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37636801060909453199477495 56455201591364179799216243)
  ·
    refine ⟨84682802387046269698824365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56455201591364179799216243 84682802387046269698824365)
    ·
      refine ⟨31756050895142351137059137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84682802387046269698824365 31756050895142351137059137)
      ·
        refine ⟨23817038171356763352794353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31756050895142351137059137 23817038171356763352794353)
        ·
          refine ⟨17862778628517572514595765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23817038171356763352794353 17862778628517572514595765)
          ·
            refine ⟨1674635496423522423243353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17862778628517572514595765 1674635496423522423243353)
            ·
              refine ⟨1255976622317641817432515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1674635496423522423243353 1255976622317641817432515)
              ·
                refine ⟨1883964933476462726148773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1255976622317641817432515 1883964933476462726148773)
                ·
                  refine ⟨353243425026836761152895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1883964933476462726148773 353243425026836761152895)
                  ·
                    rfl

theorem cell21_1547863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 1, 4].length) (baseStart_1547863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1547863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1547863 prefixEnd_1547863 := by exact prefixLift 1547863
  have htrace : WordTrace (prefixWord ++ tailWord_1547863) baseStart_1547863 baseEnd_1547863 := by
    simpa [prefixWord, tailWord_1547863, baseEnd_1547863] using wordTrace_append hprefix tailTrace_1547863
  have hstable : (prefixWord ++ tailWord_1547863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547863).length < 2 ^ (prefixWord ++ tailWord_1547863).sum := by decide
  have hdescent : baseEnd_1547863 < baseStart_1547863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547967 : List Nat := [1, 1, 2, 2, 2, 3, 1, 6, 3]
def baseStart_1547967 : Nat := 118140960795 + 1547967 * 2 ^ 59
def prefixEnd_1547967 : Nat := 4983230072969 + 3 ^ 40 * 1547967 * 2
def baseEnd_1547967 : Nat := 353267159243755691419349

theorem tailTrace_1547967 : CollatzResearch.WordTrace tailWord_1547967 prefixEnd_1547967 353267159243755691419349 := by
  unfold tailWord_1547967
  simp only [CollatzResearch.WordTrace]
  refine ⟨56458994782987405561002155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37639329855324937040668103 56458994782987405561002155)
  ·
    refine ⟨84688492174481108341503233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56458994782987405561002155 84688492174481108341503233)
    ·
      refine ⟨63516369130860831256127425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84688492174481108341503233 63516369130860831256127425)
      ·
        refine ⟨47637276848145623442095569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63516369130860831256127425 47637276848145623442095569)
        ·
          refine ⟨35727957636109217581571677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47637276848145623442095569 35727957636109217581571677)
          ·
            refine ⟨13397984113540956593089379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35727957636109217581571677 13397984113540956593089379)
            ·
              refine ⟨20096976170311434889634069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13397984113540956593089379 20096976170311434889634069)
              ·
                refine ⟨942045757983348510451597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20096976170311434889634069 942045757983348510451597)
                ·
                  refine ⟨353267159243755691419349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 942045757983348510451597 353267159243755691419349)
                  ·
                    rfl

theorem cell21_1547967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 6, 3].length) (baseStart_1547967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1547967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1547967 prefixEnd_1547967 := by exact prefixLift 1547967
  have htrace : WordTrace (prefixWord ++ tailWord_1547967) baseStart_1547967 baseEnd_1547967 := by
    simpa [prefixWord, tailWord_1547967, baseEnd_1547967] using wordTrace_append hprefix tailTrace_1547967
  have hstable : (prefixWord ++ tailWord_1547967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547967).length < 2 ^ (prefixWord ++ tailWord_1547967).sum := by decide
  have hdescent : baseEnd_1547967 < baseStart_1547967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548001 : List Nat := [1, 2, 3, 1, 5, 2, 1, 3, 3]
def baseStart_1548001 : Nat := 118140960795 + 1548001 * 2 ^ 59
def prefixEnd_1548001 : Nat := 4983230072969 + 3 ^ 40 * 1548001 * 2
def baseEnd_1548001 : Nat := 353274918506979187852613

theorem tailTrace_1548001 : CollatzResearch.WordTrace tailWord_1548001 prefixEnd_1548001 353274918506979187852613 := by
  unfold tailWord_1548001
  simp only [CollatzResearch.WordTrace]
  refine ⟨56460234864864229367739857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37640156576576152911826571 56460234864864229367739857)
  ·
    refine ⟨42345176148648172025804893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56460234864864229367739857 42345176148648172025804893)
    ·
      refine ⟨15879441055743064509676835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42345176148648172025804893 15879441055743064509676835)
      ·
        refine ⟨23819161583614596764515253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15879441055743064509676835 23819161583614596764515253)
        ·
          refine ⟨2233046398463868446673305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23819161583614596764515253 2233046398463868446673305)
          ·
            refine ⟨1674784798847901335004979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2233046398463868446673305 1674784798847901335004979)
            ·
              refine ⟨2512177198271852002507469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1674784798847901335004979 2512177198271852002507469)
              ·
                refine ⟨942066449351944500940301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2512177198271852002507469 942066449351944500940301)
                ·
                  refine ⟨353274918506979187852613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 942066449351944500940301 353274918506979187852613)
                  ·
                    rfl

theorem cell21_1548001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 3, 3].length) (baseStart_1548001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1548001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1548001 prefixEnd_1548001 := by exact prefixLift 1548001
  have htrace : WordTrace (prefixWord ++ tailWord_1548001) baseStart_1548001 baseEnd_1548001 := by
    simpa [prefixWord, tailWord_1548001, baseEnd_1548001] using wordTrace_append hprefix tailTrace_1548001
  have hstable : (prefixWord ++ tailWord_1548001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548001).length < 2 ^ (prefixWord ++ tailWord_1548001).sum := by decide
  have hdescent : baseEnd_1548001 < baseStart_1548001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548088 : List Nat := [2, 1, 2, 1, 3, 5, 1, 6]
def baseStart_1548088 : Nat := 118140960795 + 1548088 * 2 ^ 59
def prefixEnd_1548088 : Nat := 4983230072969 + 3 ^ 40 * 1548088 * 2
def baseEnd_1548088 : Nat := 117764924364095456634145

theorem tailTrace_1548088 : CollatzResearch.WordTrace tailWord_1548088 prefixEnd_1548088 117764924364095456634145 := by
  unfold tailWord_1548088
  simp only [CollatzResearch.WordTrace]
  refine ⟨28231704007774521613078459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37642272010366028817437945 28231704007774521613078459)
  ·
    refine ⟨42347556011661782419617689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28231704007774521613078459 42347556011661782419617689)
    ·
      refine ⟨31760667008746336814713267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42347556011661782419617689 31760667008746336814713267)
      ·
        refine ⟨47641000513119505222069901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31760667008746336814713267 47641000513119505222069901)
        ·
          refine ⟨17865375192419814458276213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47641000513119505222069901 17865375192419814458276213)
          ·
            refine ⟨1674878924289357605463395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17865375192419814458276213 1674878924289357605463395)
            ·
              refine ⟨2512318386434036408195093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1674878924289357605463395 2512318386434036408195093)
              ·
                refine ⟨117764924364095456634145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2512318386434036408195093 117764924364095456634145)
                ·
                  rfl

theorem cell21_1548088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 6].length) (baseStart_1548088 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1548088 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1548088 prefixEnd_1548088 := by exact prefixLift 1548088
  have htrace : WordTrace (prefixWord ++ tailWord_1548088) baseStart_1548088 baseEnd_1548088 := by
    simpa [prefixWord, tailWord_1548088, baseEnd_1548088] using wordTrace_append hprefix tailTrace_1548088
  have hstable : (prefixWord ++ tailWord_1548088).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548088).length < 2 ^ (prefixWord ++ tailWord_1548088).sum := by decide
  have hdescent : baseEnd_1548088 < baseStart_1548088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548164 : List Nat := [2, 3, 2, 1, 1, 1, 6, 5]
def baseStart_1548164 : Nat := 118140960795 + 1548164 * 2 ^ 59
def prefixEnd_1548164 : Nat := 4983230072969 + 3 ^ 40 * 1548164 * 2
def baseEnd_1548164 : Nat := 117770705775909042211871

theorem tailTrace_1548164 : CollatzResearch.WordTrace tailWord_1548164 prefixEnd_1548164 117770705775909042211871 := by
  unfold tailWord_1548164
  simp only [CollatzResearch.WordTrace]
  refine ⟨28233089981636854102961773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37644119975515805470615697 28233089981636854102961773)
  ·
    refine ⟨10587408743113820288610665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28233089981636854102961773 10587408743113820288610665)
    ·
      refine ⟨7940556557335365216457999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10587408743113820288610665 7940556557335365216457999)
      ·
        refine ⟨11910834836003047824686999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7940556557335365216457999 11910834836003047824686999)
        ·
          refine ⟨17866252254004571737030499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11910834836003047824686999 17866252254004571737030499)
          ·
            refine ⟨26799378381006857605545749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17866252254004571737030499 26799378381006857605545749)
            ·
              refine ⟨1256220861609696450259957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26799378381006857605545749 1256220861609696450259957)
              ·
                refine ⟨117770705775909042211871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1256220861609696450259957 117770705775909042211871)
                ·
                  rfl

theorem cell21_1548164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 5].length) (baseStart_1548164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1548164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1548164 prefixEnd_1548164 := by exact prefixLift 1548164
  have htrace : WordTrace (prefixWord ++ tailWord_1548164) baseStart_1548164 baseEnd_1548164 := by
    simpa [prefixWord, tailWord_1548164, baseEnd_1548164] using wordTrace_append hprefix tailTrace_1548164
  have hstable : (prefixWord ++ tailWord_1548164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548164).length < 2 ^ (prefixWord ++ tailWord_1548164).sum := by decide
  have hdescent : baseEnd_1548164 < baseStart_1548164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548170 : List Nat := [3, 1, 2, 4, 3, 1, 1, 3, 3]
def baseStart_1548170 : Nat := 118140960795 + 1548170 * 2 ^ 59
def prefixEnd_1548170 : Nat := 4983230072969 + 3 ^ 40 * 1548170 * 2
def baseEnd_1548170 : Nat := 353313486609472449535601

theorem tailTrace_1548170 : CollatzResearch.WordTrace tailWord_1548170 prefixEnd_1548170 353313486609472449535601 := by
  unfold tailWord_1548170
  simp only [CollatzResearch.WordTrace]
  refine ⟨14116599700312992807660491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37644265867501314153761309 14116599700312992807660491)
  ·
    refine ⟨21174899550469489211490737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14116599700312992807660491 21174899550469489211490737)
    ·
      refine ⟨15881174662852116908618053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21174899550469489211490737 15881174662852116908618053)
      ·
        refine ⟨2977720249284771920365885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15881174662852116908618053 2977720249284771920365885)
        ·
          refine ⟨1116645093481789470137207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2977720249284771920365885 1116645093481789470137207)
          ·
            refine ⟨1674967640222684205205811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1116645093481789470137207 1674967640222684205205811)
            ·
              refine ⟨2512451460334026307808717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1674967640222684205205811 2512451460334026307808717)
              ·
                refine ⟨942169297625259865428269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2512451460334026307808717 942169297625259865428269)
                ·
                  refine ⟨353313486609472449535601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 942169297625259865428269 353313486609472449535601)
                  ·
                    rfl

theorem cell21_1548170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 3, 3].length) (baseStart_1548170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1548170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1548170 prefixEnd_1548170 := by exact prefixLift 1548170
  have htrace : WordTrace (prefixWord ++ tailWord_1548170) baseStart_1548170 baseEnd_1548170 := by
    simpa [prefixWord, tailWord_1548170, baseEnd_1548170] using wordTrace_append hprefix tailTrace_1548170
  have hstable : (prefixWord ++ tailWord_1548170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548170).length < 2 ^ (prefixWord ++ tailWord_1548170).sum := by decide
  have hdescent : baseEnd_1548170 < baseStart_1548170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548294 : List Nat := [6, 2, 1, 2, 1, 2, 1, 2, 4]
def baseStart_1548294 : Nat := 118140960795 + 1548294 * 2 ^ 59
def prefixEnd_1548294 : Nat := 4983230072969 + 3 ^ 40 * 1548294 * 2
def baseEnd_1548294 : Nat := 353341785098875789468681

theorem tailTrace_1548294 : CollatzResearch.WordTrace tailWord_1548294 prefixEnd_1548294 353341785098875789468681 := by
  unfold tailWord_1548294
  simp only [CollatzResearch.WordTrace]
  refine ⟨1764716295400085637754873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37647280968535160272103957 1764716295400085637754873)
  ·
    refine ⟨1323537221550064228316155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1764716295400085637754873 1323537221550064228316155)
    ·
      refine ⟨1985305832325096342474233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1323537221550064228316155 1985305832325096342474233)
      ·
        refine ⟨1488979374243822256855675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1985305832325096342474233 1488979374243822256855675)
        ·
          refine ⟨2233469061365733385283513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1488979374243822256855675 2233469061365733385283513)
          ·
            refine ⟨1675101796024300038962635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2233469061365733385283513 1675101796024300038962635)
            ·
              refine ⟨2512652694036450058443953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1675101796024300038962635 2512652694036450058443953)
              ·
                refine ⟨1884489520527337543832965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2512652694036450058443953 1884489520527337543832965)
                ·
                  refine ⟨353341785098875789468681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1884489520527337543832965 353341785098875789468681)
                  ·
                    rfl

theorem cell21_1548294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_1548294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1548294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1548294 prefixEnd_1548294 := by exact prefixLift 1548294
  have htrace : WordTrace (prefixWord ++ tailWord_1548294) baseStart_1548294 baseEnd_1548294 := by
    simpa [prefixWord, tailWord_1548294, baseEnd_1548294] using wordTrace_append hprefix tailTrace_1548294
  have hstable : (prefixWord ++ tailWord_1548294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548294).length < 2 ^ (prefixWord ++ tailWord_1548294).sum := by decide
  have hdescent : baseEnd_1548294 < baseStart_1548294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548502 : List Nat := [5, 2, 1, 2, 1, 3, 2, 5]
def baseStart_1548502 : Nat := 118140960795 + 1548502 * 2 ^ 59
def prefixEnd_1548502 : Nat := 4983230072969 + 3 ^ 40 * 1548502 * 2
def baseEnd_1548502 : Nat := 117796417844237883333863

theorem tailTrace_1548502 : CollatzResearch.WordTrace tailWord_1548502 prefixEnd_1548502 117796417844237883333863 := by
  unfold tailWord_1548502
  simp only [CollatzResearch.WordTrace]
  refine ⟨3529906739753074495732985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37652338557366127954485173 3529906739753074495732985)
  ·
    refine ⟨2647430054814805871799739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3529906739753074495732985 2647430054814805871799739)
    ·
      refine ⟨3971145082222208807699609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2647430054814805871799739 3971145082222208807699609)
      ·
        refine ⟨2978358811666656605774707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3971145082222208807699609 2978358811666656605774707)
        ·
          refine ⟨4467538217499984908662061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2978358811666656605774707 4467538217499984908662061)
          ·
            refine ⟨1675326831562494340748273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4467538217499984908662061 1675326831562494340748273)
            ·
              refine ⟨1256495123671870755561205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1675326831562494340748273 1256495123671870755561205)
              ·
                refine ⟨117796417844237883333863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1256495123671870755561205 117796417844237883333863)
                ·
                  rfl

theorem cell21_1548502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_1548502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1548502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1548502 prefixEnd_1548502 := by exact prefixLift 1548502
  have htrace : WordTrace (prefixWord ++ tailWord_1548502) baseStart_1548502 baseEnd_1548502 := by
    simpa [prefixWord, tailWord_1548502, baseEnd_1548502] using wordTrace_append hprefix tailTrace_1548502
  have hstable : (prefixWord ++ tailWord_1548502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548502).length < 2 ^ (prefixWord ++ tailWord_1548502).sum := by decide
  have hdescent : baseEnd_1548502 < baseStart_1548502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548527 : List Nat := [1, 1, 2, 1, 6, 3, 7]
def baseStart_1548527 : Nat := 118140960795 + 1548527 * 2 ^ 59
def prefixEnd_1548527 : Nat := 4983230072969 + 3 ^ 40 * 1548527 * 2
def baseEnd_1548527 : Nat := 39266106541479906898319

theorem tailTrace_1548527 : CollatzResearch.WordTrace tailWord_1548527 prefixEnd_1548527 39266106541479906898319 := by
  unfold tailWord_1548527
  simp only [CollatzResearch.WordTrace]
  refine ⟨56479419660958621201387835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37652946440639080800925223 56479419660958621201387835)
  ·
    refine ⟨84719129491437931802081753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56479419660958621201387835 84719129491437931802081753)
    ·
      refine ⟨63539347118578448851561315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84719129491437931802081753 63539347118578448851561315)
      ·
        refine ⟨95309020677867673277341973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63539347118578448851561315 95309020677867673277341973)
        ·
          refine ⟨4467610344275047184875405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 95309020677867673277341973 4467610344275047184875405)
          ·
            refine ⟨1675353879103142694328277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4467610344275047184875405 1675353879103142694328277)
            ·
              refine ⟨39266106541479906898319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1675353879103142694328277 39266106541479906898319)
              ·
                rfl

theorem cell21_1548527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 7].length) (baseStart_1548527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1548527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1548527 prefixEnd_1548527 := by exact prefixLift 1548527
  have htrace : WordTrace (prefixWord ++ tailWord_1548527) baseStart_1548527 baseEnd_1548527 := by
    simpa [prefixWord, tailWord_1548527, baseEnd_1548527] using wordTrace_append hprefix tailTrace_1548527
  have hstable : (prefixWord ++ tailWord_1548527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548527).length < 2 ^ (prefixWord ++ tailWord_1548527).sum := by decide
  have hdescent : baseEnd_1548527 < baseStart_1548527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548758 : List Nat := [5, 2, 1, 1, 1, 1, 4, 2, 4]
def baseStart_1548758 : Nat := 118140960795 + 1548758 * 2 ^ 59
def prefixEnd_1548758 : Nat := 4983230072969 + 3 ^ 40 * 1548758 * 2
def baseEnd_1548758 : Nat := 353447676220514093734399

theorem tailTrace_1548758 : CollatzResearch.WordTrace tailWord_1548758 prefixEnd_1548758 353447676220514093734399 := by
  unfold tailWord_1548758
  simp only [CollatzResearch.WordTrace]
  refine ⟨3530490307695109228315433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37658563282081165102031285 3530490307695109228315433)
  ·
    refine ⟨2647867730771331921236575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3530490307695109228315433 2647867730771331921236575)
    ·
      refine ⟨3971801596156997881854863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2647867730771331921236575 3971801596156997881854863)
      ·
        refine ⟨5957702394235496822782295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3971801596156997881854863 5957702394235496822782295)
        ·
          refine ⟨8936553591353245234173443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5957702394235496822782295 8936553591353245234173443)
          ·
            refine ⟨13404830387029867851260165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8936553591353245234173443 13404830387029867851260165)
            ·
              refine ⟨2513405697568100222111281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13404830387029867851260165 2513405697568100222111281)
              ·
                refine ⟨1885054273176075166583461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2513405697568100222111281 1885054273176075166583461)
                ·
                  refine ⟨353447676220514093734399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1885054273176075166583461 353447676220514093734399)
                  ·
                    rfl

theorem cell21_1548758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_1548758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1548758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1548758 prefixEnd_1548758 := by exact prefixLift 1548758
  have htrace : WordTrace (prefixWord ++ tailWord_1548758) baseStart_1548758 baseEnd_1548758 := by
    simpa [prefixWord, tailWord_1548758, baseEnd_1548758] using wordTrace_append hprefix tailTrace_1548758
  have hstable : (prefixWord ++ tailWord_1548758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548758).length < 2 ^ (prefixWord ++ tailWord_1548758).sum := by decide
  have hdescent : baseEnd_1548758 < baseStart_1548758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548769 : List Nat := [1, 2, 3, 1, 2, 2, 2, 3, 5]
def baseStart_1548769 : Nat := 118140960795 + 1548769 * 2 ^ 59
def prefixEnd_1548769 : Nat := 4983230072969 + 3 ^ 40 * 1548769 * 2
def baseEnd_1548769 : Nat := 353450186570380519051043

theorem tailTrace_1548769 : CollatzResearch.WordTrace tailWord_1548769 prefixEnd_1548769 353450186570380519051043 := by
  unfold tailWord_1548769
  simp only [CollatzResearch.WordTrace]
  refine ⟨56488246126081896531697361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37658830750721264354464907 56488246126081896531697361)
  ·
    refine ⟨42366184594561422398773021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56488246126081896531697361 42366184594561422398773021)
    ·
      refine ⟨15887319222960533399539883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42366184594561422398773021 15887319222960533399539883)
      ·
        refine ⟨23830978834440800099309825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15887319222960533399539883 23830978834440800099309825)
        ·
          refine ⟨17873234125830600074482369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23830978834440800099309825 17873234125830600074482369)
          ·
            refine ⟨13404925594372950055861777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17873234125830600074482369 13404925594372950055861777)
            ·
              refine ⟨10053694195779712541896333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13404925594372950055861777 10053694195779712541896333)
              ·
                refine ⟨3770135323417392203211125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10053694195779712541896333 3770135323417392203211125)
                ·
                  refine ⟨353450186570380519051043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3770135323417392203211125 353450186570380519051043)
                  ·
                    rfl

theorem cell21_1548769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 5].length) (baseStart_1548769 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1548769 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1548769 prefixEnd_1548769 := by exact prefixLift 1548769
  have htrace : WordTrace (prefixWord ++ tailWord_1548769) baseStart_1548769 baseEnd_1548769 := by
    simpa [prefixWord, tailWord_1548769, baseEnd_1548769] using wordTrace_append hprefix tailTrace_1548769
  have hstable : (prefixWord ++ tailWord_1548769).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548769).length < 2 ^ (prefixWord ++ tailWord_1548769).sum := by decide
  have hdescent : baseEnd_1548769 < baseStart_1548769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548783 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 8]
def baseStart_1548783 : Nat := 118140960795 + 1548783 * 2 ^ 59
def prefixEnd_1548783 : Nat := 4983230072969 + 3 ^ 40 * 1548783 * 2
def baseEnd_1548783 : Nat := 353453381561119605817681

theorem tailTrace_1548783 : CollatzResearch.WordTrace tailWord_1548783 prefixEnd_1548783 353453381561119605817681 := by
  unfold tailWord_1548783
  simp only [CollatzResearch.WordTrace]
  refine ⟨56488756748031176922707003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37659171165354117948471335 56488756748031176922707003)
  ·
    refine ⟨84733135122046765384060505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56488756748031176922707003 84733135122046765384060505)
    ·
      refine ⟨63549851341535074038045379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84733135122046765384060505 63549851341535074038045379)
      ·
        refine ⟨95324777012302611057068069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63549851341535074038045379 95324777012302611057068069)
        ·
          refine ⟨17873395689806739573200263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95324777012302611057068069 17873395689806739573200263)
          ·
            refine ⟨26810093534710109359800395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17873395689806739573200263 26810093534710109359800395)
            ·
              refine ⟨40215140302065164039700593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26810093534710109359800395 40215140302065164039700593)
              ·
                refine ⟨30161355226548873029775445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40215140302065164039700593 30161355226548873029775445)
                ·
                  refine ⟨353453381561119605817681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30161355226548873029775445 353453381561119605817681)
                  ·
                    rfl

theorem cell21_1548783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 8].length) (baseStart_1548783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1548783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1548783 prefixEnd_1548783 := by exact prefixLift 1548783
  have htrace : WordTrace (prefixWord ++ tailWord_1548783) baseStart_1548783 baseEnd_1548783 := by
    simpa [prefixWord, tailWord_1548783, baseEnd_1548783] using wordTrace_append hprefix tailTrace_1548783
  have hstable : (prefixWord ++ tailWord_1548783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548783).length < 2 ^ (prefixWord ++ tailWord_1548783).sum := by decide
  have hdescent : baseEnd_1548783 < baseStart_1548783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548789 : List Nat := [1, 3, 5, 1, 2, 1, 3, 5]
def baseStart_1548789 : Nat := 118140960795 + 1548789 * 2 ^ 59
def prefixEnd_1548789 : Nat := 4983230072969 + 3 ^ 40 * 1548789 * 2
def baseEnd_1548789 : Nat := 117818250280954976239223

theorem tailTrace_1548789 : CollatzResearch.WordTrace tailWord_1548789 prefixEnd_1548789 117818250280954976239223 := by
  unfold tailWord_1548789
  simp only [CollatzResearch.WordTrace]
  refine ⟨56488975586009439947425421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37659317057339626631616947 56488975586009439947425421)
  ·
    refine ⟨21183365844753539980284533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56488975586009439947425421 21183365844753539980284533)
    ·
      refine ⟨1985940547945644373151675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21183365844753539980284533 1985940547945644373151675)
      ·
        refine ⟨2978910821918466559727513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1985940547945644373151675 2978910821918466559727513)
        ·
          refine ⟨2234183116438849919795635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2978910821918466559727513 2234183116438849919795635)
          ·
            refine ⟨3351274674658274879693453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2234183116438849919795635 3351274674658274879693453)
            ·
              refine ⟨1256728002996853079885045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3351274674658274879693453 1256728002996853079885045)
              ·
                refine ⟨117818250280954976239223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1256728002996853079885045 117818250280954976239223)
                ·
                  rfl

theorem cell21_1548789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 5].length) (baseStart_1548789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1548789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1548789 prefixEnd_1548789 := by exact prefixLift 1548789
  have htrace : WordTrace (prefixWord ++ tailWord_1548789) baseStart_1548789 baseEnd_1548789 := by
    simpa [prefixWord, tailWord_1548789, baseEnd_1548789] using wordTrace_append hprefix tailTrace_1548789
  have hstable : (prefixWord ++ tailWord_1548789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548789).length < 2 ^ (prefixWord ++ tailWord_1548789).sum := by decide
  have hdescent : baseEnd_1548789 < baseStart_1548789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548820 : List Nat := [2, 4, 3, 1, 1, 1, 2, 4, 3]
def baseStart_1548820 : Nat := 118140960795 + 1548820 * 2 ^ 59
def prefixEnd_1548820 : Nat := 4983230072969 + 3 ^ 40 * 1548820 * 2
def baseEnd_1548820 : Nat := 353461825465215763700939

theorem tailTrace_1548820 : CollatzResearch.WordTrace tailWord_1548820 prefixEnd_1548820 353461825465215763700939 := by
  unfold tailWord_1548820
  simp only [CollatzResearch.WordTrace]
  refine ⟨28245053124448566120901957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37660070832598088161202609 28245053124448566120901957)
  ·
    refine ⟨5295947460834106147669117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28245053124448566120901957 5295947460834106147669117)
    ·
      refine ⟨1985980297812789805375919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5295947460834106147669117 1985980297812789805375919)
      ·
        refine ⟨2978970446719184708063879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1985980297812789805375919 2978970446719184708063879)
        ·
          refine ⟨4468455670078777062095819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2978970446719184708063879 4468455670078777062095819)
          ·
            refine ⟨6702683505118165593143729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4468455670078777062095819 6702683505118165593143729)
            ·
              refine ⟨5027012628838624194857797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6702683505118165593143729 5027012628838624194857797)
              ·
                refine ⟨942564867907242036535837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5027012628838624194857797 942564867907242036535837)
                ·
                  refine ⟨353461825465215763700939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 942564867907242036535837 353461825465215763700939)
                  ·
                    rfl

theorem cell21_1548820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_1548820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1548820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1548820 prefixEnd_1548820 := by exact prefixLift 1548820
  have htrace : WordTrace (prefixWord ++ tailWord_1548820) baseStart_1548820 baseEnd_1548820 := by
    simpa [prefixWord, tailWord_1548820, baseEnd_1548820] using wordTrace_append hprefix tailTrace_1548820
  have hstable : (prefixWord ++ tailWord_1548820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548820).length < 2 ^ (prefixWord ++ tailWord_1548820).sum := by decide
  have hdescent : baseEnd_1548820 < baseStart_1548820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548876 : List Nat := [2, 2, 1, 3, 1, 2, 2, 4, 4]
def baseStart_1548876 : Nat := 118140960795 + 1548876 * 2 ^ 59
def prefixEnd_1548876 : Nat := 4983230072969 + 3 ^ 40 * 1548876 * 2
def baseEnd_1548876 : Nat := 353474605428172110767491

theorem tailTrace_1548876 : CollatzResearch.WordTrace tailWord_1548876 prefixEnd_1548876 353474605428172110767491 := by
  unfold tailWord_1548876
  simp only [CollatzResearch.WordTrace]
  refine ⟨28246074368347126902921241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37661432491129502537228321 28246074368347126902921241)
  ·
    refine ⟨21184555776260345177190931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28246074368347126902921241 21184555776260345177190931)
    ·
      refine ⟨31776833664390517765786397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21184555776260345177190931 31776833664390517765786397)
      ·
        refine ⟨11916312624146444162169899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31776833664390517765786397 11916312624146444162169899)
        ·
          refine ⟨17874468936219666243254849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11916312624146444162169899 17874468936219666243254849)
          ·
            refine ⟨13405851702164749682441137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17874468936219666243254849 13405851702164749682441137)
            ·
              refine ⟨10054388776623562261830853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13405851702164749682441137 10054388776623562261830853)
              ·
                refine ⟨1885197895616917924093285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10054388776623562261830853 1885197895616917924093285)
                ·
                  refine ⟨353474605428172110767491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1885197895616917924093285 353474605428172110767491)
                  ·
                    rfl

theorem cell21_1548876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4, 4].length) (baseStart_1548876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1548876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1548876 prefixEnd_1548876 := by exact prefixLift 1548876
  have htrace : WordTrace (prefixWord ++ tailWord_1548876) baseStart_1548876 baseEnd_1548876 := by
    simpa [prefixWord, tailWord_1548876, baseEnd_1548876] using wordTrace_append hprefix tailTrace_1548876
  have hstable : (prefixWord ++ tailWord_1548876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548876).length < 2 ^ (prefixWord ++ tailWord_1548876).sum := by decide
  have hdescent : baseEnd_1548876 < baseStart_1548876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548930 : List Nat := [3, 4, 3, 1, 1, 1, 1, 4, 3]
def baseStart_1548930 : Nat := 118140960795 + 1548930 * 2 ^ 59
def prefixEnd_1548930 : Nat := 4983230072969 + 3 ^ 40 * 1548930 * 2
def baseEnd_1548930 : Nat := 353486928963880016867381

theorem tailTrace_1548930 : CollatzResearch.WordTrace tailWord_1548930 prefixEnd_1548930 353486928963880016867381 := by
  unfold tailWord_1548930
  simp only [CollatzResearch.WordTrace]
  refine ⟨14123529569624655257077061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37662745518999080685538829 14123529569624655257077061)
  ·
    refine ⟨2648161794304622860701949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14123529569624655257077061 2648161794304622860701949)
    ·
      refine ⟨993060672864233572763231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2648161794304622860701949 993060672864233572763231)
      ·
        refine ⟨1489591009296350359144847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 993060672864233572763231 1489591009296350359144847)
        ·
          refine ⟨2234386513944525538717271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1489591009296350359144847 2234386513944525538717271)
          ·
            refine ⟨3351579770916788308075907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2234386513944525538717271 3351579770916788308075907)
            ·
              refine ⟨5027369656375182462113861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3351579770916788308075907 5027369656375182462113861)
              ·
                refine ⟨942631810570346711646349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5027369656375182462113861 942631810570346711646349)
                ·
                  refine ⟨353486928963880016867381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 942631810570346711646349 353486928963880016867381)
                  ·
                    rfl

theorem cell21_1548930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_1548930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1548930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1548930 prefixEnd_1548930 := by exact prefixLift 1548930
  have htrace : WordTrace (prefixWord ++ tailWord_1548930) baseStart_1548930 baseEnd_1548930 := by
    simpa [prefixWord, tailWord_1548930, baseEnd_1548930] using wordTrace_append hprefix tailTrace_1548930
  have hstable : (prefixWord ++ tailWord_1548930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548930).length < 2 ^ (prefixWord ++ tailWord_1548930).sum := by decide
  have hdescent : baseEnd_1548930 < baseStart_1548930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548952 : List Nat := [2, 1, 2, 4, 1, 1, 1, 5, 4]
def baseStart_1548952 : Nat := 118140960795 + 1548952 * 2 ^ 59
def prefixEnd_1548952 : Nat := 4983230072969 + 3 ^ 40 * 1548952 * 2
def baseEnd_1548952 : Nat := 353491949663612867500669

theorem tailTrace_1548952 : CollatzResearch.WordTrace tailWord_1548952 prefixEnd_1548952 353491949663612867500669 := by
  unfold tailWord_1548952
  simp only [CollatzResearch.WordTrace]
  refine ⟨28247460342209459392804555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37663280456279279190406073 28247460342209459392804555)
  ·
    refine ⟨42371190513314189089206833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28247460342209459392804555 42371190513314189089206833)
    ·
      refine ⟨31778392884985641816905125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42371190513314189089206833 31778392884985641816905125)
      ·
        refine ⟨5958448665934807840669711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31778392884985641816905125 5958448665934807840669711)
        ·
          refine ⟨8937672998902211761004567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5958448665934807840669711 8937672998902211761004567)
          ·
            refine ⟨13406509498353317641506851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8937672998902211761004567 13406509498353317641506851)
            ·
              refine ⟨20109764247529976462260277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13406509498353317641506851 20109764247529976462260277)
              ·
                refine ⟨1885290398205935293336901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20109764247529976462260277 1885290398205935293336901)
                ·
                  refine ⟨353491949663612867500669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1885290398205935293336901 353491949663612867500669)
                  ·
                    rfl

theorem cell21_1548952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5, 4].length) (baseStart_1548952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1548952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1548952 prefixEnd_1548952 := by exact prefixLift 1548952
  have htrace : WordTrace (prefixWord ++ tailWord_1548952) baseStart_1548952 baseEnd_1548952 := by
    simpa [prefixWord, tailWord_1548952, baseEnd_1548952] using wordTrace_append hprefix tailTrace_1548952
  have hstable : (prefixWord ++ tailWord_1548952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548952).length < 2 ^ (prefixWord ++ tailWord_1548952).sum := by decide
  have hdescent : baseEnd_1548952 < baseStart_1548952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549042 : List Nat := [3, 2, 1, 3, 1, 2, 9]
def baseStart_1549042 : Nat := 118140960795 + 1549042 * 2 ^ 59
def prefixEnd_1549042 : Nat := 4983230072969 + 3 ^ 40 * 1549042 * 2
def baseEnd_1549042 : Nat := 39279165432199190111165

theorem tailTrace_1549042 : CollatzResearch.WordTrace tailWord_1549042 prefixEnd_1549042 39279165432199190111165 := by
  unfold tailWord_1549042
  simp only [CollatzResearch.WordTrace]
  refine ⟨14124550813523216039096345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37665468836061909437590253 14124550813523216039096345)
  ·
    refine ⟨10593413110142412029322259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14124550813523216039096345 10593413110142412029322259)
    ·
      refine ⟨15890119665213618043983389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10593413110142412029322259 15890119665213618043983389)
      ·
        refine ⟨5958794874455106766493771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15890119665213618043983389 5958794874455106766493771)
        ·
          refine ⟨8938192311682660149740657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5958794874455106766493771 8938192311682660149740657)
          ·
            refine ⟨6703644233761995112305493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8938192311682660149740657 6703644233761995112305493)
            ·
              refine ⟨39279165432199190111165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6703644233761995112305493 39279165432199190111165)
              ·
                rfl

theorem cell21_1549042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 9].length) (baseStart_1549042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1549042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1549042 prefixEnd_1549042 := by exact prefixLift 1549042
  have htrace : WordTrace (prefixWord ++ tailWord_1549042) baseStart_1549042 baseEnd_1549042 := by
    simpa [prefixWord, tailWord_1549042, baseEnd_1549042] using wordTrace_append hprefix tailTrace_1549042
  have hstable : (prefixWord ++ tailWord_1549042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549042).length < 2 ^ (prefixWord ++ tailWord_1549042).sum := by decide
  have hdescent : baseEnd_1549042 < baseStart_1549042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549107 : List Nat := [1, 1, 1, 2, 6, 1, 4, 2, 3]
def baseStart_1549107 : Nat := 118140960795 + 1549107 * 2 ^ 59
def prefixEnd_1549107 : Nat := 4983230072969 + 3 ^ 40 * 1549107 * 2
def baseEnd_1549107 : Nat := 353527322775367042417019

theorem tailTrace_1549107 : CollatzResearch.WordTrace tailWord_1549107 prefixEnd_1549107 353527322775367042417019 := by
  unfold tailWord_1549107
  simp only [CollatzResearch.WordTrace]
  refine ⟨56500573998857380257501575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37667049332571586838334383 56500573998857380257501575)
  ·
    refine ⟨84750860998286070386252363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56500573998857380257501575 84750860998286070386252363)
    ·
      refine ⟨127126291497429105579378545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84750860998286070386252363 127126291497429105579378545)
      ·
        refine ⟨95344718623071829184533909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127126291497429105579378545 95344718623071829184533909)
        ·
          refine ⟨4469283685456491993025027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 95344718623071829184533909 4469283685456491993025027)
          ·
            refine ⟨6703925528184737989537541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4469283685456491993025027 6703925528184737989537541)
            ·
              refine ⟨1256986036534638373038289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6703925528184737989537541 1256986036534638373038289)
              ·
                refine ⟨942739527400978779778717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1256986036534638373038289 942739527400978779778717)
                ·
                  refine ⟨353527322775367042417019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 942739527400978779778717 353527322775367042417019)
                  ·
                    rfl

theorem cell21_1549107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 2, 3].length) (baseStart_1549107 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1549107 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1549107 prefixEnd_1549107 := by exact prefixLift 1549107
  have htrace : WordTrace (prefixWord ++ tailWord_1549107) baseStart_1549107 baseEnd_1549107 := by
    simpa [prefixWord, tailWord_1549107, baseEnd_1549107] using wordTrace_append hprefix tailTrace_1549107
  have hstable : (prefixWord ++ tailWord_1549107).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549107).length < 2 ^ (prefixWord ++ tailWord_1549107).sum := by decide
  have hdescent : baseEnd_1549107 < baseStart_1549107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549186 : List Nat := [3, 4, 2, 2, 1, 2, 2, 5]
def baseStart_1549186 : Nat := 118140960795 + 1549186 * 2 ^ 59
def prefixEnd_1549186 : Nat := 4983230072969 + 3 ^ 40 * 1549186 * 2
def baseEnd_1549186 : Nat := 117848450550560153533397

theorem tailTrace_1549186 : CollatzResearch.WordTrace tailWord_1549186 prefixEnd_1549186 117848450550560153533397 := by
  unfold tailWord_1549186
  simp only [CollatzResearch.WordTrace]
  refine ⟨14125863841392794187406853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37668970243714117833084941 14125863841392794187406853)
  ·
    refine ⟨2648599470261148910138785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14125863841392794187406853 2648599470261148910138785)
    ·
      refine ⟨1986449602695861682604089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2648599470261148910138785 1986449602695861682604089)
      ·
        refine ⟨1489837202021896261953067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1986449602695861682604089 1489837202021896261953067)
        ·
          refine ⟨2234755803032844392929601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1489837202021896261953067 2234755803032844392929601)
          ·
            refine ⟨1676066852274633294697201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2234755803032844392929601 1676066852274633294697201)
            ·
              refine ⟨1257050139205974971022901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1676066852274633294697201 1257050139205974971022901)
              ·
                refine ⟨117848450550560153533397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1257050139205974971022901 117848450550560153533397)
                ·
                  rfl

theorem cell21_1549186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 5].length) (baseStart_1549186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1549186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1549186 prefixEnd_1549186 := by exact prefixLift 1549186
  have htrace : WordTrace (prefixWord ++ tailWord_1549186) baseStart_1549186 baseEnd_1549186 := by
    simpa [prefixWord, tailWord_1549186, baseEnd_1549186] using wordTrace_append hprefix tailTrace_1549186
  have hstable : (prefixWord ++ tailWord_1549186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549186).length < 2 ^ (prefixWord ++ tailWord_1549186).sum := by decide
  have hdescent : baseEnd_1549186 < baseStart_1549186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549287 : List Nat := [1, 1, 5, 2, 2, 3, 1, 6]
def baseStart_1549287 : Nat := 118140960795 + 1549287 * 2 ^ 59
def prefixEnd_1549287 : Nat := 4983230072969 + 3 ^ 40 * 1549287 * 2
def baseEnd_1549287 : Nat := 117856133742575576472217

theorem tailTrace_1549287 : CollatzResearch.WordTrace tailWord_1549287 prefixEnd_1549287 117856133742575576472217 := by
  unfold tailWord_1549287
  simp only [CollatzResearch.WordTrace]
  refine ⟨56507139138205270999054115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37671426092136847332702743 56507139138205270999054115)
  ·
    refine ⟨84760708707307906498581173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56507139138205270999054115 84760708707307906498581173)
    ·
      refine ⟨7946316441310116234241985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84760708707307906498581173 7946316441310116234241985)
      ·
        refine ⟨5959737330982587175681489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7946316441310116234241985 5959737330982587175681489)
        ·
          refine ⟨4469802998236940381761117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5959737330982587175681489 4469802998236940381761117)
          ·
            refine ⟨1676176124338852643160419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4469802998236940381761117 1676176124338852643160419)
            ·
              refine ⟨2514264186508278964740629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1676176124338852643160419 2514264186508278964740629)
              ·
                refine ⟨117856133742575576472217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2514264186508278964740629 117856133742575576472217)
                ·
                  rfl

theorem cell21_1549287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 6].length) (baseStart_1549287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1549287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1549287 prefixEnd_1549287 := by exact prefixLift 1549287
  have htrace : WordTrace (prefixWord ++ tailWord_1549287) baseStart_1549287 baseEnd_1549287 := by
    simpa [prefixWord, tailWord_1549287, baseEnd_1549287] using wordTrace_append hprefix tailTrace_1549287
  have hstable : (prefixWord ++ tailWord_1549287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549287).length < 2 ^ (prefixWord ++ tailWord_1549287).sum := by decide
  have hdescent : baseEnd_1549287 < baseStart_1549287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549360 : List Nat := [2, 1, 1, 1, 2, 4, 1, 4, 5]
def baseStart_1549360 : Nat := 118140960795 + 1549360 * 2 ^ 59
def prefixEnd_1549360 : Nat := 4983230072969 + 3 ^ 40 * 1549360 * 2
def baseEnd_1549360 : Nat := 353585060822294824699835

theorem tailTrace_1549360 : CollatzResearch.WordTrace tailWord_1549360 prefixEnd_1549360 353585060822294824699835 := by
  unfold tailWord_1549360
  simp only [CollatzResearch.WordTrace]
  refine ⟨28254900833470402233230767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37673201111293869644307689 28254900833470402233230767)
  ·
    refine ⟨42382351250205603349846151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28254900833470402233230767 42382351250205603349846151)
    ·
      refine ⟨63573526875308405024769227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42382351250205603349846151 63573526875308405024769227)
      ·
        refine ⟨95360290312962607537153841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63573526875308405024769227 95360290312962607537153841)
        ·
          refine ⟨71520217734721955652865381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95360290312962607537153841 71520217734721955652865381)
          ·
            refine ⟨13410040825260366684912259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71520217734721955652865381 13410040825260366684912259)
            ·
              refine ⟨20115061237890550027368389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13410040825260366684912259 20115061237890550027368389)
              ·
                refine ⟨3771573982104478130131573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20115061237890550027368389 3771573982104478130131573)
                ·
                  refine ⟨353585060822294824699835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3771573982104478130131573 353585060822294824699835)
                  ·
                    rfl

theorem cell21_1549360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 5].length) (baseStart_1549360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1549360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1549360 prefixEnd_1549360 := by exact prefixLift 1549360
  have htrace : WordTrace (prefixWord ++ tailWord_1549360) baseStart_1549360 baseEnd_1549360 := by
    simpa [prefixWord, tailWord_1549360, baseEnd_1549360] using wordTrace_append hprefix tailTrace_1549360
  have hstable : (prefixWord ++ tailWord_1549360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549360).length < 2 ^ (prefixWord ++ tailWord_1549360).sum := by decide
  have hdescent : baseEnd_1549360 < baseStart_1549360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549394 : List Nat := [3, 2, 2, 1, 3, 3, 1, 1, 5]
def baseStart_1549394 : Nat := 118140960795 + 1549394 * 2 ^ 59
def prefixEnd_1549394 : Nat := 4983230072969 + 3 ^ 40 * 1549394 * 2
def baseEnd_1549394 : Nat := 353592820085518321133099

theorem tailTrace_1549394 : CollatzResearch.WordTrace tailWord_1549394 prefixEnd_1549394 353592820085518321133099 := by
  unfold tailWord_1549394
  simp only [CollatzResearch.WordTrace]
  refine ⟨14127760437204407068299809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37674027832545085515466157 14127760437204407068299809)
  ·
    refine ⟨10595820327903305301224857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14127760437204407068299809 10595820327903305301224857)
    ·
      refine ⟨7946865245927478975918643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10595820327903305301224857 7946865245927478975918643)
      ·
        refine ⟨11920297868891218463877965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7946865245927478975918643 11920297868891218463877965)
        ·
          refine ⟨4470111700834206923954237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11920297868891218463877965 4470111700834206923954237)
          ·
            refine ⟨1676291887812827596482839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4470111700834206923954237 1676291887812827596482839)
            ·
              refine ⟨2514437831719241394724259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1676291887812827596482839 2514437831719241394724259)
              ·
                refine ⟨3771656747578862092086389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2514437831719241394724259 3771656747578862092086389)
                ·
                  refine ⟨353592820085518321133099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3771656747578862092086389 353592820085518321133099)
                  ·
                    rfl

theorem cell21_1549394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_1549394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1549394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1549394 prefixEnd_1549394 := by exact prefixLift 1549394
  have htrace : WordTrace (prefixWord ++ tailWord_1549394) baseStart_1549394 baseEnd_1549394 := by
    simpa [prefixWord, tailWord_1549394, baseEnd_1549394] using wordTrace_append hprefix tailTrace_1549394
  have hstable : (prefixWord ++ tailWord_1549394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549394).length < 2 ^ (prefixWord ++ tailWord_1549394).sum := by decide
  have hdescent : baseEnd_1549394 < baseStart_1549394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549422 : List Nat := [4, 1, 2, 2, 1, 2, 2, 7]
def baseStart_1549422 : Nat := 118140960795 + 1549422 * 2 ^ 59
def prefixEnd_1549422 : Nat := 4983230072969 + 3 ^ 40 * 1549422 * 2
def baseEnd_1549422 : Nat := 117866403355665498222125

theorem tailTrace_1549422 : CollatzResearch.WordTrace tailWord_1549422 prefixEnd_1549422 117866403355665498222125 := by
  unfold tailWord_1549422
  simp only [CollatzResearch.WordTrace]
  refine ⟨7064007874089523631902315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37674708661810792703479013 7064007874089523631902315)
  ·
    refine ⟨10596011811134285447853473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7064007874089523631902315 10596011811134285447853473)
    ·
      refine ⟨7947008858350714085890105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10596011811134285447853473 7947008858350714085890105)
      ·
        refine ⟨5960256643763035564417579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7947008858350714085890105 5960256643763035564417579)
        ·
          refine ⟨8940384965644553346626369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5960256643763035564417579 8940384965644553346626369)
          ·
            refine ⟨6705288724233415009969777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8940384965644553346626369 6705288724233415009969777)
            ·
              refine ⟨5028966543175061257477333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6705288724233415009969777 5028966543175061257477333)
              ·
                refine ⟨117866403355665498222125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5028966543175061257477333 117866403355665498222125)
                ·
                  rfl

theorem cell21_1549422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_1549422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1549422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1549422 prefixEnd_1549422 := by exact prefixLift 1549422
  have htrace : WordTrace (prefixWord ++ tailWord_1549422) baseStart_1549422 baseEnd_1549422 := by
    simpa [prefixWord, tailWord_1549422, baseEnd_1549422] using wordTrace_append hprefix tailTrace_1549422
  have hstable : (prefixWord ++ tailWord_1549422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549422).length < 2 ^ (prefixWord ++ tailWord_1549422).sum := by decide
  have hdescent : baseEnd_1549422 < baseStart_1549422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549470 : List Nat := [4, 3, 1, 1, 2, 2, 1, 2, 5]
def baseStart_1549470 : Nat := 118140960795 + 1549470 * 2 ^ 59
def prefixEnd_1549470 : Nat := 4983230072969 + 3 ^ 40 * 1549470 * 2
def baseEnd_1549470 : Nat := 353610164320959077866277

theorem tailTrace_1549470 : CollatzResearch.WordTrace tailWord_1549470 prefixEnd_1549470 353610164320959077866277 := by
  unfold tailWord_1549470
  simp only [CollatzResearch.WordTrace]
  refine ⟨7064226712067786656620733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37675875797694862168643909 7064226712067786656620733)
  ·
    refine ⟨2649085017025419996232775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7064226712067786656620733 2649085017025419996232775)
    ·
      refine ⟨3973627525538129994349163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2649085017025419996232775 3973627525538129994349163)
      ·
        refine ⟨5960441288307194991523745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3973627525538129994349163 5960441288307194991523745)
        ·
          refine ⟨4470330966230396243642809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5960441288307194991523745 4470330966230396243642809)
          ·
            refine ⟨3352748224672797182732107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4470330966230396243642809 3352748224672797182732107)
            ·
              refine ⟨5029122337009195774098161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3352748224672797182732107 5029122337009195774098161)
              ·
                refine ⟨3771841752756896830573621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5029122337009195774098161 3771841752756896830573621)
                ·
                  refine ⟨353610164320959077866277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3771841752756896830573621 353610164320959077866277)
                  ·
                    rfl

theorem cell21_1549470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_1549470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1549470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1549470 prefixEnd_1549470 := by exact prefixLift 1549470
  have htrace : WordTrace (prefixWord ++ tailWord_1549470) baseStart_1549470 baseEnd_1549470 := by
    simpa [prefixWord, tailWord_1549470, baseEnd_1549470] using wordTrace_append hprefix tailTrace_1549470
  have hstable : (prefixWord ++ tailWord_1549470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549470).length < 2 ^ (prefixWord ++ tailWord_1549470).sum := by decide
  have hdescent : baseEnd_1549470 < baseStart_1549470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549512 : List Nat := [2, 1, 3, 1, 2, 1, 3, 3, 5]
def baseStart_1549512 : Nat := 118140960795 + 1549512 * 2 ^ 59
def prefixEnd_1549512 : Nat := 4983230072969 + 3 ^ 40 * 1549512 * 2
def baseEnd_1549512 : Nat := 353619749293176338166191

theorem tailTrace_1549512 : CollatzResearch.WordTrace tailWord_1549512 prefixEnd_1549512 353619749293176338166191 := by
  unfold tailWord_1549512
  simp only [CollatzResearch.WordTrace]
  refine ⟨28257672781195067212997395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37676897041593422950663193 28257672781195067212997395)
  ·
    refine ⟨42386509171792600819496093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28257672781195067212997395 42386509171792600819496093)
    ·
      refine ⟨15894940939422225307311035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42386509171792600819496093 15894940939422225307311035)
      ·
        refine ⟨23842411409133337960966553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15894940939422225307311035 23842411409133337960966553)
        ·
          refine ⟨17881808556850003470724915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23842411409133337960966553 17881808556850003470724915)
          ·
            refine ⟨26822712835275005206087373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17881808556850003470724915 26822712835275005206087373)
            ·
              refine ⟨10058517313228126952282765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26822712835275005206087373 10058517313228126952282765)
              ·
                refine ⟨3771943992460547607106037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10058517313228126952282765 3771943992460547607106037)
                ·
                  refine ⟨353619749293176338166191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3771943992460547607106037 353619749293176338166191)
                  ·
                    rfl

theorem cell21_1549512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 5].length) (baseStart_1549512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1549512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1549512 prefixEnd_1549512 := by exact prefixLift 1549512
  have htrace : WordTrace (prefixWord ++ tailWord_1549512) baseStart_1549512 baseEnd_1549512 := by
    simpa [prefixWord, tailWord_1549512, baseEnd_1549512] using wordTrace_append hprefix tailTrace_1549512
  have hstable : (prefixWord ++ tailWord_1549512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549512).length < 2 ^ (prefixWord ++ tailWord_1549512).sum := by decide
  have hdescent : baseEnd_1549512 < baseStart_1549512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549546 : List Nat := [3, 1, 3, 1, 1, 3, 3, 3, 3]
def baseStart_1549546 : Nat := 118140960795 + 1549546 * 2 ^ 59
def prefixEnd_1549546 : Nat := 4983230072969 + 3 ^ 40 * 1549546 * 2
def baseEnd_1549546 : Nat := 353627508556399834599455

theorem tailTrace_1549546 : CollatzResearch.WordTrace tailWord_1549546 prefixEnd_1549546 353627508556399834599455 := by
  unfold tailWord_1549546
  simp only [CollatzResearch.WordTrace]
  refine ⟨14129146411066739558183123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37677723762844638821821661 14129146411066739558183123)
  ·
    refine ⟨21193719616600109337274685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14129146411066739558183123 21193719616600109337274685)
    ·
      refine ⟨7947644856225041001478007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21193719616600109337274685 7947644856225041001478007)
      ·
        refine ⟨11921467284337561502217011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7947644856225041001478007 11921467284337561502217011)
        ·
          refine ⟨17882200926506342253325517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11921467284337561502217011 17882200926506342253325517)
          ·
            refine ⟨6705825347439878344997069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17882200926506342253325517 6705825347439878344997069)
            ·
              refine ⟨2514684505289954379373901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6705825347439878344997069 2514684505289954379373901)
              ·
                refine ⟨943006689483732892265213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2514684505289954379373901 943006689483732892265213)
                ·
                  refine ⟨353627508556399834599455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 943006689483732892265213 353627508556399834599455)
                  ·
                    rfl

theorem cell21_1549546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 3, 3].length) (baseStart_1549546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1549546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1549546 prefixEnd_1549546 := by exact prefixLift 1549546
  have htrace : WordTrace (prefixWord ++ tailWord_1549546) baseStart_1549546 baseEnd_1549546 := by
    simpa [prefixWord, tailWord_1549546, baseEnd_1549546] using wordTrace_append hprefix tailTrace_1549546
  have hstable : (prefixWord ++ tailWord_1549546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549546).length < 2 ^ (prefixWord ++ tailWord_1549546).sum := by decide
  have hdescent : baseEnd_1549546 < baseStart_1549546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549619 : List Nat := [1, 1, 1, 2, 5, 2, 1, 4, 4]
def baseStart_1549619 : Nat := 118140960795 + 1549619 * 2 ^ 59
def prefixEnd_1549619 : Nat := 4983230072969 + 3 ^ 40 * 1549619 * 2
def baseEnd_1549619 : Nat := 353644168150967929882639

theorem tailTrace_1549619 : CollatzResearch.WordTrace tailWord_1549619 prefixEnd_1549619 353644168150967929882639 := by
  unfold tailWord_1549619
  simp only [CollatzResearch.WordTrace]
  refine ⟨56519248173002491700139911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37679498782001661133426607 56519248173002491700139911)
  ·
    refine ⟨84778872259503737550209867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56519248173002491700139911 84778872259503737550209867)
    ·
      refine ⟨127168308389255606325314801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84778872259503737550209867 127168308389255606325314801)
      ·
        refine ⟨95376231291941704743986101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127168308389255606325314801 95376231291941704743986101)
        ·
          refine ⟨8941521683619534819748697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95376231291941704743986101 8941521683619534819748697)
          ·
            refine ⟨6706141262714651114811523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8941521683619534819748697 6706141262714651114811523)
            ·
              refine ⟨10059211894071976672217285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6706141262714651114811523 10059211894071976672217285)
              ·
                refine ⟨1886102230138495626040741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10059211894071976672217285 1886102230138495626040741)
                ·
                  refine ⟨353644168150967929882639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1886102230138495626040741 353644168150967929882639)
                  ·
                    rfl

theorem cell21_1549619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4, 4].length) (baseStart_1549619 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1549619 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1549619 prefixEnd_1549619 := by exact prefixLift 1549619
  have htrace : WordTrace (prefixWord ++ tailWord_1549619) baseStart_1549619 baseEnd_1549619 := by
    simpa [prefixWord, tailWord_1549619, baseEnd_1549619] using wordTrace_append hprefix tailTrace_1549619
  have hstable : (prefixWord ++ tailWord_1549619).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549619).length < 2 ^ (prefixWord ++ tailWord_1549619).sum := by decide
  have hdescent : baseEnd_1549619 < baseStart_1549619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549681 : List Nat := [1, 2, 2, 2, 1, 2, 4, 4, 3]
def baseStart_1549681 : Nat := 118140960795 + 1549681 * 2 ^ 59
def prefixEnd_1549681 : Nat := 4983230072969 + 3 ^ 40 * 1549681 * 2
def baseEnd_1549681 : Nat := 353658317395669599849179

theorem tailTrace_1549681 : CollatzResearch.WordTrace tailWord_1549681 prefixEnd_1549681 353658317395669599849179 := by
  unfold tailWord_1549681
  simp only [CollatzResearch.WordTrace]
  refine ⟨56521509498777876288896897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37681006332518584192597931 56521509498777876288896897)
  ·
    refine ⟨42391132124083407216672673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56521509498777876288896897 42391132124083407216672673)
    ·
      refine ⟨31793349093062555412504505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42391132124083407216672673 31793349093062555412504505)
      ·
        refine ⟨23845011819796916559378379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31793349093062555412504505 23845011819796916559378379)
        ·
          refine ⟨35767517729695374839067569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23845011819796916559378379 35767517729695374839067569)
          ·
            refine ⟨26825638297271531129300677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35767517729695374839067569 26825638297271531129300677)
            ·
              refine ⟨5029807180738412086743877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26825638297271531129300677 5029807180738412086743877)
              ·
                refine ⟨943088846388452266264477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5029807180738412086743877 943088846388452266264477)
                ·
                  refine ⟨353658317395669599849179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 943088846388452266264477 353658317395669599849179)
                  ·
                    rfl

theorem cell21_1549681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 4, 3].length) (baseStart_1549681 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1549681 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1549681 prefixEnd_1549681 := by exact prefixLift 1549681
  have htrace : WordTrace (prefixWord ++ tailWord_1549681) baseStart_1549681 baseEnd_1549681 := by
    simpa [prefixWord, tailWord_1549681, baseEnd_1549681] using wordTrace_append hprefix tailTrace_1549681
  have hstable : (prefixWord ++ tailWord_1549681).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549681).length < 2 ^ (prefixWord ++ tailWord_1549681).sum := by decide
  have hdescent : baseEnd_1549681 < baseStart_1549681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549698 : List Nat := [3, 4, 2, 1, 1, 1, 2, 2, 5]
def baseStart_1549698 : Nat := 118140960795 + 1549698 * 2 ^ 59
def prefixEnd_1549698 : Nat := 4983230072969 + 3 ^ 40 * 1549698 * 2
def baseEnd_1549698 : Nat := 353662197027281348065811

theorem tailTrace_1549698 : CollatzResearch.WordTrace tailWord_1549698 prefixEnd_1549698 353662197027281348065811 := by
  unfold tailWord_1549698
  simp only [CollatzResearch.WordTrace]
  refine ⟨14130532384929072048066437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37681419693144192128177165 14130532384929072048066437)
  ·
    refine ⟨2649474822174201009012457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14130532384929072048066437 2649474822174201009012457)
    ·
      refine ⟨1987106116630650756759343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2649474822174201009012457 1987106116630650756759343)
      ·
        refine ⟨2980659174945976135139015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1987106116630650756759343 2980659174945976135139015)
        ·
          refine ⟨4470988762418964202708523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2980659174945976135139015 4470988762418964202708523)
          ·
            refine ⟨6706483143628446304062785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4470988762418964202708523 6706483143628446304062785)
            ·
              refine ⟨5029862357721334728047089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6706483143628446304062785 5029862357721334728047089)
              ·
                refine ⟨3772396768291001046035317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5029862357721334728047089 3772396768291001046035317)
                ·
                  refine ⟨353662197027281348065811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3772396768291001046035317 353662197027281348065811)
                  ·
                    rfl

theorem cell21_1549698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_1549698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1549698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1549698 prefixEnd_1549698 := by exact prefixLift 1549698
  have htrace : WordTrace (prefixWord ++ tailWord_1549698) baseStart_1549698 baseEnd_1549698 := by
    simpa [prefixWord, tailWord_1549698, baseEnd_1549698] using wordTrace_append hprefix tailTrace_1549698
  have hstable : (prefixWord ++ tailWord_1549698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549698).length < 2 ^ (prefixWord ++ tailWord_1549698).sum := by decide
  have hdescent : baseEnd_1549698 < baseStart_1549698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549740 : List Nat := [2, 2, 1, 1, 1, 1, 7, 1, 5]
def baseStart_1549740 : Nat := 118140960795 + 1549740 * 2 ^ 59
def prefixEnd_1549740 : Nat := 4983230072969 + 3 ^ 40 * 1549740 * 2
def baseEnd_1549740 : Nat := 353671781999498608365725

theorem tailTrace_1549740 : CollatzResearch.WordTrace tailWord_1549740 prefixEnd_1549740 353671781999498608365725 := by
  unfold tailWord_1549740
  simp only [CollatzResearch.WordTrace]
  refine ⟨28261830702782064682647337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37682440937042752910196449 28261830702782064682647337)
  ·
    refine ⟨21196373027086548511985503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28261830702782064682647337 21196373027086548511985503)
    ·
      refine ⟨31794559540629822767978255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21196373027086548511985503 31794559540629822767978255)
      ·
        refine ⟨47691839310944734151967383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31794559540629822767978255 47691839310944734151967383)
        ·
          refine ⟨71537758966417101227951075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47691839310944734151967383 71537758966417101227951075)
          ·
            refine ⟨107306638449625651841926613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71537758966417101227951075 107306638449625651841926613)
            ·
              refine ⟨2514999338663101215045155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 107306638449625651841926613 2514999338663101215045155)
              ·
                refine ⟨3772499007994651822567733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2514999338663101215045155 3772499007994651822567733)
                ·
                  refine ⟨353671781999498608365725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3772499007994651822567733 353671781999498608365725)
                  ·
                    rfl

theorem cell21_1549740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 5].length) (baseStart_1549740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1549740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1549740 prefixEnd_1549740 := by exact prefixLift 1549740
  have htrace : WordTrace (prefixWord ++ tailWord_1549740) baseStart_1549740 baseEnd_1549740 := by
    simpa [prefixWord, tailWord_1549740, baseEnd_1549740] using wordTrace_append hprefix tailTrace_1549740
  have hstable : (prefixWord ++ tailWord_1549740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549740).length < 2 ^ (prefixWord ++ tailWord_1549740).sum := by decide
  have hdescent : baseEnd_1549740 < baseStart_1549740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549816 : List Nat := [2, 1, 2, 1, 1, 6, 1, 2, 5]
def baseStart_1549816 : Nat := 118140960795 + 1549816 * 2 ^ 59
def prefixEnd_1549816 : Nat := 4983230072969 + 3 ^ 40 * 1549816 * 2
def baseEnd_1549816 : Nat := 353689126234939365098903

theorem tailTrace_1549816 : CollatzResearch.WordTrace tailWord_1549816 prefixEnd_1549816 353689126234939365098903 := by
  unfold tailWord_1549816
  simp only [CollatzResearch.WordTrace]
  refine ⟨28263216676644397172530651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37684288902192529563374201 28263216676644397172530651)
  ·
    refine ⟨42394825014966595758795977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28263216676644397172530651 42394825014966595758795977)
    ·
      refine ⟨31796118761224946819096983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42394825014966595758795977 31796118761224946819096983)
      ·
        refine ⟨47694178141837420228645475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31796118761224946819096983 47694178141837420228645475)
        ·
          refine ⟨71541267212756130342968213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47694178141837420228645475 71541267212756130342968213)
          ·
            refine ⟨3353496900597943609826635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 71541267212756130342968213 3353496900597943609826635)
            ·
              refine ⟨5030245350896915414739953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3353496900597943609826635 5030245350896915414739953)
              ·
                refine ⟨3772684013172686561054965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5030245350896915414739953 3772684013172686561054965)
                ·
                  refine ⟨353689126234939365098903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3772684013172686561054965 353689126234939365098903)
                  ·
                    rfl

theorem cell21_1549816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 5].length) (baseStart_1549816 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1549816 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1549816 prefixEnd_1549816 := by exact prefixLift 1549816
  have htrace : WordTrace (prefixWord ++ tailWord_1549816) baseStart_1549816 baseEnd_1549816 := by
    simpa [prefixWord, tailWord_1549816, baseEnd_1549816] using wordTrace_append hprefix tailTrace_1549816
  have hstable : (prefixWord ++ tailWord_1549816).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549816).length < 2 ^ (prefixWord ++ tailWord_1549816).sum := by decide
  have hdescent : baseEnd_1549816 < baseStart_1549816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549833 : List Nat := [1, 2, 1, 1, 3, 1, 6, 3, 3]
def baseStart_1549833 : Nat := 118140960795 + 1549833 * 2 ^ 59
def prefixEnd_1549833 : Nat := 4983230072969 + 3 ^ 40 * 1549833 * 2
def baseEnd_1549833 : Nat := 353693005866551113315535

theorem tailTrace_1549833 : CollatzResearch.WordTrace tailWord_1549833 prefixEnd_1549833 353693005866551113315535 := by
  unfold tailWord_1549833
  simp only [CollatzResearch.WordTrace]
  refine ⟨56527053394227206248430153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37684702262818137498953435 56527053394227206248430153)
  ·
    refine ⟨42395290045670404686322615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56527053394227206248430153 42395290045670404686322615)
    ·
      refine ⟨63592935068505607029483923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42395290045670404686322615 63592935068505607029483923)
      ·
        refine ⟨95389402602758410544225885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63592935068505607029483923 95389402602758410544225885)
        ·
          refine ⟨35771025976034403954084707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95389402602758410544225885 35771025976034403954084707)
          ·
            refine ⟨53656538964051605931127061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35771025976034403954084707 53656538964051605931127061)
            ·
              refine ⟨2515150263939919028021581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 53656538964051605931127061 2515150263939919028021581)
              ·
                refine ⟨943181348977469635508093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2515150263939919028021581 943181348977469635508093)
                ·
                  refine ⟨353693005866551113315535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 943181348977469635508093 353693005866551113315535)
                  ·
                    rfl

theorem cell21_1549833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 3, 3].length) (baseStart_1549833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1549833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1549833 prefixEnd_1549833 := by exact prefixLift 1549833
  have htrace : WordTrace (prefixWord ++ tailWord_1549833) baseStart_1549833 baseEnd_1549833 := by
    simpa [prefixWord, tailWord_1549833, baseEnd_1549833] using wordTrace_append hprefix tailTrace_1549833
  have hstable : (prefixWord ++ tailWord_1549833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549833).length < 2 ^ (prefixWord ++ tailWord_1549833).sum := by decide
  have hdescent : baseEnd_1549833 < baseStart_1549833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549923 : List Nat := [1, 1, 1, 5, 1, 4, 1, 3, 4]
def baseStart_1549923 : Nat := 118140960795 + 1549923 * 2 ^ 59
def prefixEnd_1549923 : Nat := 4983230072969 + 3 ^ 40 * 1549923 * 2
def baseEnd_1549923 : Nat := 353713545092730956815351

theorem tailTrace_1549923 : CollatzResearch.WordTrace tailWord_1549923 prefixEnd_1549923 353713545092730956815351 := by
  unfold tailWord_1549923
  simp only [CollatzResearch.WordTrace]
  refine ⟨56530335963901151619206423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37686890642600767746137615 56530335963901151619206423)
  ·
    refine ⟨84795503945851727428809635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56530335963901151619206423 84795503945851727428809635)
    ·
      refine ⟨127193255918777591143214453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84795503945851727428809635 127193255918777591143214453)
      ·
        refine ⟨11924367742385399169676355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 127193255918777591143214453 11924367742385399169676355)
        ·
          refine ⟨17886551613578098754514533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11924367742385399169676355 17886551613578098754514533)
          ·
            refine ⟨3353728427545893516471475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17886551613578098754514533 3353728427545893516471475)
            ·
              refine ⟨5030592641318840274707213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3353728427545893516471475 5030592641318840274707213)
              ·
                refine ⟨1886472240494565103015205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5030592641318840274707213 1886472240494565103015205)
                ·
                  refine ⟨353713545092730956815351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1886472240494565103015205 353713545092730956815351)
                  ·
                    rfl

theorem cell21_1549923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3, 4].length) (baseStart_1549923 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1549923 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1549923 prefixEnd_1549923 := by exact prefixLift 1549923
  have htrace : WordTrace (prefixWord ++ tailWord_1549923) baseStart_1549923 baseEnd_1549923 := by
    simpa [prefixWord, tailWord_1549923, baseEnd_1549923] using wordTrace_append hprefix tailTrace_1549923
  have hstable : (prefixWord ++ tailWord_1549923).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549923).length < 2 ^ (prefixWord ++ tailWord_1549923).sum := by decide
  have hdescent : baseEnd_1549923 < baseStart_1549923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549954 : List Nat := [3, 4, 3, 11]
def baseStart_1549954 : Nat := 118140960795 + 1549954 * 2 ^ 59
def prefixEnd_1549954 : Nat := 4983230072969 + 3 ^ 40 * 1549954 * 2
def baseEnd_1549954 : Nat := 1455640410350130830447

theorem tailTrace_1549954 : CollatzResearch.WordTrace tailWord_1549954 prefixEnd_1549954 1455640410350130830447 := by
  unfold tailWord_1549954
  simp only [CollatzResearch.WordTrace]
  refine ⟨14132866656697210978396229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37687644417859229275723277 14132866656697210978396229)
  ·
    refine ⟨2649912498130727058449293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14132866656697210978396229 2649912498130727058449293)
    ·
      refine ⟨993717186799022646918485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2649912498130727058449293 993717186799022646918485)
      ·
        refine ⟨1455640410350130830447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 993717186799022646918485 1455640410350130830447)
        ·
          rfl

theorem cell21_1549954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 11].length) (baseStart_1549954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1549954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1549954 prefixEnd_1549954 := by exact prefixLift 1549954
  have htrace : WordTrace (prefixWord ++ tailWord_1549954) baseStart_1549954 baseEnd_1549954 := by
    simpa [prefixWord, tailWord_1549954, baseEnd_1549954] using wordTrace_append hprefix tailTrace_1549954
  have hstable : (prefixWord ++ tailWord_1549954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549954).length < 2 ^ (prefixWord ++ tailWord_1549954).sum := by decide
  have hdescent : baseEnd_1549954 < baseStart_1549954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549960 : List Nat := [2, 1, 3, 5, 1, 2, 2, 2, 3]
def baseStart_1549960 : Nat := 118140960795 + 1549960 * 2 ^ 59
def prefixEnd_1549960 : Nat := 4983230072969 + 3 ^ 40 * 1549960 * 2
def baseEnd_1549960 : Nat := 353721988996827114698609

theorem tailTrace_1549960 : CollatzResearch.WordTrace tailWord_1549960 prefixEnd_1549960 353721988996827114698609 := by
  unfold tailWord_1549960
  simp only [CollatzResearch.WordTrace]
  refine ⟨28265842732383553469151667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37687790309844737958868889 28265842732383553469151667)
  ·
    refine ⟨42398764098575330203727501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28265842732383553469151667 42398764098575330203727501)
    ·
      refine ⟨15899536536965748826397813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42398764098575330203727501 15899536536965748826397813)
      ·
        refine ⟨1490581550340538952474795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15899536536965748826397813 1490581550340538952474795)
        ·
          refine ⟨2235872325510808428712193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1490581550340538952474795 2235872325510808428712193)
          ·
            refine ⟨1676904244133106321534145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2235872325510808428712193 1676904244133106321534145)
            ·
              refine ⟨1257678183099829741150609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1676904244133106321534145 1257678183099829741150609)
              ·
                refine ⟨943258637324872305862957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1257678183099829741150609 943258637324872305862957)
                ·
                  refine ⟨353721988996827114698609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 943258637324872305862957 353721988996827114698609)
                  ·
                    rfl

theorem cell21_1549960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 2, 3].length) (baseStart_1549960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1549960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1549960 prefixEnd_1549960 := by exact prefixLift 1549960
  have htrace : WordTrace (prefixWord ++ tailWord_1549960) baseStart_1549960 baseEnd_1549960 := by
    simpa [prefixWord, tailWord_1549960, baseEnd_1549960] using wordTrace_append hprefix tailTrace_1549960
  have hstable : (prefixWord ++ tailWord_1549960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549960).length < 2 ^ (prefixWord ++ tailWord_1549960).sum := by decide
  have hdescent : baseEnd_1549960 < baseStart_1549960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550058 : List Nat := [3, 1, 3, 1, 1, 1, 3, 2, 6]
def baseStart_1550058 : Nat := 118140960795 + 1550058 * 2 ^ 59
def prefixEnd_1550058 : Nat := 4983230072969 + 3 ^ 40 * 1550058 * 2
def baseEnd_1550058 : Nat := 353744353932000722065075

theorem tailTrace_1550058 : CollatzResearch.WordTrace tailWord_1550058 prefixEnd_1550058 353744353932000722065075 := by
  unfold tailWord_1550058
  simp only [CollatzResearch.WordTrace]
  refine ⟨14133814954603017418842707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37690173212274713116913885 14133814954603017418842707)
  ·
    refine ⟨21200722431904526128264061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14133814954603017418842707 21200722431904526128264061)
    ·
      refine ⟨7950270911964197298099023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21200722431904526128264061 7950270911964197298099023)
      ·
        refine ⟨11925406367946295947148535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7950270911964197298099023 11925406367946295947148535)
        ·
          refine ⟨17888109551919443920722803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11925406367946295947148535 17888109551919443920722803)
          ·
            refine ⟨26832164327879165881084205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17888109551919443920722803 26832164327879165881084205)
            ·
              refine ⟨10062061622954687205406577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26832164327879165881084205 10062061622954687205406577)
              ·
                refine ⟨7546546217216015404054933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10062061622954687205406577 7546546217216015404054933)
                ·
                  refine ⟨353744353932000722065075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7546546217216015404054933 353744353932000722065075)
                  ·
                    rfl

theorem cell21_1550058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_1550058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1550058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1550058 prefixEnd_1550058 := by exact prefixLift 1550058
  have htrace : WordTrace (prefixWord ++ tailWord_1550058) baseStart_1550058 baseEnd_1550058 := by
    simpa [prefixWord, tailWord_1550058, baseEnd_1550058] using wordTrace_append hprefix tailTrace_1550058
  have hstable : (prefixWord ++ tailWord_1550058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550058).length < 2 ^ (prefixWord ++ tailWord_1550058).sum := by decide
  have hdescent : baseEnd_1550058 < baseStart_1550058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550078 : List Nat := [4, 2, 2, 1, 3, 2, 1, 1, 5]
def baseStart_1550078 : Nat := 118140960795 + 1550078 * 2 ^ 59
def prefixEnd_1550078 : Nat := 4983230072969 + 3 ^ 40 * 1550078 * 2
def baseEnd_1550078 : Nat := 353748918204485131731701

theorem tailTrace_1550078 : CollatzResearch.WordTrace tailWord_1550078 prefixEnd_1550078 353748918204485131731701 := by
  unfold tailWord_1550078
  simp only [CollatzResearch.WordTrace]
  refine ⟨7066998659792451636387361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37690659518893075394065925 7066998659792451636387361)
  ·
    refine ⟨5300248994844338727290521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7066998659792451636387361 5300248994844338727290521)
    ·
      refine ⟨3975186746133254045467891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5300248994844338727290521 3975186746133254045467891)
      ·
        refine ⟨5962780119199881068201837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3975186746133254045467891 5962780119199881068201837)
        ·
          refine ⟨2236042544699955400575689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5962780119199881068201837 2236042544699955400575689)
          ·
            refine ⟨1677031908524966550431767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2236042544699955400575689 1677031908524966550431767)
            ·
              refine ⟨2515547862787449825647651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1677031908524966550431767 2515547862787449825647651)
              ·
                refine ⟨3773321794181174738471477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2515547862787449825647651 3773321794181174738471477)
                ·
                  refine ⟨353748918204485131731701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3773321794181174738471477 353748918204485131731701)
                  ·
                    rfl

theorem cell21_1550078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_1550078 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1550078 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1550078 prefixEnd_1550078 := by exact prefixLift 1550078
  have htrace : WordTrace (prefixWord ++ tailWord_1550078) baseStart_1550078 baseEnd_1550078 := by
    simpa [prefixWord, tailWord_1550078, baseEnd_1550078] using wordTrace_append hprefix tailTrace_1550078
  have hstable : (prefixWord ++ tailWord_1550078).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550078).length < 2 ^ (prefixWord ++ tailWord_1550078).sum := by decide
  have hdescent : baseEnd_1550078 < baseStart_1550078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550303 : List Nat := [1, 1, 2, 3, 4, 2, 2, 2, 4]
def baseStart_1550303 : Nat := 118140960795 + 1550303 * 2 ^ 59
def prefixEnd_1550303 : Nat := 4983230072969 + 3 ^ 40 * 1550303 * 2
def baseEnd_1550303 : Nat := 353800266269934740481241

theorem tailTrace_1550303 : CollatzResearch.WordTrace tailWord_1550303 prefixEnd_1550303 353800266269934740481241 := by
  unfold tailWord_1550303
  simp only [CollatzResearch.WordTrace]
  refine ⟨56544195702524476518039563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37696130468349651012026375 56544195702524476518039563)
  ·
    refine ⟨84816293553786714777059345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56544195702524476518039563 84816293553786714777059345)
    ·
      refine ⟨63612220165340036082794509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84816293553786714777059345 63612220165340036082794509)
      ·
        refine ⟨23854582562002513531047941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63612220165340036082794509 23854582562002513531047941)
        ·
          refine ⟨4472734230375471287071489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23854582562002513531047941 4472734230375471287071489)
          ·
            refine ⟨3354550672781603465303617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4472734230375471287071489 3354550672781603465303617)
            ·
              refine ⟨2515913004586202598977713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3354550672781603465303617 2515913004586202598977713)
              ·
                refine ⟨1886934753439651949233285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2515913004586202598977713 1886934753439651949233285)
                ·
                  refine ⟨353800266269934740481241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1886934753439651949233285 353800266269934740481241)
                  ·
                    rfl

theorem cell21_1550303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2, 4].length) (baseStart_1550303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1550303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1550303 prefixEnd_1550303 := by exact prefixLift 1550303
  have htrace : WordTrace (prefixWord ++ tailWord_1550303) baseStart_1550303 baseEnd_1550303 := by
    simpa [prefixWord, tailWord_1550303, baseEnd_1550303] using wordTrace_append hprefix tailTrace_1550303
  have hstable : (prefixWord ++ tailWord_1550303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550303).length < 2 ^ (prefixWord ++ tailWord_1550303).sum := by decide
  have hdescent : baseEnd_1550303 < baseStart_1550303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550362 : List Nat := [3, 1, 1, 3, 1, 4, 1, 1, 6]
def baseStart_1550362 : Nat := 118140960795 + 1550362 * 2 ^ 59
def prefixEnd_1550362 : Nat := 4983230072969 + 3 ^ 40 * 1550362 * 2
def baseEnd_1550362 : Nat := 353813730873763748997787

theorem tailTrace_1550362 : CollatzResearch.WordTrace tailWord_1550362 prefixEnd_1550362 353813730873763748997787 := by
  unfold tailWord_1550362
  simp only [CollatzResearch.WordTrace]
  refine ⟨14136586902327682398609335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37697565072873819729624893 14136586902327682398609335)
  ·
    refine ⟨21204880353491523597914003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14136586902327682398609335 21204880353491523597914003)
    ·
      refine ⟨31807320530237285396871005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21204880353491523597914003 31807320530237285396871005)
      ·
        refine ⟨11927745198838982023826627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31807320530237285396871005 11927745198838982023826627)
        ·
          refine ⟨17891617798258473035739941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11927745198838982023826627 17891617798258473035739941)
          ·
            refine ⟨3354678337173463694201239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17891617798258473035739941 3354678337173463694201239)
            ·
              refine ⟨5032017505760195541301859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3354678337173463694201239 5032017505760195541301859)
              ·
                refine ⟨7548026258640293311952789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5032017505760195541301859 7548026258640293311952789)
                ·
                  refine ⟨353813730873763748997787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7548026258640293311952789 353813730873763748997787)
                  ·
                    rfl

theorem cell21_1550362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 6].length) (baseStart_1550362 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1550362 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1550362 prefixEnd_1550362 := by exact prefixLift 1550362
  have htrace : WordTrace (prefixWord ++ tailWord_1550362) baseStart_1550362 baseEnd_1550362 := by
    simpa [prefixWord, tailWord_1550362, baseEnd_1550362] using wordTrace_append hprefix tailTrace_1550362
  have hstable : (prefixWord ++ tailWord_1550362).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550362).length < 2 ^ (prefixWord ++ tailWord_1550362).sum := by decide
  have hdescent : baseEnd_1550362 < baseStart_1550362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550365 : List Nat := [1, 4, 2, 2, 2, 1, 2, 4, 3]
def baseStart_1550365 : Nat := 118140960795 + 1550365 * 2 ^ 59
def prefixEnd_1550365 : Nat := 4983230072969 + 3 ^ 40 * 1550365 * 2
def baseEnd_1550365 : Nat := 353814415514636410447781

theorem tailTrace_1550365 : CollatzResearch.WordTrace tailWord_1550365 prefixEnd_1550365 353814415514636410447781 := by
  unfold tailWord_1550365
  simp only [CollatzResearch.WordTrace]
  refine ⟨56546457028299861106796549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37697638018866574071197699 56546457028299861106796549)
  ·
    refine ⟨10602460692806223957524353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56546457028299861106796549 10602460692806223957524353)
    ·
      refine ⟨7951845519604667968143265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10602460692806223957524353 7951845519604667968143265)
      ·
        refine ⟨5963884139703500976107449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7951845519604667968143265 5963884139703500976107449)
        ·
          refine ⟨4472913104777625732080587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5963884139703500976107449 4472913104777625732080587)
          ·
            refine ⟨6709369657166438598120881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4472913104777625732080587 6709369657166438598120881)
            ·
              refine ⟨5032027242874828948590661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6709369657166438598120881 5032027242874828948590661)
              ·
                refine ⟨943505108039030427860749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5032027242874828948590661 943505108039030427860749)
                ·
                  refine ⟨353814415514636410447781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 943505108039030427860749 353814415514636410447781)
                  ·
                    rfl

theorem cell21_1550365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 4, 3].length) (baseStart_1550365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1550365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1550365 prefixEnd_1550365 := by exact prefixLift 1550365
  have htrace : WordTrace (prefixWord ++ tailWord_1550365) baseStart_1550365 baseEnd_1550365 := by
    simpa [prefixWord, tailWord_1550365, baseEnd_1550365] using wordTrace_append hprefix tailTrace_1550365
  have hstable : (prefixWord ++ tailWord_1550365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550365).length < 2 ^ (prefixWord ++ tailWord_1550365).sum := by decide
  have hdescent : baseEnd_1550365 < baseStart_1550365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550393 : List Nat := [1, 2, 1, 5, 3, 1, 1, 7]
def baseStart_1550393 : Nat := 118140960795 + 1550393 * 2 ^ 59
def prefixEnd_1550393 : Nat := 4983230072969 + 3 ^ 40 * 1550393 * 2
def baseEnd_1550393 : Nat := 117940268498704861327019

theorem tailTrace_1550393 : CollatzResearch.WordTrace tailWord_1550393 prefixEnd_1550393 117940268498704861327019 := by
  unfold tailWord_1550393
  simp only [CollatzResearch.WordTrace]
  refine ⟨56547478272198421888815833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37698318848132281259210555 56547478272198421888815833)
  ·
    refine ⟨42410608704148816416611875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56547478272198421888815833 42410608704148816416611875)
    ·
      refine ⟨63615913056223224624917813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42410608704148816416611875 63615913056223224624917813)
      ·
        refine ⟨5963991849020927308586045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63615913056223224624917813 5963991849020927308586045)
        ·
          refine ⟨2236496943382847740719767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5963991849020927308586045 2236496943382847740719767)
          ·
            refine ⟨3354745415074271611079651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2236496943382847740719767 3354745415074271611079651)
            ·
              refine ⟨5032118122611407416619477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3354745415074271611079651 5032118122611407416619477)
              ·
                refine ⟨117940268498704861327019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5032118122611407416619477 117940268498704861327019)
                ·
                  rfl

theorem cell21_1550393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 7].length) (baseStart_1550393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1550393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1550393 prefixEnd_1550393 := by exact prefixLift 1550393
  have htrace : WordTrace (prefixWord ++ tailWord_1550393) baseStart_1550393 baseEnd_1550393 := by
    simpa [prefixWord, tailWord_1550393, baseEnd_1550393] using wordTrace_append hprefix tailTrace_1550393
  have hstable : (prefixWord ++ tailWord_1550393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550393).length < 2 ^ (prefixWord ++ tailWord_1550393).sum := by decide
  have hdescent : baseEnd_1550393 < baseStart_1550393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550424 : List Nat := [2, 1, 2, 2, 1, 6, 1, 1, 5]
def baseStart_1550424 : Nat := 118140960795 + 1550424 * 2 ^ 59
def prefixEnd_1550424 : Nat := 4983230072969 + 3 ^ 40 * 1550424 * 2
def baseEnd_1550424 : Nat := 353827880118465418964327

theorem tailTrace_1550424 : CollatzResearch.WordTrace tailWord_1550424 prefixEnd_1550424 353827880118465418964327 := by
  unfold tailWord_1550424
  simp only [CollatzResearch.WordTrace]
  refine ⟨28274304467543057091597163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37699072623390742788796217 28274304467543057091597163)
  ·
    refine ⟨42411456701314585637395745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28274304467543057091597163 42411456701314585637395745)
    ·
      refine ⟨31808592525985939228046809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42411456701314585637395745 31808592525985939228046809)
      ·
        refine ⟨23856444394489454421035107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31808592525985939228046809 23856444394489454421035107)
        ·
          refine ⟨35784666591734181631552661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23856444394489454421035107 35784666591734181631552661)
          ·
            refine ⟨1677406246487539763979031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 35784666591734181631552661 1677406246487539763979031)
            ·
              refine ⟨2516109369731309645968547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1677406246487539763979031 2516109369731309645968547)
              ·
                refine ⟨3774164054596964468952821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2516109369731309645968547 3774164054596964468952821)
                ·
                  refine ⟨353827880118465418964327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3774164054596964468952821 353827880118465418964327)
                  ·
                    rfl

theorem cell21_1550424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 5].length) (baseStart_1550424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1550424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1550424 prefixEnd_1550424 := by exact prefixLift 1550424
  have htrace : WordTrace (prefixWord ++ tailWord_1550424) baseStart_1550424 baseEnd_1550424 := by
    simpa [prefixWord, tailWord_1550424, baseEnd_1550424] using wordTrace_append hprefix tailTrace_1550424
  have hstable : (prefixWord ++ tailWord_1550424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550424).length < 2 ^ (prefixWord ++ tailWord_1550424).sum := by decide
  have hdescent : baseEnd_1550424 < baseStart_1550424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550500 : List Nat := [2, 3, 1, 2, 4, 1, 1, 2, 5]
def baseStart_1550500 : Nat := 118140960795 + 1550500 * 2 ^ 59
def prefixEnd_1550500 : Nat := 4983230072969 + 3 ^ 40 * 1550500 * 2
def baseEnd_1550500 : Nat := 353845224353906175697505

theorem tailTrace_1550500 : CollatzResearch.WordTrace tailWord_1550500 prefixEnd_1550500 353845224353906175697505 := by
  unfold tailWord_1550500
  simp only [CollatzResearch.WordTrace]
  refine ⟨28275690441405389581480477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37700920588540519441973969 28275690441405389581480477)
  ·
    refine ⟨10603383915527021093055179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28275690441405389581480477 10603383915527021093055179)
    ·
      refine ⟨15905075873290531639582769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10603383915527021093055179 15905075873290531639582769)
      ·
        refine ⟨11928806904967898729687077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15905075873290531639582769 11928806904967898729687077)
        ·
          refine ⟨2236651294681481011816327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11928806904967898729687077 2236651294681481011816327)
          ·
            refine ⟨3354976942022221517724491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2236651294681481011816327 3354976942022221517724491)
            ·
              refine ⟨5032465413033332276586737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3354976942022221517724491 5032465413033332276586737)
              ·
                refine ⟨3774349059774999207440053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5032465413033332276586737 3774349059774999207440053)
                ·
                  refine ⟨353845224353906175697505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3774349059774999207440053 353845224353906175697505)
                  ·
                    rfl

theorem cell21_1550500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_1550500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1550500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1550500 prefixEnd_1550500 := by exact prefixLift 1550500
  have htrace : WordTrace (prefixWord ++ tailWord_1550500) baseStart_1550500 baseEnd_1550500 := by
    simpa [prefixWord, tailWord_1550500, baseEnd_1550500] using wordTrace_append hprefix tailTrace_1550500
  have hstable : (prefixWord ++ tailWord_1550500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550500).length < 2 ^ (prefixWord ++ tailWord_1550500).sum := by decide
  have hdescent : baseEnd_1550500 < baseStart_1550500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550528 : List Nat := [2, 1, 1, 2, 5, 2, 8]
def baseStart_1550528 : Nat := 118140960795 + 1550528 * 2 ^ 59
def prefixEnd_1550528 : Nat := 4983230072969 + 3 ^ 40 * 1550528 * 2
def baseEnd_1550528 : Nat := 39316846037264927692309

theorem tailTrace_1550528 : CollatzResearch.WordTrace tailWord_1550528 prefixEnd_1550528 39316846037264927692309 := by
  unfold tailWord_1550528
  simp only [CollatzResearch.WordTrace]
  refine ⟨28276201063354669972490119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37701601417806226629986825 28276201063354669972490119)
  ·
    refine ⟨42414301595032004958735179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28276201063354669972490119 42414301595032004958735179)
    ·
      refine ⟨63621452392548007438102769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42414301595032004958735179 63621452392548007438102769)
      ·
        refine ⟨47716089294411005578577077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63621452392548007438102769 47716089294411005578577077)
        ·
          refine ⟨4473383371351031772991601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47716089294411005578577077 4473383371351031772991601)
          ·
            refine ⟨3355037528513273829743701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4473383371351031772991601 3355037528513273829743701)
            ·
              refine ⟨39316846037264927692309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3355037528513273829743701 39316846037264927692309)
              ·
                rfl

theorem cell21_1550528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 8].length) (baseStart_1550528 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1550528 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1550528 prefixEnd_1550528 := by exact prefixLift 1550528
  have htrace : WordTrace (prefixWord ++ tailWord_1550528) baseStart_1550528 baseEnd_1550528 := by
    simpa [prefixWord, tailWord_1550528, baseEnd_1550528] using wordTrace_append hprefix tailTrace_1550528
  have hstable : (prefixWord ++ tailWord_1550528).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550528).length < 2 ^ (prefixWord ++ tailWord_1550528).sum := by decide
  have hdescent : baseEnd_1550528 < baseStart_1550528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550590 : List Nat := [4, 2, 2, 1, 1, 1, 1, 3, 6]
def baseStart_1550590 : Nat := 118140960795 + 1550590 * 2 ^ 59
def prefixEnd_1550590 : Nat := 4983230072969 + 3 ^ 40 * 1550590 * 2
def baseEnd_1550590 : Nat := 353865763580086019197321

theorem tailTrace_1550590 : CollatzResearch.WordTrace tailWord_1550590 prefixEnd_1550590 353865763580086019197321 := by
  unfold tailWord_1550590
  simp only [CollatzResearch.WordTrace]
  refine ⟨7069332931560590566717153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37703108968323149689158149 7069332931560590566717153)
  ·
    refine ⟨5301999698670442925037865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7069332931560590566717153 5301999698670442925037865)
    ·
      refine ⟨3976499774002832193778399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5301999698670442925037865 3976499774002832193778399)
      ·
        refine ⟨5964749661004248290667599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3976499774002832193778399 5964749661004248290667599)
        ·
          refine ⟨8947124491506372436001399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5964749661004248290667599 8947124491506372436001399)
          ·
            refine ⟨13420686737259558654002099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8947124491506372436001399 13420686737259558654002099)
            ·
              refine ⟨20131030105889337981003149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13420686737259558654002099 20131030105889337981003149)
              ·
                refine ⟨7549136289708501742876181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20131030105889337981003149 7549136289708501742876181)
                ·
                  refine ⟨353865763580086019197321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7549136289708501742876181 353865763580086019197321)
                  ·
                    rfl

theorem cell21_1550590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_1550590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1550590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1550590 prefixEnd_1550590 := by exact prefixLift 1550590
  have htrace : WordTrace (prefixWord ++ tailWord_1550590) baseStart_1550590 baseEnd_1550590 := by
    simpa [prefixWord, tailWord_1550590, baseEnd_1550590] using wordTrace_append hprefix tailTrace_1550590
  have hstable : (prefixWord ++ tailWord_1550590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550590).length < 2 ^ (prefixWord ++ tailWord_1550590).sum := by decide
  have hdescent : baseEnd_1550590 < baseStart_1550590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550593 : List Nat := [1, 2, 4, 1, 1, 2, 5, 2, 3]
def baseStart_1550593 : Nat := 118140960795 + 1550593 * 2 ^ 59
def prefixEnd_1550593 : Nat := 4983230072969 + 3 ^ 40 * 1550593 * 2
def baseEnd_1550593 : Nat := 353866448220958680647315

theorem tailTrace_1550593 : CollatzResearch.WordTrace tailWord_1550593 prefixEnd_1550593 353866448220958680647315 := by
  unfold tailWord_1550593
  simp only [CollatzResearch.WordTrace]
  refine ⟨56554772871473856046096433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37703181914315904030730955 56554772871473856046096433)
  ·
    refine ⟨42416079653605392034572325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56554772871473856046096433 42416079653605392034572325)
    ·
      refine ⟨7953014935051011006482311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42416079653605392034572325 7953014935051011006482311)
      ·
        refine ⟨11929522402576516509723467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7953014935051011006482311 11929522402576516509723467)
        ·
          refine ⟨17894283603864774764585201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11929522402576516509723467 17894283603864774764585201)
          ·
            refine ⟨13420712702898581073438901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17894283603864774764585201 13420712702898581073438901)
            ·
              refine ⟨1258191815896741975634897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13420712702898581073438901 1258191815896741975634897)
              ·
                refine ⟨943643861922556481726173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1258191815896741975634897 943643861922556481726173)
                ·
                  refine ⟨353866448220958680647315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 943643861922556481726173 353866448220958680647315)
                  ·
                    rfl

theorem cell21_1550593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 2, 3].length) (baseStart_1550593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1550593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1550593 prefixEnd_1550593 := by exact prefixLift 1550593
  have htrace : WordTrace (prefixWord ++ tailWord_1550593) baseStart_1550593 baseEnd_1550593 := by
    simpa [prefixWord, tailWord_1550593, baseEnd_1550593] using wordTrace_append hprefix tailTrace_1550593
  have hstable : (prefixWord ++ tailWord_1550593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550593).length < 2 ^ (prefixWord ++ tailWord_1550593).sum := by decide
  have hdescent : baseEnd_1550593 < baseStart_1550593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550604 : List Nat := [2, 2, 1, 2, 2, 2, 4, 6]
def baseStart_1550604 : Nat := 118140960795 + 1550604 * 2 ^ 59
def prefixEnd_1550604 : Nat := 4983230072969 + 3 ^ 40 * 1550604 * 2
def baseEnd_1550604 : Nat := 117956319523608368654653

theorem tailTrace_1550604 : CollatzResearch.WordTrace tailWord_1550604 prefixEnd_1550604 117956319523608368654653 := by
  unfold tailWord_1550604
  simp only [CollatzResearch.WordTrace]
  refine ⟨28277587037217002462373433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37703449382956003283164577 28277587037217002462373433)
  ·
    refine ⟨21208190277912751846780075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28277587037217002462373433 21208190277912751846780075)
    ·
      refine ⟨31812285416869127770170113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21208190277912751846780075 31812285416869127770170113)
      ·
        refine ⟨23859214062651845827627585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31812285416869127770170113 23859214062651845827627585)
        ·
          refine ⟨17894410546988884370720689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23859214062651845827627585 17894410546988884370720689)
          ·
            refine ⟨13420807910241663278040517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17894410546988884370720689 13420807910241663278040517)
            ·
              refine ⟨2516401483170311864632597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13420807910241663278040517 2516401483170311864632597)
              ·
                refine ⟨117956319523608368654653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2516401483170311864632597 117956319523608368654653)
                ·
                  rfl

theorem cell21_1550604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 6].length) (baseStart_1550604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1550604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1550604 prefixEnd_1550604 := by exact prefixLift 1550604
  have htrace : WordTrace (prefixWord ++ tailWord_1550604) baseStart_1550604 baseEnd_1550604 := by
    simpa [prefixWord, tailWord_1550604, baseEnd_1550604] using wordTrace_append hprefix tailTrace_1550604
  have hstable : (prefixWord ++ tailWord_1550604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550604).length < 2 ^ (prefixWord ++ tailWord_1550604).sum := by decide
  have hdescent : baseEnd_1550604 < baseStart_1550604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550638 : List Nat := [4, 1, 3, 3, 2, 8]
def baseStart_1550638 : Nat := 118140960795 + 1550638 * 2 ^ 59
def prefixEnd_1550638 : Nat := 4983230072969 + 3 ^ 40 * 1550638 * 2
def baseEnd_1550638 : Nat := 13106545104964763051749

theorem tailTrace_1550638 : CollatzResearch.WordTrace tailWord_1550638 prefixEnd_1550638 13106545104964763051749 := by
  unfold tailWord_1550638
  simp only [CollatzResearch.WordTrace]
  refine ⟨7069551769538853591435571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37704276104207219154323045 7069551769538853591435571)
  ·
    refine ⟨10604327654308280387153357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7069551769538853591435571 10604327654308280387153357)
    ·
      refine ⟨3976622870365605145182509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10604327654308280387153357 3976622870365605145182509)
      ·
        refine ⟨1491233576387101929443441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3976622870365605145182509 1491233576387101929443441)
        ·
          refine ⟨1118425182290326447082581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1491233576387101929443441 1118425182290326447082581)
          ·
            refine ⟨13106545104964763051749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1118425182290326447082581 13106545104964763051749)
            ·
              rfl

theorem cell21_1550638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 8].length) (baseStart_1550638 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1550638 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1550638 prefixEnd_1550638 := by exact prefixLift 1550638
  have htrace : WordTrace (prefixWord ++ tailWord_1550638) baseStart_1550638 baseEnd_1550638 := by
    simpa [prefixWord, tailWord_1550638, baseEnd_1550638] using wordTrace_append hprefix tailTrace_1550638
  have hstable : (prefixWord ++ tailWord_1550638).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550638).length < 2 ^ (prefixWord ++ tailWord_1550638).sum := by decide
  have hdescent : baseEnd_1550638 < baseStart_1550638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550652 : List Nat := [2, 2, 2, 2, 1, 2, 3, 4, 3]
def baseStart_1550652 : Nat := 118140960795 + 1550652 * 2 ^ 59
def prefixEnd_1550652 : Nat := 4983230072969 + 3 ^ 40 * 1550652 * 2
def baseEnd_1550652 : Nat := 353879912824787689163861

theorem tailTrace_1550652 : CollatzResearch.WordTrace tailWord_1550652 prefixEnd_1550652 353879912824787689163861 := by
  unfold tailWord_1550652
  simp only [CollatzResearch.WordTrace]
  refine ⟨28278462389130054561247105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37704616518840072748329473 28278462389130054561247105)
  ·
    refine ⟨21208846791847540920935329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28278462389130054561247105 21208846791847540920935329)
    ·
      refine ⟨15906635093885655690701497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21208846791847540920935329 15906635093885655690701497)
      ·
        refine ⟨11929976320414241768026123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15906635093885655690701497 11929976320414241768026123)
        ·
          refine ⟨17894964480621362652039185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11929976320414241768026123 17894964480621362652039185)
          ·
            refine ⟨13421223360466021989029389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17894964480621362652039185 13421223360466021989029389)
            ·
              refine ⟨5032958760174758245886021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13421223360466021989029389 5032958760174758245886021)
              ·
                refine ⟨943679767532767171103629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5032958760174758245886021 943679767532767171103629)
                ·
                  refine ⟨353879912824787689163861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 943679767532767171103629 353879912824787689163861)
                  ·
                    rfl

theorem cell21_1550652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 4, 3].length) (baseStart_1550652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1550652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1550652 prefixEnd_1550652 := by exact prefixLift 1550652
  have htrace : WordTrace (prefixWord ++ tailWord_1550652) baseStart_1550652 baseEnd_1550652 := by
    simpa [prefixWord, tailWord_1550652, baseEnd_1550652] using wordTrace_append hprefix tailTrace_1550652
  have hstable : (prefixWord ++ tailWord_1550652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550652).length < 2 ^ (prefixWord ++ tailWord_1550652).sum := by decide
  have hdescent : baseEnd_1550652 < baseStart_1550652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550700 : List Nat := [2, 2, 1, 1, 7, 1, 1, 2, 4]
def baseStart_1550700 : Nat := 118140960795 + 1550700 * 2 ^ 59
def prefixEnd_1550700 : Nat := 4983230072969 + 3 ^ 40 * 1550700 * 2
def baseEnd_1550700 : Nat := 353890867078750272363763

theorem tailTrace_1550700 : CollatzResearch.WordTrace tailWord_1550700 prefixEnd_1550700 353890867078750272363763 := by
  unfold tailWord_1550700
  simp only [CollatzResearch.WordTrace]
  refine ⟨28279337741043106660120777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37705783654724142213494369 28279337741043106660120777)
  ·
    refine ⟨21209503305782329995090583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28279337741043106660120777 21209503305782329995090583)
    ·
      refine ⟨31814254958673494992635875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21209503305782329995090583 31814254958673494992635875)
      ·
        refine ⟨47721382438010242488953813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31814254958673494992635875 47721382438010242488953813)
        ·
          refine ⟨1118469900890865058334855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 47721382438010242488953813 1118469900890865058334855)
          ·
            refine ⟨1677704851336297587502283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1118469900890865058334855 1677704851336297587502283)
            ·
              refine ⟨2516557277004446381253425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1677704851336297587502283 2516557277004446381253425)
              ·
                refine ⟨1887417957753334785940069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2516557277004446381253425 1887417957753334785940069)
                ·
                  refine ⟨353890867078750272363763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1887417957753334785940069 353890867078750272363763)
                  ·
                    rfl

theorem cell21_1550700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 2, 4].length) (baseStart_1550700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1550700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1550700 prefixEnd_1550700 := by exact prefixLift 1550700
  have htrace : WordTrace (prefixWord ++ tailWord_1550700) baseStart_1550700 baseEnd_1550700 := by
    simpa [prefixWord, tailWord_1550700, baseEnd_1550700] using wordTrace_append hprefix tailTrace_1550700
  have hstable : (prefixWord ++ tailWord_1550700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550700).length < 2 ^ (prefixWord ++ tailWord_1550700).sum := by decide
  have hdescent : baseEnd_1550700 < baseStart_1550700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550773 : List Nat := [1, 3, 3, 2, 3, 1, 2, 6]
def baseStart_1550773 : Nat := 118140960795 + 1550773 * 2 ^ 59
def prefixEnd_1550773 : Nat := 4983230072969 + 3 ^ 40 * 1550773 * 2
def baseEnd_1550773 : Nat := 117969175557772789215649

theorem tailTrace_1550773 : CollatzResearch.WordTrace tailWord_1550773 prefixEnd_1550773 117969175557772789215649 := by
  unfold tailWord_1550773
  simp only [CollatzResearch.WordTrace]
  refine ⟨56561338010821746787648973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37707558673881164525099315 56561338010821746787648973)
  ·
    refine ⟨21210501754058155045368365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56561338010821746787648973 21210501754058155045368365)
    ·
      refine ⟨7953938157771808142013137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21210501754058155045368365 7953938157771808142013137)
      ·
        refine ⟨5965453618328856106509853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7953938157771808142013137 5965453618328856106509853)
        ·
          refine ⟨2237045106873321039941195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5965453618328856106509853 2237045106873321039941195)
          ·
            refine ⟨3355567660309981559911793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2237045106873321039941195 3355567660309981559911793)
            ·
              refine ⟨2516675745232486169933845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3355567660309981559911793 2516675745232486169933845)
              ·
                refine ⟨117969175557772789215649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2516675745232486169933845 117969175557772789215649)
                ·
                  rfl

theorem cell21_1550773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 6].length) (baseStart_1550773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1550773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1550773 prefixEnd_1550773 := by exact prefixLift 1550773
  have htrace : WordTrace (prefixWord ++ tailWord_1550773) baseStart_1550773 baseEnd_1550773 := by
    simpa [prefixWord, tailWord_1550773, baseEnd_1550773] using wordTrace_append hprefix tailTrace_1550773
  have hstable : (prefixWord ++ tailWord_1550773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550773).length < 2 ^ (prefixWord ++ tailWord_1550773).sum := by decide
  have hdescent : baseEnd_1550773 < baseStart_1550773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550815 : List Nat := [1, 1, 2, 3, 3, 11]
def baseStart_1550815 : Nat := 118140960795 + 1550815 * 2 ^ 59
def prefixEnd_1550815 : Nat := 4983230072969 + 3 ^ 40 * 1550815 * 2
def baseEnd_1550815 : Nat := 13108041172056875109143

theorem tailTrace_1550815 : CollatzResearch.WordTrace tailWord_1550815 prefixEnd_1550815 13108041172056875109143 := by
  unfold tailWord_1550815
  simp only [CollatzResearch.WordTrace]
  refine ⟨56562869876669587960677899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37708579917779725307118599 56562869876669587960677899)
  ·
    refine ⟨84844304815004381941016849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56562869876669587960677899 84844304815004381941016849)
    ·
      refine ⟨63633228611253286455762637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84844304815004381941016849 63633228611253286455762637)
      ·
        refine ⟨23862460729219982420910989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63633228611253286455762637 23862460729219982420910989)
        ·
          refine ⟨8948422773457493407841621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23862460729219982420910989 8948422773457493407841621)
          ·
            refine ⟨13108041172056875109143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8948422773457493407841621 13108041172056875109143)
            ·
              rfl

theorem cell21_1550815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 11].length) (baseStart_1550815 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1550815 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1550815 prefixEnd_1550815 := by exact prefixLift 1550815
  have htrace : WordTrace (prefixWord ++ tailWord_1550815) baseStart_1550815 baseEnd_1550815 := by
    simpa [prefixWord, tailWord_1550815, baseEnd_1550815] using wordTrace_append hprefix tailTrace_1550815
  have hstable : (prefixWord ++ tailWord_1550815).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550815).length < 2 ^ (prefixWord ++ tailWord_1550815).sum := by decide
  have hdescent : baseEnd_1550815 < baseStart_1550815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550821 : List Nat := [1, 3, 1, 5, 2, 1, 1, 4, 3]
def baseStart_1550821 : Nat := 118140960795 + 1550821 * 2 ^ 59
def prefixEnd_1550821 : Nat := 4983230072969 + 3 ^ 40 * 1550821 * 2
def baseEnd_1550821 : Nat := 353918480927280950846849

theorem tailTrace_1550821 : CollatzResearch.WordTrace tailWord_1550821 prefixEnd_1550821 353918480927280950846849 := by
  unfold tailWord_1550821
  simp only [CollatzResearch.WordTrace]
  refine ⟨56563088714647850985396317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37708725809765233990264211 56563088714647850985396317)
  ·
    refine ⟨21211158267992944119523619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56563088714647850985396317 21211158267992944119523619)
    ·
      refine ⟨31816737401989416179285429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21211158267992944119523619 31816737401989416179285429)
      ·
        refine ⟨2982819131436507766808009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31816737401989416179285429 2982819131436507766808009)
        ·
          refine ⟨2237114348577380825106007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2982819131436507766808009 2237114348577380825106007)
          ·
            refine ⟨3355671522866071237659011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2237114348577380825106007 3355671522866071237659011)
            ·
              refine ⟨5033507284299106856488517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3355671522866071237659011 5033507284299106856488517)
              ·
                refine ⟨943782615806082535591597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5033507284299106856488517 943782615806082535591597)
                ·
                  refine ⟨353918480927280950846849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 943782615806082535591597 353918480927280950846849)
                  ·
                    rfl

theorem cell21_1550821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 4, 3].length) (baseStart_1550821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1550821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1550821 prefixEnd_1550821 := by exact prefixLift 1550821
  have htrace : WordTrace (prefixWord ++ tailWord_1550821) baseStart_1550821 baseEnd_1550821 := by
    simpa [prefixWord, tailWord_1550821, baseEnd_1550821] using wordTrace_append hprefix tailTrace_1550821
  have hstable : (prefixWord ++ tailWord_1550821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550821).length < 2 ^ (prefixWord ++ tailWord_1550821).sum := by decide
  have hdescent : baseEnd_1550821 < baseStart_1550821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550849 : List Nat := [1, 2, 4, 1, 3, 2, 3, 5]
def baseStart_1550849 : Nat := 118140960795 + 1550849 * 2 ^ 59
def prefixEnd_1550849 : Nat := 4983230072969 + 3 ^ 40 * 1550849 * 2
def baseEnd_1550849 : Nat := 117974956969586374793375

theorem tailTrace_1550849 : CollatzResearch.WordTrace tailWord_1550849 prefixEnd_1550849 117974956969586374793375 := by
  unfold tailWord_1550849
  simp only [CollatzResearch.WordTrace]
  refine ⟨56564109958546411767415601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37709406639030941178277067 56564109958546411767415601)
  ·
    refine ⟨42423082468909808825561701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56564109958546411767415601 42423082468909808825561701)
    ·
      refine ⟨7954327962920589154792819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42423082468909808825561701 7954327962920589154792819)
      ·
        refine ⟨11931491944380883732189229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7954327962920589154792819 11931491944380883732189229)
        ·
          refine ⟨4474309479142831399570961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11931491944380883732189229 4474309479142831399570961)
          ·
            refine ⟨3355732109357123549678221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4474309479142831399570961 3355732109357123549678221)
            ·
              refine ⟨1258399541008921331129333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3355732109357123549678221 1258399541008921331129333)
              ·
                refine ⟨117974956969586374793375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1258399541008921331129333 117974956969586374793375)
                ·
                  rfl

theorem cell21_1550849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 5].length) (baseStart_1550849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1550849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1550849 prefixEnd_1550849 := by exact prefixLift 1550849
  have htrace : WordTrace (prefixWord ++ tailWord_1550849) baseStart_1550849 baseEnd_1550849 := by
    simpa [prefixWord, tailWord_1550849, baseEnd_1550849] using wordTrace_append hprefix tailTrace_1550849
  have hstable : (prefixWord ++ tailWord_1550849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550849).length < 2 ^ (prefixWord ++ tailWord_1550849).sum := by decide
  have hdescent : baseEnd_1550849 < baseStart_1550849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550863 : List Nat := [1, 1, 2, 1, 1, 1, 2, 9, 3]
def baseStart_1550863 : Nat := 118140960795 + 1550863 * 2 ^ 59
def prefixEnd_1550863 : Nat := 4983230072969 + 3 ^ 40 * 1550863 * 2
def baseEnd_1550863 : Nat := 353928065899498211146763

theorem tailTrace_1550863 : CollatzResearch.WordTrace tailWord_1550863 prefixEnd_1550863 353928065899498211146763 := by
  unfold tailWord_1550863
  simp only [CollatzResearch.WordTrace]
  refine ⟨56564620580495692158425243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37709747053663794772283495 56564620580495692158425243)
  ·
    refine ⟨84846930870743538237637865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56564620580495692158425243 84846930870743538237637865)
    ·
      refine ⟨63635198153057653678228399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84846930870743538237637865 63635198153057653678228399)
      ·
        refine ⟨95452797229586480517342599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63635198153057653678228399 95452797229586480517342599)
        ·
          refine ⟨143179195844379720776013899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95452797229586480517342599 143179195844379720776013899)
          ·
            refine ⟨214768793766569581164020849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143179195844379720776013899 214768793766569581164020849)
            ·
              refine ⟨161076595324927185873015637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214768793766569581164020849 161076595324927185873015637)
              ·
                refine ⟨943808175731995229724701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 161076595324927185873015637 943808175731995229724701)
                ·
                  refine ⟨353928065899498211146763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 943808175731995229724701 353928065899498211146763)
                  ·
                    rfl

theorem cell21_1550863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 9, 3].length) (baseStart_1550863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1550863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1550863 prefixEnd_1550863 := by exact prefixLift 1550863
  have htrace : WordTrace (prefixWord ++ tailWord_1550863) baseStart_1550863 baseEnd_1550863 := by
    simpa [prefixWord, tailWord_1550863, baseEnd_1550863] using wordTrace_append hprefix tailTrace_1550863
  have hstable : (prefixWord ++ tailWord_1550863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550863).length < 2 ^ (prefixWord ++ tailWord_1550863).sum := by decide
  have hdescent : baseEnd_1550863 < baseStart_1550863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550880 : List Nat := [2, 1, 1, 6, 2, 1, 2, 1, 5]
def baseStart_1550880 : Nat := 118140960795 + 1550880 * 2 ^ 59
def prefixEnd_1550880 : Nat := 4983230072969 + 3 ^ 40 * 1550880 * 2
def baseEnd_1550880 : Nat := 353931945531109959363395

theorem tailTrace_1550880 : CollatzResearch.WordTrace tailWord_1550880 prefixEnd_1550880 353931945531109959363395 := by
  unfold tailWord_1550880
  simp only [CollatzResearch.WordTrace]
  refine ⟨28282620310717052030897047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37710160414289402707862729 28282620310717052030897047)
  ·
    refine ⟨42423930466075578046345571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28282620310717052030897047 42423930466075578046345571)
    ·
      refine ⟨63635895699113367069518357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42423930466075578046345571 63635895699113367069518357)
      ·
        refine ⟨2982932610895939081383673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 63635895699113367069518357 2982932610895939081383673)
        ·
          refine ⟨2237199458171954311037755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2982932610895939081383673 2237199458171954311037755)
          ·
            refine ⟨3355799187257931466556633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2237199458171954311037755 3355799187257931466556633)
            ·
              refine ⟨2516849390443448599917475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3355799187257931466556633 2516849390443448599917475)
              ·
                refine ⟨3775274085665172899876213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2516849390443448599917475 3775274085665172899876213)
                ·
                  refine ⟨353931945531109959363395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3775274085665172899876213 353931945531109959363395)
                  ·
                    rfl

theorem cell21_1550880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 5].length) (baseStart_1550880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1550880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1550880 prefixEnd_1550880 := by exact prefixLift 1550880
  have htrace : WordTrace (prefixWord ++ tailWord_1550880) baseStart_1550880 baseEnd_1550880 := by
    simpa [prefixWord, tailWord_1550880, baseEnd_1550880] using wordTrace_append hprefix tailTrace_1550880
  have hstable : (prefixWord ++ tailWord_1550880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550880).length < 2 ^ (prefixWord ++ tailWord_1550880).sum := by decide
  have hdescent : baseEnd_1550880 < baseStart_1550880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550900 : List Nat := [2, 5, 1, 3, 2, 1, 2, 5]
def baseStart_1550900 : Nat := 118140960795 + 1550900 * 2 ^ 59
def prefixEnd_1550900 : Nat := 4983230072969 + 3 ^ 40 * 1550900 * 2
def baseEnd_1550900 : Nat := 117978836601198123010007

theorem tailTrace_1550900 : CollatzResearch.WordTrace tailWord_1550900 prefixEnd_1550900 117978836601198123010007 := by
  unfold tailWord_1550900
  simp only [CollatzResearch.WordTrace]
  refine ⟨28282985040680823738761077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37710646720907764985014769 28282985040680823738761077)
  ·
    refine ⟨2651529847563827225508851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28282985040680823738761077 2651529847563827225508851)
    ·
      refine ⟨3977294771345740838263277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2651529847563827225508851 3977294771345740838263277)
      ·
        refine ⟨1491485539254652814348729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3977294771345740838263277 1491485539254652814348729)
        ·
          refine ⟨1118614154440989610761547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1491485539254652814348729 1118614154440989610761547)
          ·
            refine ⟨1677921231661484416142321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1118614154440989610761547 1677921231661484416142321)
            ·
              refine ⟨1258440923746113312106741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1677921231661484416142321 1258440923746113312106741)
              ·
                refine ⟨117978836601198123010007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1258440923746113312106741 117978836601198123010007)
                ·
                  rfl

theorem cell21_1550900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 5].length) (baseStart_1550900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1550900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1550900 prefixEnd_1550900 := by exact prefixLift 1550900
  have htrace : WordTrace (prefixWord ++ tailWord_1550900) baseStart_1550900 baseEnd_1550900 := by
    simpa [prefixWord, tailWord_1550900, baseEnd_1550900] using wordTrace_append hprefix tailTrace_1550900
  have hstable : (prefixWord ++ tailWord_1550900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550900).length < 2 ^ (prefixWord ++ tailWord_1550900).sum := by decide
  have hdescent : baseEnd_1550900 < baseStart_1550900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550908 : List Nat := [2, 2, 2, 2, 3, 2, 1, 7]
def baseStart_1550908 : Nat := 118140960795 + 1550908 * 2 ^ 59
def prefixEnd_1550908 : Nat := 4983230072969 + 3 ^ 40 * 1550908 * 2
def baseEnd_1550908 : Nat := 117979445170862710965557

theorem tailTrace_1550908 : CollatzResearch.WordTrace tailWord_1550908 prefixEnd_1550908 117979445170862710965557 := by
  unfold tailWord_1550908
  simp only [CollatzResearch.WordTrace]
  refine ⟨28283130932666332421906689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37710841243555109895875585 28283130932666332421906689)
  ·
    refine ⟨21212348199499749316430017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28283130932666332421906689 21212348199499749316430017)
    ·
      refine ⟨15909261149624811987322513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21212348199499749316430017 15909261149624811987322513)
      ·
        refine ⟨11931945862218608990491885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15909261149624811987322513 11931945862218608990491885)
        ·
          refine ⟨4474479698331978371434457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11931945862218608990491885 4474479698331978371434457)
          ·
            refine ⟨3355859773748983778575843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4474479698331978371434457 3355859773748983778575843)
            ·
              refine ⟨5033789660623475667863765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3355859773748983778575843 5033789660623475667863765)
              ·
                refine ⟨117979445170862710965557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5033789660623475667863765 117979445170862710965557)
                ·
                  rfl

theorem cell21_1550908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 7].length) (baseStart_1550908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1550908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1550908 prefixEnd_1550908 := by exact prefixLift 1550908
  have htrace : WordTrace (prefixWord ++ tailWord_1550908) baseStart_1550908 baseEnd_1550908 := by
    simpa [prefixWord, tailWord_1550908, baseEnd_1550908] using wordTrace_append hprefix tailTrace_1550908
  have hstable : (prefixWord ++ tailWord_1550908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550908).length < 2 ^ (prefixWord ++ tailWord_1550908).sum := by decide
  have hdescent : baseEnd_1550908 < baseStart_1550908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550925 : List Nat := [1, 6, 1, 1, 2, 3, 7]
def baseStart_1550925 : Nat := 118140960795 + 1550925 * 2 ^ 59
def prefixEnd_1550925 : Nat := 4983230072969 + 3 ^ 40 * 1550925 * 2
def baseEnd_1550925 : Nat := 39326912793799986790367

theorem tailTrace_1550925 : CollatzResearch.WordTrace tailWord_1550925 prefixEnd_1550925 39326912793799986790367 := by
  unfold tailWord_1550925
  simp only [CollatzResearch.WordTrace]
  refine ⟨56566881906271076747182229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37711254604180717831454819 56566881906271076747182229)
  ·
    refine ⟨2651572589356456722524167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 56566881906271076747182229 2651572589356456722524167)
    ·
      refine ⟨3977358884034685083786251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2651572589356456722524167 3977358884034685083786251)
      ·
        refine ⟨5966038326052027625679377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3977358884034685083786251 5966038326052027625679377)
        ·
          refine ⟨4474528744539020719259533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5966038326052027625679377 4474528744539020719259533)
          ·
            refine ⟨1677948279202132769722325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4474528744539020719259533 1677948279202132769722325)
            ·
              refine ⟨39326912793799986790367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1677948279202132769722325 39326912793799986790367)
              ·
                rfl

theorem cell21_1550925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 7].length) (baseStart_1550925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1550925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1550925 prefixEnd_1550925 := by exact prefixLift 1550925
  have htrace : WordTrace (prefixWord ++ tailWord_1550925) baseStart_1550925 baseEnd_1550925 := by
    simpa [prefixWord, tailWord_1550925, baseEnd_1550925] using wordTrace_append hprefix tailTrace_1550925
  have hstable : (prefixWord ++ tailWord_1550925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550925).length < 2 ^ (prefixWord ++ tailWord_1550925).sum := by decide
  have hdescent : baseEnd_1550925 < baseStart_1550925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550967 : List Nat := [1, 1, 3, 1, 1, 3, 4, 7]
def baseStart_1550967 : Nat := 118140960795 + 1550967 * 2 ^ 59
def prefixEnd_1550967 : Nat := 4983230072969 + 3 ^ 40 * 1550967 * 2
def baseEnd_1550967 : Nat := 117983933372139047137739

theorem tailTrace_1550967 : CollatzResearch.WordTrace tailWord_1550967 prefixEnd_1550967 117983933372139047137739 := by
  unfold tailWord_1550967
  simp only [CollatzResearch.WordTrace]
  refine ⟨56568413772118917920211155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37712275848079278613474103 56568413772118917920211155)
  ·
    refine ⟨84852620658178376880316733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56568413772118917920211155 84852620658178376880316733)
    ·
      refine ⟨31819732746816891330118775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84852620658178376880316733 31819732746816891330118775)
      ·
        refine ⟨47729599120225336995178163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31819732746816891330118775 47729599120225336995178163)
        ·
          refine ⟨71594398680338005492767245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47729599120225336995178163 71594398680338005492767245)
          ·
            refine ⟨26847899505126752059787717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71594398680338005492767245 26847899505126752059787717)
            ·
              refine ⟨5033981157211266011210197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26847899505126752059787717 5033981157211266011210197)
              ·
                refine ⟨117983933372139047137739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5033981157211266011210197 117983933372139047137739)
                ·
                  rfl

theorem cell21_1550967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 7].length) (baseStart_1550967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1550967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1550967 prefixEnd_1550967 := by exact prefixLift 1550967
  have htrace : WordTrace (prefixWord ++ tailWord_1550967) baseStart_1550967 baseEnd_1550967 := by
    simpa [prefixWord, tailWord_1550967, baseEnd_1550967] using wordTrace_append hprefix tailTrace_1550967
  have hstable : (prefixWord ++ tailWord_1550967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550967).length < 2 ^ (prefixWord ++ tailWord_1550967).sum := by decide
  have hdescent : baseEnd_1550967 < baseStart_1550967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551077 : List Nat := [1, 3, 1, 4, 1, 4, 2, 5]
def baseStart_1551077 : Nat := 118140960795 + 1551077 * 2 ^ 59
def prefixEnd_1551077 : Nat := 4983230072969 + 3 ^ 40 * 1551077 * 2
def baseEnd_1551077 : Nat := 117992301205027131526553

theorem tailTrace_1551077 : CollatzResearch.WordTrace tailWord_1551077 prefixEnd_1551077 117992301205027131526553 := by
  unfold tailWord_1551077
  simp only [CollatzResearch.WordTrace]
  refine ⟨56572425801720406706715485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37714950534480271137810323 56572425801720406706715485)
  ·
    refine ⟨21214659675645152515018307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56572425801720406706715485 21214659675645152515018307)
    ·
      refine ⟨31821989513467728772527461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21214659675645152515018307 31821989513467728772527461)
      ·
        refine ⟨5966623033775199144848899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31821989513467728772527461 5966623033775199144848899)
        ·
          refine ⟨8949934550662798717273349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5966623033775199144848899 8949934550662798717273349)
          ·
            refine ⟨1678112728249274759488753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8949934550662798717273349 1678112728249274759488753)
            ·
              refine ⟨1258584546186956069616565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1678112728249274759488753 1258584546186956069616565)
              ·
                refine ⟨117992301205027131526553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1258584546186956069616565 117992301205027131526553)
                ·
                  rfl

theorem cell21_1551077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 5].length) (baseStart_1551077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1551077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1551077 prefixEnd_1551077 := by exact prefixLift 1551077
  have htrace : WordTrace (prefixWord ++ tailWord_1551077) baseStart_1551077 baseEnd_1551077 := by
    simpa [prefixWord, tailWord_1551077, baseEnd_1551077] using wordTrace_append hprefix tailTrace_1551077
  have hstable : (prefixWord ++ tailWord_1551077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551077).length < 2 ^ (prefixWord ++ tailWord_1551077).sum := by decide
  have hdescent : baseEnd_1551077 < baseStart_1551077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551088 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 8]
def baseStart_1551088 : Nat := 118140960795 + 1551088 * 2 ^ 59
def prefixEnd_1551088 : Nat := 4983230072969 + 3 ^ 40 * 1551088 * 2
def baseEnd_1551088 : Nat := 353979413964947819896303

theorem tailTrace_1551088 : CollatzResearch.WordTrace tailWord_1551088 prefixEnd_1551088 353979413964947819896303 := by
  unfold tailWord_1551088
  simp only [CollatzResearch.WordTrace]
  refine ⟨28286413502340277792682959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37715218003120370390243945 28286413502340277792682959)
  ·
    refine ⟨42429620253510416689024439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28286413502340277792682959 42429620253510416689024439)
    ·
      refine ⟨63644430380265625033536659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42429620253510416689024439 63644430380265625033536659)
      ·
        refine ⟨95466645570398437550304989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63644430380265625033536659 95466645570398437550304989)
        ·
          refine ⟨35799992088899414081364371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95466645570398437550304989 35799992088899414081364371)
          ·
            refine ⟨53699988133349121122046557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35799992088899414081364371 53699988133349121122046557)
            ·
              refine ⟨20137495550005920420767459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53699988133349121122046557 20137495550005920420767459)
              ·
                refine ⟨30206243325008880631151189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20137495550005920420767459 30206243325008880631151189)
                ·
                  refine ⟨353979413964947819896303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30206243325008880631151189 353979413964947819896303)
                  ·
                    rfl

theorem cell21_1551088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 8].length) (baseStart_1551088 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1551088 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1551088 prefixEnd_1551088 := by exact prefixLift 1551088
  have htrace : WordTrace (prefixWord ++ tailWord_1551088) baseStart_1551088 baseEnd_1551088 := by
    simpa [prefixWord, tailWord_1551088, baseEnd_1551088] using wordTrace_append hprefix tailTrace_1551088
  have hstable : (prefixWord ++ tailWord_1551088).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551088).length < 2 ^ (prefixWord ++ tailWord_1551088).sum := by decide
  have hdescent : baseEnd_1551088 < baseStart_1551088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551105 : List Nat := [1, 2, 4, 1, 1, 1, 1, 6, 4]
def baseStart_1551105 : Nat := 118140960795 + 1551105 * 2 ^ 59
def prefixEnd_1551105 : Nat := 4983230072969 + 3 ^ 40 * 1551105 * 2
def baseEnd_1551105 : Nat := 353983293596559568112935

theorem tailTrace_1551105 : CollatzResearch.WordTrace tailWord_1551105 prefixEnd_1551105 353983293596559568112935 := by
  unfold tailWord_1551105
  simp only [CollatzResearch.WordTrace]
  refine ⟨56573447045618967488734769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37715631363745978325823179 56573447045618967488734769)
  ·
    refine ⟨42430085284214225616551077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56573447045618967488734769 42430085284214225616551077)
    ·
      refine ⟨7955640990790167303103327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42430085284214225616551077 7955640990790167303103327)
      ·
        refine ⟨11933461486185250954654991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7955640990790167303103327 11933461486185250954654991)
        ·
          refine ⟨17900192229277876431982487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11933461486185250954654991 17900192229277876431982487)
          ·
            refine ⟨26850288343916814647973731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17900192229277876431982487 26850288343916814647973731)
            ·
              refine ⟨40275432515875221971960597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26850288343916814647973731 40275432515875221971960597)
              ·
                refine ⟨1887910899181651029935653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40275432515875221971960597 1887910899181651029935653)
                ·
                  refine ⟨353983293596559568112935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1887910899181651029935653 353983293596559568112935)
                  ·
                    rfl

theorem cell21_1551105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6, 4].length) (baseStart_1551105 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1551105 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1551105 prefixEnd_1551105 := by exact prefixLift 1551105
  have htrace : WordTrace (prefixWord ++ tailWord_1551105) baseStart_1551105 baseEnd_1551105 := by
    simpa [prefixWord, tailWord_1551105, baseEnd_1551105] using wordTrace_append hprefix tailTrace_1551105
  have hstable : (prefixWord ++ tailWord_1551105).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551105).length < 2 ^ (prefixWord ++ tailWord_1551105).sum := by decide
  have hdescent : baseEnd_1551105 < baseStart_1551105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551119 : List Nat := [1, 1, 2, 1, 1, 1, 8, 6]
def baseStart_1551119 : Nat := 118140960795 + 1551119 * 2 ^ 59
def prefixEnd_1551119 : Nat := 4983230072969 + 3 ^ 40 * 1551119 * 2
def baseEnd_1551119 : Nat := 117995496195766218293191

theorem tailTrace_1551119 : CollatzResearch.WordTrace tailWord_1551119 prefixEnd_1551119 117995496195766218293191 := by
  unfold tailWord_1551119
  simp only [CollatzResearch.WordTrace]
  refine ⟨56573957667568247879744411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37715971778378831919829607 56573957667568247879744411)
  ·
    refine ⟨84860936501352371819616617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56573957667568247879744411 84860936501352371819616617)
    ·
      refine ⟨63645702376014278864712463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84860936501352371819616617 63645702376014278864712463)
      ·
        refine ⟨95468553564021418297068695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63645702376014278864712463 95468553564021418297068695)
        ·
          refine ⟨143202830346032127445603043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95468553564021418297068695 143202830346032127445603043)
          ·
            refine ⟨214804245519048191168404565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143202830346032127445603043 214804245519048191168404565)
            ·
              refine ⟨2517237252176345990254741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 214804245519048191168404565 2517237252176345990254741)
              ·
                refine ⟨117995496195766218293191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2517237252176345990254741 117995496195766218293191)
                ·
                  rfl

theorem cell21_1551119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 6].length) (baseStart_1551119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1551119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1551119 prefixEnd_1551119 := by exact prefixLift 1551119
  have htrace : WordTrace (prefixWord ++ tailWord_1551119) baseStart_1551119 baseEnd_1551119 := by
    simpa [prefixWord, tailWord_1551119, baseEnd_1551119] using wordTrace_append hprefix tailTrace_1551119
  have hstable : (prefixWord ++ tailWord_1551119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551119).length < 2 ^ (prefixWord ++ tailWord_1551119).sum := by decide
  have hdescent : baseEnd_1551119 < baseStart_1551119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551277 : List Nat := [1, 5, 2, 3, 1, 2, 1, 1, 5]
def baseStart_1551277 : Nat := 118140960795 + 1551277 * 2 ^ 59
def prefixEnd_1551277 : Nat := 4983230072969 + 3 ^ 40 * 1551277 * 2
def baseEnd_1551277 : Nat := 354022546339925491245917

theorem tailTrace_1551277 : CollatzResearch.WordTrace tailWord_1551277 prefixEnd_1551277 354022546339925491245917 := by
  unfold tailWord_1551277
  simp only [CollatzResearch.WordTrace]
  refine ⟨56579720400995840863996085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37719813600663893909330723 56579720400995840863996085)
  ·
    refine ⟨5304348787593360080999633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56579720400995840863996085 5304348787593360080999633)
    ·
      refine ⟨3978261590695020060749725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5304348787593360080999633 3978261590695020060749725)
      ·
        refine ⟨1491848096510632522781147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3978261590695020060749725 1491848096510632522781147)
        ·
          refine ⟨2237772144765948784171721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1491848096510632522781147 2237772144765948784171721)
          ·
            refine ⟨1678329108574461588128791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2237772144765948784171721 1678329108574461588128791)
            ·
              refine ⟨2517493662861692382193187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1678329108574461588128791 2517493662861692382193187)
              ·
                refine ⟨3776240494292538573289781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2517493662861692382193187 3776240494292538573289781)
                ·
                  refine ⟨354022546339925491245917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3776240494292538573289781 354022546339925491245917)
                  ·
                    rfl

theorem cell21_1551277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_1551277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1551277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1551277 prefixEnd_1551277 := by exact prefixLift 1551277
  have htrace : WordTrace (prefixWord ++ tailWord_1551277) baseStart_1551277 baseEnd_1551277 := by
    simpa [prefixWord, tailWord_1551277, baseEnd_1551277] using wordTrace_append hprefix tailTrace_1551277
  have hstable : (prefixWord ++ tailWord_1551277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551277).length < 2 ^ (prefixWord ++ tailWord_1551277).sum := by decide
  have hdescent : baseEnd_1551277 < baseStart_1551277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551336 : List Nat := [2, 1, 4, 1, 1, 1, 6, 2, 3]
def baseStart_1551336 : Nat := 118140960795 + 1551336 * 2 ^ 59
def prefixEnd_1551336 : Nat := 4983230072969 + 3 ^ 40 * 1551336 * 2
def baseEnd_1551336 : Nat := 354036010943754499762463

theorem tailTrace_1551336 : CollatzResearch.WordTrace tailWord_1551336 prefixEnd_1551336 354036010943754499762463 := by
  unfold tailWord_1551336
  simp only [CollatzResearch.WordTrace]
  refine ⟨28290936153891046970196931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37721248205188062626929241 28290936153891046970196931)
  ·
    refine ⟨42436404230836570455295397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28290936153891046970196931 42436404230836570455295397)
    ·
      refine ⟨7956825793281856960367887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42436404230836570455295397 7956825793281856960367887)
      ·
        refine ⟨11935238689922785440551831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7956825793281856960367887 11935238689922785440551831)
        ·
          refine ⟨17902858034884178160827747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11935238689922785440551831 17902858034884178160827747)
          ·
            refine ⟨26854287052326267241241621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17902858034884178160827747 26854287052326267241241621)
            ·
              refine ⟨1258794705577793776933201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26854287052326267241241621 1258794705577793776933201)
              ·
                refine ⟨944096029183345332699901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1258794705577793776933201 944096029183345332699901)
                ·
                  refine ⟨354036010943754499762463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 944096029183345332699901 354036010943754499762463)
                  ·
                    rfl

theorem cell21_1551336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 2, 3].length) (baseStart_1551336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1551336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1551336 prefixEnd_1551336 := by exact prefixLift 1551336
  have htrace : WordTrace (prefixWord ++ tailWord_1551336) baseStart_1551336 baseEnd_1551336 := by
    simpa [prefixWord, tailWord_1551336, baseEnd_1551336] using wordTrace_append hprefix tailTrace_1551336
  have hstable : (prefixWord ++ tailWord_1551336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551336).length < 2 ^ (prefixWord ++ tailWord_1551336).sum := by decide
  have hdescent : baseEnd_1551336 < baseStart_1551336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551350 : List Nat := [5, 1, 1, 1, 3, 1, 2, 3, 4]
def baseStart_1551350 : Nat := 118140960795 + 1551350 * 2 ^ 59
def prefixEnd_1551350 : Nat := 4983230072969 + 3 ^ 40 * 1551350 * 2
def baseEnd_1551350 : Nat := 354039205934493586529101

theorem tailTrace_1551350 : CollatzResearch.WordTrace tailWord_1551350 prefixEnd_1551350 354039205934493586529101 := by
  unfold tailWord_1551350
  simp only [CollatzResearch.WordTrace]
  refine ⟨3536398933108210895712719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37721588619820916220935669 3536398933108210895712719)
  ·
    refine ⟨5304598399662316343569079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3536398933108210895712719 5304598399662316343569079)
    ·
      refine ⟨7956897599493474515353619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5304598399662316343569079 7956897599493474515353619)
      ·
        refine ⟨11935346399240211773030429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7956897599493474515353619 11935346399240211773030429)
        ·
          refine ⟨4475754899715079414886411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11935346399240211773030429 4475754899715079414886411)
          ·
            refine ⟨6713632349572619122329617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4475754899715079414886411 6713632349572619122329617)
            ·
              refine ⟨5035224262179464341747213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6713632349572619122329617 5035224262179464341747213)
              ·
                refine ⟨1888209098317299128155205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5035224262179464341747213 1888209098317299128155205)
                ·
                  refine ⟨354039205934493586529101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1888209098317299128155205 354039205934493586529101)
                  ·
                    rfl

theorem cell21_1551350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_1551350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1551350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1551350 prefixEnd_1551350 := by exact prefixLift 1551350
  have htrace : WordTrace (prefixWord ++ tailWord_1551350) baseStart_1551350 baseEnd_1551350 := by
    simpa [prefixWord, tailWord_1551350, baseEnd_1551350] using wordTrace_append hprefix tailTrace_1551350
  have hstable : (prefixWord ++ tailWord_1551350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551350).length < 2 ^ (prefixWord ++ tailWord_1551350).sum := by decide
  have hdescent : baseEnd_1551350 < baseStart_1551350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551395 : List Nat := [1, 1, 1, 4, 3, 2, 2, 4, 3]
def baseStart_1551395 : Nat := 118140960795 + 1551395 * 2 ^ 59
def prefixEnd_1551395 : Nat := 4983230072969 + 3 ^ 40 * 1551395 * 2
def baseEnd_1551395 : Nat := 354049475547583508279009

theorem tailTrace_1551395 : CollatzResearch.WordTrace tailWord_1551395 prefixEnd_1551395 354049475547583508279009 := by
  unfold tailWord_1551395
  simp only [CollatzResearch.WordTrace]
  refine ⟨56584024214568347016791639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37722682809712231344527759 56584024214568347016791639)
  ·
    refine ⟨84876036321852520525187459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56584024214568347016791639 84876036321852520525187459)
    ·
      refine ⟨127314054482778780787781189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84876036321852520525187459 127314054482778780787781189)
      ·
        refine ⟨23871385215521021397708973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127314054482778780787781189 23871385215521021397708973)
        ·
          refine ⟨8951769455820383024140865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23871385215521021397708973 8951769455820383024140865)
          ·
            refine ⟨6713827091865287268105649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8951769455820383024140865 6713827091865287268105649)
            ·
              refine ⟨5035370318898965451079237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6713827091865287268105649 5035370318898965451079237)
              ·
                refine ⟨944131934793556022077357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5035370318898965451079237 944131934793556022077357)
                ·
                  refine ⟨354049475547583508279009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 944131934793556022077357 354049475547583508279009)
                  ·
                    rfl

theorem cell21_1551395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 4, 3].length) (baseStart_1551395 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1551395 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1551395 prefixEnd_1551395 := by exact prefixLift 1551395
  have htrace : WordTrace (prefixWord ++ tailWord_1551395) baseStart_1551395 baseEnd_1551395 := by
    simpa [prefixWord, tailWord_1551395, baseEnd_1551395] using wordTrace_append hprefix tailTrace_1551395
  have hstable : (prefixWord ++ tailWord_1551395).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551395).length < 2 ^ (prefixWord ++ tailWord_1551395).sum := by decide
  have hdescent : baseEnd_1551395 < baseStart_1551395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551446 : List Nat := [5, 2, 2, 1, 3, 1, 1, 1, 5]
def baseStart_1551446 : Nat := 118140960795 + 1551446 * 2 ^ 59
def prefixEnd_1551446 : Nat := 4983230072969 + 3 ^ 40 * 1551446 * 2
def baseEnd_1551446 : Nat := 354061114442418752928905

theorem tailTrace_1551446 : CollatzResearch.WordTrace tailWord_1551446 prefixEnd_1551446 354061114442418752928905 := by
  unfold tailWord_1551446
  simp only [CollatzResearch.WordTrace]
  refine ⟨3536617771086473920431137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37723922891589055151265461 3536617771086473920431137)
  ·
    refine ⟨2652463328314855440323353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3536617771086473920431137 2652463328314855440323353)
    ·
      refine ⟨1989347496236141580242515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2652463328314855440323353 1989347496236141580242515)
      ·
        refine ⟨2984021244354212370363773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1989347496236141580242515 2984021244354212370363773)
        ·
          refine ⟨1119007966632829638886415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2984021244354212370363773 1119007966632829638886415)
          ·
            refine ⟨1678511949949244458329623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1119007966632829638886415 1678511949949244458329623)
            ·
              refine ⟨2517767924923866687494435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1678511949949244458329623 2517767924923866687494435)
              ·
                refine ⟨3776651887385800031241653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2517767924923866687494435 3776651887385800031241653)
                ·
                  refine ⟨354061114442418752928905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3776651887385800031241653 354061114442418752928905)
                  ·
                    rfl

theorem cell21_1551446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_1551446 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1551446 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1551446 prefixEnd_1551446 := by exact prefixLift 1551446
  have htrace : WordTrace (prefixWord ++ tailWord_1551446) baseStart_1551446 baseEnd_1551446 := by
    simpa [prefixWord, tailWord_1551446, baseEnd_1551446] using wordTrace_append hprefix tailTrace_1551446
  have hstable : (prefixWord ++ tailWord_1551446).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551446).length < 2 ^ (prefixWord ++ tailWord_1551446).sum := by decide
  have hdescent : baseEnd_1551446 < baseStart_1551446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551502 : List Nat := [4, 1, 1, 3, 2, 2, 2, 2, 4]
def baseStart_1551502 : Nat := 118140960795 + 1551502 * 2 ^ 59
def prefixEnd_1551502 : Nat := 4983230072969 + 3 ^ 40 * 1551502 * 2
def baseEnd_1551502 : Nat := 354073894405375099995457

theorem tailTrace_1551502 : CollatzResearch.WordTrace tailWord_1551502 prefixEnd_1551502 354073894405375099995457 := by
  unfold tailWord_1551502
  simp only [CollatzResearch.WordTrace]
  refine ⟨7073490853147588036367095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37725284550120469527291173 7073490853147588036367095)
  ·
    refine ⟨10610236279721382054550643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7073490853147588036367095 10610236279721382054550643)
    ·
      refine ⟨15915354419582073081825965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10610236279721382054550643 15915354419582073081825965)
      ·
        refine ⟨5968257907343277405684737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15915354419582073081825965 5968257907343277405684737)
        ·
          refine ⟨4476193430507458054263553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5968257907343277405684737 4476193430507458054263553)
          ·
            refine ⟨3357145072880593540697665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4476193430507458054263553 3357145072880593540697665)
            ·
              refine ⟨2517858804660445155523249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3357145072880593540697665 2517858804660445155523249)
              ·
                refine ⟨1888394103495333866642437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2517858804660445155523249 1888394103495333866642437)
                ·
                  refine ⟨354073894405375099995457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1888394103495333866642437 354073894405375099995457)
                  ·
                    rfl

theorem cell21_1551502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_1551502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1551502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1551502 prefixEnd_1551502 := by exact prefixLift 1551502
  have htrace : WordTrace (prefixWord ++ tailWord_1551502) baseStart_1551502 baseEnd_1551502 := by
    simpa [prefixWord, tailWord_1551502, baseEnd_1551502] using wordTrace_append hprefix tailTrace_1551502
  have hstable : (prefixWord ++ tailWord_1551502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551502).length < 2 ^ (prefixWord ++ tailWord_1551502).sum := by decide
  have hdescent : baseEnd_1551502 < baseStart_1551502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551516 : List Nat := [2, 2, 3, 2, 1, 4, 1, 6]
def baseStart_1551516 : Nat := 118140960795 + 1551516 * 2 ^ 59
def prefixEnd_1551516 : Nat := 4983230072969 + 3 ^ 40 * 1551516 * 2
def baseEnd_1551516 : Nat := 118025696465371395587365

theorem tailTrace_1551516 : CollatzResearch.WordTrace tailWord_1551516 prefixEnd_1551516 118025696465371395587365 := by
  unfold tailWord_1551516
  simp only [CollatzResearch.WordTrace]
  refine ⟨28294218723564992340973201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37725624964753323121297601 28294218723564992340973201)
  ·
    refine ⟨21220664042673744255729901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28294218723564992340973201 21220664042673744255729901)
    ·
      refine ⟨7957749016002654095898713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21220664042673744255729901 7957749016002654095898713)
      ·
        refine ⟨5968311762001990571924035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7957749016002654095898713 5968311762001990571924035)
        ·
          refine ⟨8952467643002985857886053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5968311762001990571924035 8952467643002985857886053)
          ·
            refine ⟨1678587683063059848353635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8952467643002985857886053 1678587683063059848353635)
            ·
              refine ⟨2517881524594589772530453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1678587683063059848353635 2517881524594589772530453)
              ·
                refine ⟨118025696465371395587365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2517881524594589772530453 118025696465371395587365)
                ·
                  rfl

theorem cell21_1551516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 6].length) (baseStart_1551516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1551516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1551516 prefixEnd_1551516 := by exact prefixLift 1551516
  have htrace : WordTrace (prefixWord ++ tailWord_1551516) baseStart_1551516 baseEnd_1551516 := by
    simpa [prefixWord, tailWord_1551516, baseEnd_1551516] using wordTrace_append hprefix tailTrace_1551516
  have hstable : (prefixWord ++ tailWord_1551516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551516).length < 2 ^ (prefixWord ++ tailWord_1551516).sum := by decide
  have hdescent : baseEnd_1551516 < baseStart_1551516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551533 : List Nat := [1, 5, 2, 1, 3, 1, 3, 5]
def baseStart_1551533 : Nat := 118140960795 + 1551533 * 2 ^ 59
def prefixEnd_1551533 : Nat := 4983230072969 + 3 ^ 40 * 1551533 * 2
def baseEnd_1551533 : Nat := 118026989675908644992909

theorem tailTrace_1551533 : CollatzResearch.WordTrace tailWord_1551533 prefixEnd_1551533 118026989675908644992909 := by
  unfold tailWord_1551533
  simp only [CollatzResearch.WordTrace]
  refine ⟨56589057488068396585315253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37726038325378931056876835 56589057488068396585315253)
  ·
    refine ⟨5305224139506412179873305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56589057488068396585315253 5305224139506412179873305)
    ·
      refine ⟨3978918104629809134904979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5305224139506412179873305 3978918104629809134904979)
      ·
        refine ⟨5968377156944713702357469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3978918104629809134904979 5968377156944713702357469)
        ·
          refine ⟨2238141433854267638384051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5968377156944713702357469 2238141433854267638384051)
          ·
            refine ⟨3357212150781401457576077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2238141433854267638384051 3357212150781401457576077)
            ·
              refine ⟨1258954556543025546591029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3357212150781401457576077 1258954556543025546591029)
              ·
                refine ⟨118026989675908644992909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1258954556543025546591029 118026989675908644992909)
                ·
                  rfl

theorem cell21_1551533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 5].length) (baseStart_1551533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1551533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1551533 prefixEnd_1551533 := by exact prefixLift 1551533
  have htrace : WordTrace (prefixWord ++ tailWord_1551533) baseStart_1551533 baseEnd_1551533 := by
    simpa [prefixWord, tailWord_1551533, baseEnd_1551533] using wordTrace_append hprefix tailTrace_1551533
  have hstable : (prefixWord ++ tailWord_1551533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551533).length < 2 ^ (prefixWord ++ tailWord_1551533).sum := by decide
  have hdescent : baseEnd_1551533 < baseStart_1551533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551696 : List Nat := [2, 1, 1, 1, 1, 5, 1, 5, 4]
def baseStart_1551696 : Nat := 118140960795 + 1551696 * 2 ^ 59
def prefixEnd_1551696 : Nat := 4983230072969 + 3 ^ 40 * 1551696 * 2
def baseEnd_1551696 : Nat := 354118167848473873761727

theorem tailTrace_1551696 : CollatzResearch.WordTrace tailWord_1551696 prefixEnd_1551696 354118167848473873761727 := by
  unfold tailWord_1551696
  simp only [CollatzResearch.WordTrace]
  refine ⟨28297501293238937711749471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37730001724318583615665961 28297501293238937711749471)
  ·
    refine ⟨42446251939858406567624207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28297501293238937711749471 42446251939858406567624207)
    ·
      refine ⟨63669377909787609851436311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42446251939858406567624207 63669377909787609851436311)
      ·
        refine ⟨95504066864681414777154467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63669377909787609851436311 95504066864681414777154467)
        ·
          refine ⟨143256100297022122165731701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95504066864681414777154467 143256100297022122165731701)
          ·
            refine ⟨13430259402845823953037347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 143256100297022122165731701 13430259402845823953037347)
            ·
              refine ⟨20145389104268735929556021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13430259402845823953037347 20145389104268735929556021)
              ·
                refine ⟨1888630228525193993395877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20145389104268735929556021 1888630228525193993395877)
                ·
                  refine ⟨354118167848473873761727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1888630228525193993395877 354118167848473873761727)
                  ·
                    rfl

theorem cell21_1551696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5, 4].length) (baseStart_1551696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1551696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1551696 prefixEnd_1551696 := by exact prefixLift 1551696
  have htrace : WordTrace (prefixWord ++ tailWord_1551696) baseStart_1551696 baseEnd_1551696 := by
    simpa [prefixWord, tailWord_1551696, baseEnd_1551696] using wordTrace_append hprefix tailTrace_1551696
  have hstable : (prefixWord ++ tailWord_1551696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551696).length < 2 ^ (prefixWord ++ tailWord_1551696).sum := by decide
  have hdescent : baseEnd_1551696 < baseStart_1551696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551775 : List Nat := [1, 1, 2, 5, 1, 2, 3, 3, 3]
def baseStart_1551775 : Nat := 118140960795 + 1551775 * 2 ^ 59
def prefixEnd_1551775 : Nat := 4983230072969 + 3 ^ 40 * 1551775 * 2
def baseEnd_1551775 : Nat := 354136196724787291944899

theorem tailTrace_1551775 : CollatzResearch.WordTrace tailWord_1551775 prefixEnd_1551775 354136196724787291944899 := by
  unfold tailWord_1551775
  simp only [CollatzResearch.WordTrace]
  refine ⟨56597883953191671915624779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37731922635461114610416519 56597883953191671915624779)
  ·
    refine ⟨84896825929787507873437169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56597883953191671915624779 84896825929787507873437169)
    ·
      refine ⟨63672619447340630905077877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84896825929787507873437169 63672619447340630905077877)
      ·
        refine ⟨5969308073188184147351051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63672619447340630905077877 5969308073188184147351051)
        ·
          refine ⟨8953962109782276221026577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5969308073188184147351051 8953962109782276221026577)
          ·
            refine ⟨6715471582336707165769933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8953962109782276221026577 6715471582336707165769933)
            ·
              refine ⟨2518301843376265187163725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6715471582336707165769933 2518301843376265187163725)
              ·
                refine ⟨944363191266099445186397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2518301843376265187163725 944363191266099445186397)
                ·
                  refine ⟨354136196724787291944899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 944363191266099445186397 354136196724787291944899)
                  ·
                    rfl

theorem cell21_1551775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 3, 3].length) (baseStart_1551775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1551775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1551775 prefixEnd_1551775 := by exact prefixLift 1551775
  have htrace : WordTrace (prefixWord ++ tailWord_1551775) baseStart_1551775 baseEnd_1551775 := by
    simpa [prefixWord, tailWord_1551775, baseEnd_1551775] using wordTrace_append hprefix tailTrace_1551775
  have hstable : (prefixWord ++ tailWord_1551775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551775).length < 2 ^ (prefixWord ++ tailWord_1551775).sum := by decide
  have hdescent : baseEnd_1551775 < baseStart_1551775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551789 : List Nat := [1, 5, 2, 2, 1, 1, 2, 1, 6]
def baseStart_1551789 : Nat := 118140960795 + 1551789 * 2 ^ 59
def prefixEnd_1551789 : Nat := 4983230072969 + 3 ^ 40 * 1551789 * 2
def baseEnd_1551789 : Nat := 354139391715526378711537

theorem tailTrace_1551789 : CollatzResearch.WordTrace tailWord_1551789 prefixEnd_1551789 354139391715526378711537 := by
  unfold tailWord_1551789
  simp only [CollatzResearch.WordTrace]
  refine ⟨56598394575140952306634421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37732263050093968204422947 56598394575140952306634421)
  ·
    refine ⟨5306099491419464278746977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56598394575140952306634421 5306099491419464278746977)
    ·
      refine ⟨3979574618564598209060233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5306099491419464278746977 3979574618564598209060233)
      ·
        refine ⟨2984680963923448656795175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3979574618564598209060233 2984680963923448656795175)
        ·
          refine ⟨4477021445885172985192763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2984680963923448656795175 4477021445885172985192763)
          ·
            refine ⟨6715532168827759477789145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4477021445885172985192763 6715532168827759477789145)
            ·
              refine ⟨5036649126620819608341859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6715532168827759477789145 5036649126620819608341859)
              ·
                refine ⟨7554973689931229412512789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5036649126620819608341859 7554973689931229412512789)
                ·
                  refine ⟨354139391715526378711537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7554973689931229412512789 354139391715526378711537)
                  ·
                    rfl

theorem cell21_1551789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_1551789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1551789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1551789 prefixEnd_1551789 := by exact prefixLift 1551789
  have htrace : WordTrace (prefixWord ++ tailWord_1551789) baseStart_1551789 baseEnd_1551789 := by
    simpa [prefixWord, tailWord_1551789, baseEnd_1551789] using wordTrace_append hprefix tailTrace_1551789
  have hstable : (prefixWord ++ tailWord_1551789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551789).length < 2 ^ (prefixWord ++ tailWord_1551789).sum := by decide
  have hdescent : baseEnd_1551789 < baseStart_1551789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551831 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 8]
def baseStart_1551831 : Nat := 118140960795 + 1551831 * 2 ^ 59
def prefixEnd_1551831 : Nat := 4983230072969 + 3 ^ 40 * 1551831 * 2
def baseEnd_1551831 : Nat := 354148976687743639011451

theorem tailTrace_1551831 : CollatzResearch.WordTrace tailWord_1551831 prefixEnd_1551831 354148976687743639011451 := by
  unfold tailWord_1551831
  simp only [CollatzResearch.WordTrace]
  refine ⟨56599926440988793479663347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37733284293992528986442231 56599926440988793479663347)
  ·
    refine ⟨84899889661483190219495021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56599926440988793479663347 84899889661483190219495021)
    ·
      refine ⟨31837458623056196332310633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84899889661483190219495021 31837458623056196332310633)
      ·
        refine ⟨23878093967292147249232975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31837458623056196332310633 23878093967292147249232975)
        ·
          refine ⟨35817140950938220873849463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23878093967292147249232975 35817140950938220873849463)
          ·
            refine ⟨53725711426407331310774195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35817140950938220873849463 53725711426407331310774195)
            ·
              refine ⟨80588567139610996966161293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53725711426407331310774195 80588567139610996966161293)
              ·
                refine ⟨30220712677354123862310485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80588567139610996966161293 30220712677354123862310485)
                ·
                  refine ⟨354148976687743639011451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30220712677354123862310485 354148976687743639011451)
                  ·
                    rfl

theorem cell21_1551831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 8].length) (baseStart_1551831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1551831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1551831 prefixEnd_1551831 := by exact prefixLift 1551831
  have htrace : WordTrace (prefixWord ++ tailWord_1551831) baseStart_1551831 baseEnd_1551831 := by
    simpa [prefixWord, tailWord_1551831, baseEnd_1551831] using wordTrace_append hprefix tailTrace_1551831
  have hstable : (prefixWord ++ tailWord_1551831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551831).length < 2 ^ (prefixWord ++ tailWord_1551831).sum := by decide
  have hdescent : baseEnd_1551831 < baseStart_1551831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552014 : List Nat := [4, 1, 1, 3, 1, 11]
def baseStart_1552014 : Nat := 118140960795 + 1552014 * 2 ^ 59
def prefixEnd_1552014 : Nat := 4983230072969 + 3 ^ 40 * 1552014 * 2
def baseEnd_1552014 : Nat := 13118175547443555091151

theorem tailTrace_1552014 : CollatzResearch.WordTrace tailWord_1552014 prefixEnd_1552014 13118175547443555091151 := by
  unfold tailWord_1552014
  simp only [CollatzResearch.WordTrace]
  refine ⟨7075825124915726966696887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37737733999550543822383397 7075825124915726966696887)
  ·
    refine ⟨10613737687373590450045331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7075825124915726966696887 10613737687373590450045331)
    ·
      refine ⟨15920606531060385675067997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10613737687373590450045331 15920606531060385675067997)
      ·
        refine ⟨5970227449147644628150499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15920606531060385675067997 5970227449147644628150499)
        ·
          refine ⟨8955341173721466942225749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5970227449147644628150499 8955341173721466942225749)
          ·
            refine ⟨13118175547443555091151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8955341173721466942225749 13118175547443555091151)
            ·
              rfl

theorem cell21_1552014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 11].length) (baseStart_1552014 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1552014 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1552014 prefixEnd_1552014 := by exact prefixLift 1552014
  have htrace : WordTrace (prefixWord ++ tailWord_1552014) baseStart_1552014 baseEnd_1552014 := by
    simpa [prefixWord, tailWord_1552014, baseEnd_1552014] using wordTrace_append hprefix tailTrace_1552014
  have hstable : (prefixWord ++ tailWord_1552014).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552014).length < 2 ^ (prefixWord ++ tailWord_1552014).sum := by decide
  have hdescent : baseEnd_1552014 < baseStart_1552014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552020 : List Nat := [2, 4, 2, 2, 2, 1, 1, 4, 3]
def baseStart_1552020 : Nat := 118140960795 + 1552020 * 2 ^ 59
def prefixEnd_1552020 : Nat := 4983230072969 + 3 ^ 40 * 1552020 * 2
def baseEnd_1552020 : Nat := 354192109062721310361065

theorem tailTrace_1552020 : CollatzResearch.WordTrace tailWord_1552020 prefixEnd_1552020 354192109062721310361065 := by
  unfold tailWord_1552020
  simp only [CollatzResearch.WordTrace]
  refine ⟨28303409918652039379146757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37737879891536052505529009 28303409918652039379146757)
  ·
    refine ⟨5306889359747257383590017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28303409918652039379146757 5306889359747257383590017)
    ·
      refine ⟨3980167019810443037692513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5306889359747257383590017 3980167019810443037692513)
      ·
        refine ⟨2985125264857832278269385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3980167019810443037692513 2985125264857832278269385)
        ·
          refine ⟨2238843948643374208702039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2985125264857832278269385 2238843948643374208702039)
          ·
            refine ⟨3358265922965061313053059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2238843948643374208702039 3358265922965061313053059)
            ·
              refine ⟨5037398884447591969579589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3358265922965061313053059 5037398884447591969579589)
              ·
                refine ⟨944512290833923494296173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5037398884447591969579589 944512290833923494296173)
                ·
                  refine ⟨354192109062721310361065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 944512290833923494296173 354192109062721310361065)
                  ·
                    rfl

theorem cell21_1552020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_1552020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1552020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1552020 prefixEnd_1552020 := by exact prefixLift 1552020
  have htrace : WordTrace (prefixWord ++ tailWord_1552020) baseStart_1552020 baseEnd_1552020 := by
    simpa [prefixWord, tailWord_1552020, baseEnd_1552020] using wordTrace_append hprefix tailTrace_1552020
  have hstable : (prefixWord ++ tailWord_1552020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552020).length < 2 ^ (prefixWord ++ tailWord_1552020).sum := by decide
  have hdescent : baseEnd_1552020 < baseStart_1552020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552138 : List Nat := [3, 1, 2, 2, 1, 5, 1, 1, 5]
def baseStart_1552138 : Nat := 118140960795 + 1552138 * 2 ^ 59
def prefixEnd_1552138 : Nat := 4983230072969 + 3 ^ 40 * 1552138 * 2
def baseEnd_1552138 : Nat := 354219038270379327394157

theorem tailTrace_1552138 : CollatzResearch.WordTrace tailWord_1552138 prefixEnd_1552138 354219038270379327394157 := by
  unfold tailWord_1552138
  simp only [CollatzResearch.WordTrace]
  refine ⟨14152780912719146227772267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37740749100584389940726045 14152780912719146227772267)
  ·
    refine ⟨21229171369078719341658401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14152780912719146227772267 21229171369078719341658401)
    ·
      refine ⟨15921878526809039506243801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21229171369078719341658401 15921878526809039506243801)
      ·
        refine ⟨11941408895106779629682851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15921878526809039506243801 11941408895106779629682851)
        ·
          refine ⟨17912113342660169444524277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11941408895106779629682851 17912113342660169444524277)
          ·
            refine ⟨1679260625874390885424151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17912113342660169444524277 1679260625874390885424151)
            ·
              refine ⟨2518890938811586328136227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1679260625874390885424151 2518890938811586328136227)
              ·
                refine ⟨3778336408217379492204341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2518890938811586328136227 3778336408217379492204341)
                ·
                  refine ⟨354219038270379327394157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3778336408217379492204341 354219038270379327394157)
                  ·
                    rfl

theorem cell21_1552138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 5].length) (baseStart_1552138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1552138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1552138 prefixEnd_1552138 := by exact prefixLift 1552138
  have htrace : WordTrace (prefixWord ++ tailWord_1552138) baseStart_1552138 baseEnd_1552138 := by
    simpa [prefixWord, tailWord_1552138, baseEnd_1552138] using wordTrace_append hprefix tailTrace_1552138
  have hstable : (prefixWord ++ tailWord_1552138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552138).length < 2 ^ (prefixWord ++ tailWord_1552138).sum := by decide
  have hdescent : baseEnd_1552138 < baseStart_1552138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552276 : List Nat := [2, 4, 2, 1, 1, 4, 2, 5]
def baseStart_1552276 : Nat := 118140960795 + 1552276 * 2 ^ 59
def prefixEnd_1552276 : Nat := 4983230072969 + 3 ^ 40 * 1552276 * 2
def baseEnd_1552276 : Nat := 118083510583507251364625

theorem tailTrace_1552276 : CollatzResearch.WordTrace tailWord_1552276 prefixEnd_1552276 118083510583507251364625 := by
  unfold tailWord_1552276
  simp only [CollatzResearch.WordTrace]
  refine ⟨28308078462188317239806341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37744104616251089653075121 28308078462188317239806341)
  ·
    refine ⟨5307764711660309482463689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28308078462188317239806341 5307764711660309482463689)
    ·
      refine ⟨3980823533745232111847767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5307764711660309482463689 3980823533745232111847767)
      ·
        refine ⟨5971235300617848167771651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3980823533745232111847767 5971235300617848167771651)
        ·
          refine ⟨8956852950926772251657477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5971235300617848167771651 8956852950926772251657477)
          ·
            refine ⟨1679409928298769797185777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8956852950926772251657477 1679409928298769797185777)
            ·
              refine ⟨1259557446224077347889333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1679409928298769797185777 1259557446224077347889333)
              ·
                refine ⟨118083510583507251364625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1259557446224077347889333 118083510583507251364625)
                ·
                  rfl

theorem cell21_1552276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 5].length) (baseStart_1552276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1552276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1552276 prefixEnd_1552276 := by exact prefixLift 1552276
  have htrace : WordTrace (prefixWord ++ tailWord_1552276) baseStart_1552276 baseEnd_1552276 := by
    simpa [prefixWord, tailWord_1552276, baseEnd_1552276] using wordTrace_append hprefix tailTrace_1552276
  have hstable : (prefixWord ++ tailWord_1552276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552276).length < 2 ^ (prefixWord ++ tailWord_1552276).sum := by decide
  have hdescent : baseEnd_1552276 < baseStart_1552276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552318 : List Nat := [4, 2, 1, 1, 1, 3, 1, 8]
def baseStart_1552318 : Nat := 118140960795 + 1552318 * 2 ^ 59
def prefixEnd_1552318 : Nat := 4983230072969 + 3 ^ 40 * 1552318 * 2
def baseEnd_1552318 : Nat := 118086705574246338131263

theorem tailTrace_1552318 : CollatzResearch.WordTrace tailWord_1552318 prefixEnd_1552318 118086705574246338131263 := by
  unfold tailWord_1552318
  simp only [CollatzResearch.WordTrace]
  refine ⟨7077211098778059456580201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37745125860149650435094405 7077211098778059456580201)
  ·
    refine ⟨5307908324083544592435151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7077211098778059456580201 5307908324083544592435151)
    ·
      refine ⟨7961862486125316888652727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5307908324083544592435151 7961862486125316888652727)
      ·
        refine ⟨11942793729187975332979091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7961862486125316888652727 11942793729187975332979091)
        ·
          refine ⟨17914190593781962999468637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11942793729187975332979091 17914190593781962999468637)
          ·
            refine ⟨6717821472668236124800739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17914190593781962999468637 6717821472668236124800739)
            ·
              refine ⟨10076732209002354187201109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6717821472668236124800739 10076732209002354187201109)
              ·
                refine ⟨118086705574246338131263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10076732209002354187201109 118086705574246338131263)
                ·
                  rfl

theorem cell21_1552318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_1552318 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1552318 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1552318 prefixEnd_1552318 := by exact prefixLift 1552318
  have htrace : WordTrace (prefixWord ++ tailWord_1552318) baseStart_1552318 baseEnd_1552318 := by
    simpa [prefixWord, tailWord_1552318, baseEnd_1552318] using wordTrace_append hprefix tailTrace_1552318
  have hstable : (prefixWord ++ tailWord_1552318).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552318).length < 2 ^ (prefixWord ++ tailWord_1552318).sum := by decide
  have hdescent : baseEnd_1552318 < baseStart_1552318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552408 : List Nat := [2, 1, 2, 3, 2, 1, 1, 2, 7]
def baseStart_1552408 : Nat := 118140960795 + 1552408 * 2 ^ 59
def prefixEnd_1552408 : Nat := 4983230072969 + 3 ^ 40 * 1552408 * 2
def baseEnd_1552408 : Nat := 354280655948918857893605

theorem tailTrace_1552408 : CollatzResearch.WordTrace tailWord_1552408 prefixEnd_1552408 354280655948918857893605 := by
  unfold tailWord_1552408
  simp only [CollatzResearch.WordTrace]
  refine ⟨28310485679949210511708939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37747314239932280682278585 28310485679949210511708939)
  ·
    refine ⟨42465728519923815767563409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28310485679949210511708939 42465728519923815767563409)
    ·
      refine ⟨31849296389942861825672557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42465728519923815767563409 31849296389942861825672557)
      ·
        refine ⟨11943486146228573184627209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31849296389942861825672557 11943486146228573184627209)
        ·
          refine ⟨8957614609671429888470407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11943486146228573184627209 8957614609671429888470407)
          ·
            refine ⟨13436421914507144832705611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8957614609671429888470407 13436421914507144832705611)
            ·
              refine ⟨20154632871760717249058417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13436421914507144832705611 20154632871760717249058417)
              ·
                refine ⟨15115974653820537936793813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20154632871760717249058417 15115974653820537936793813)
                ·
                  refine ⟨354280655948918857893605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15115974653820537936793813 354280655948918857893605)
                  ·
                    rfl

theorem cell21_1552408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 7].length) (baseStart_1552408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1552408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1552408 prefixEnd_1552408 := by exact prefixLift 1552408
  have htrace : WordTrace (prefixWord ++ tailWord_1552408) baseStart_1552408 baseEnd_1552408 := by
    simpa [prefixWord, tailWord_1552408, baseEnd_1552408] using wordTrace_append hprefix tailTrace_1552408
  have hstable : (prefixWord ++ tailWord_1552408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552408).length < 2 ^ (prefixWord ++ tailWord_1552408).sum := by decide
  have hdescent : baseEnd_1552408 < baseStart_1552408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552439 : List Nat := [1, 1, 3, 1, 2, 2, 2, 5, 4]
def baseStart_1552439 : Nat := 118140960795 + 1552439 * 2 ^ 59
def prefixEnd_1552439 : Nat := 4983230072969 + 3 ^ 40 * 1552439 * 2
def baseEnd_1552439 : Nat := 354287730571269692876875

theorem tailTrace_1552439 : CollatzResearch.WordTrace tailWord_1552439 prefixEnd_1552439 354287730571269692876875 := by
  unfold tailWord_1552439
  simp only [CollatzResearch.WordTrace]
  refine ⟨56622102022786113317796371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37748068015190742211864247 56622102022786113317796371)
  ·
    refine ⟨84933153034179169976694557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56622102022786113317796371 84933153034179169976694557)
    ·
      refine ⟨31849932387817188741260459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84933153034179169976694557 31849932387817188741260459)
      ·
        refine ⟨47774898581725783111890689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31849932387817188741260459 47774898581725783111890689)
        ·
          refine ⟨35831173936294337333918017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47774898581725783111890689 35831173936294337333918017)
          ·
            refine ⟨26873380452220753000438513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35831173936294337333918017 26873380452220753000438513)
            ·
              refine ⟨20155035339165564750328885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26873380452220753000438513 20155035339165564750328885)
              ·
                refine ⟨1889534563046771695343333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20155035339165564750328885 1889534563046771695343333)
                ·
                  refine ⟨354287730571269692876875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1889534563046771695343333 354287730571269692876875)
                  ·
                    rfl

theorem cell21_1552439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5, 4].length) (baseStart_1552439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1552439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1552439 prefixEnd_1552439 := by exact prefixLift 1552439
  have htrace : WordTrace (prefixWord ++ tailWord_1552439) baseStart_1552439 baseEnd_1552439 := by
    simpa [prefixWord, tailWord_1552439, baseEnd_1552439] using wordTrace_append hprefix tailTrace_1552439
  have hstable : (prefixWord ++ tailWord_1552439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552439).length < 2 ^ (prefixWord ++ tailWord_1552439).sum := by decide
  have hdescent : baseEnd_1552439 < baseStart_1552439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552490 : List Nat := [3, 1, 3, 2, 3, 2, 2, 1, 4]
def baseStart_1552490 : Nat := 118140960795 + 1552490 * 2 ^ 59
def prefixEnd_1552490 : Nat := 4983230072969 + 3 ^ 40 * 1552490 * 2
def baseEnd_1552490 : Nat := 354299369466104937526771

theorem tailTrace_1552490 : CollatzResearch.WordTrace tailWord_1552490 prefixEnd_1552490 354299369466104937526771 := by
  unfold tailWord_1552490
  simp only [CollatzResearch.WordTrace]
  refine ⟨14155990536400337256975731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37749308097067566018601949 14155990536400337256975731)
  ·
    refine ⟨21233985804600505885463597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14155990536400337256975731 21233985804600505885463597)
    ·
      refine ⟨7962744676725189707048849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21233985804600505885463597 7962744676725189707048849)
      ·
        refine ⟨5972058507543892280286637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7962744676725189707048849 5972058507543892280286637)
        ·
          refine ⟨2239521940328959605107489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5972058507543892280286637 2239521940328959605107489)
          ·
            refine ⟨1679641455246719703830617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2239521940328959605107489 1679641455246719703830617)
            ·
              refine ⟨1259731091435039777872963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1679641455246719703830617 1259731091435039777872963)
              ·
                refine ⟨1889596637152559666809445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1259731091435039777872963 1889596637152559666809445)
                ·
                  refine ⟨354299369466104937526771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1889596637152559666809445 354299369466104937526771)
                  ·
                    rfl

theorem cell21_1552490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 4].length) (baseStart_1552490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1552490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1552490 prefixEnd_1552490 := by exact prefixLift 1552490
  have htrace : WordTrace (prefixWord ++ tailWord_1552490) baseStart_1552490 baseEnd_1552490 := by
    simpa [prefixWord, tailWord_1552490, baseEnd_1552490] using wordTrace_append hprefix tailTrace_1552490
  have hstable : (prefixWord ++ tailWord_1552490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552490).length < 2 ^ (prefixWord ++ tailWord_1552490).sum := by decide
  have hdescent : baseEnd_1552490 < baseStart_1552490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552594 : List Nat := [3, 2, 2, 2, 1, 2, 2, 4, 3]
def baseStart_1552594 : Nat := 118140960795 + 1552594 * 2 ^ 59
def prefixEnd_1552594 : Nat := 4983230072969 + 3 ^ 40 * 1552594 * 2
def baseEnd_1552594 : Nat := 354323103683023867793225

theorem tailTrace_1552594 : CollatzResearch.WordTrace tailWord_1552594 prefixEnd_1552594 354323103683023867793225 := by
  unfold tailWord_1552594
  simp only [CollatzResearch.WordTrace]
  refine ⟨14156938834306143697422209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37751836891483049859792557 14156938834306143697422209)
  ·
    refine ⟨10617704125729607773066657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14156938834306143697422209 10617704125729607773066657)
    ·
      refine ⟨7963278094297205829799993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10617704125729607773066657 7963278094297205829799993)
      ·
        refine ⟨5972458570722904372349995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7963278094297205829799993 5972458570722904372349995)
        ·
          refine ⟨8958687856084356558524993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5972458570722904372349995 8958687856084356558524993)
          ·
            refine ⟨6719015892063267418893745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8958687856084356558524993 6719015892063267418893745)
            ·
              refine ⟨5039261919047450564170309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6719015892063267418893745 5039261919047450564170309)
              ·
                refine ⟨944861609821396980781933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5039261919047450564170309 944861609821396980781933)
                ·
                  refine ⟨354323103683023867793225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 944861609821396980781933 354323103683023867793225)
                  ·
                    rfl

theorem cell21_1552594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 4, 3].length) (baseStart_1552594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1552594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1552594 prefixEnd_1552594 := by exact prefixLift 1552594
  have htrace : WordTrace (prefixWord ++ tailWord_1552594) baseStart_1552594 baseEnd_1552594 := by
    simpa [prefixWord, tailWord_1552594, baseEnd_1552594] using wordTrace_append hprefix tailTrace_1552594
  have hstable : (prefixWord ++ tailWord_1552594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552594).length < 2 ^ (prefixWord ++ tailWord_1552594).sum := by decide
  have hdescent : baseEnd_1552594 < baseStart_1552594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552608 : List Nat := [2, 1, 1, 3, 1, 3, 5, 1, 4]
def baseStart_1552608 : Nat := 118140960795 + 1552608 * 2 ^ 59
def prefixEnd_1552608 : Nat := 4983230072969 + 3 ^ 40 * 1552608 * 2
def baseEnd_1552608 : Nat := 354326298673762954559863

theorem tailTrace_1552608 : CollatzResearch.WordTrace tailWord_1552608 prefixEnd_1552608 354326298673762954559863 := by
  unfold tailWord_1552608
  simp only [CollatzResearch.WordTrace]
  refine ⟨28314132979586927590349239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37752177306115903453798985 28314132979586927590349239)
  ·
    refine ⟨42471199469380391385523859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28314132979586927590349239 42471199469380391385523859)
    ·
      refine ⟨63706799204070587078285789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42471199469380391385523859 63706799204070587078285789)
      ·
        refine ⟨23890049701526470154357171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63706799204070587078285789 23890049701526470154357171)
        ·
          refine ⟨35835074552289705231535757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23890049701526470154357171 35835074552289705231535757)
          ·
            refine ⟨13438152957108639461825909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35835074552289705231535757 13438152957108639461825909)
            ·
              refine ⟨1259826839728934949546179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13438152957108639461825909 1259826839728934949546179)
              ·
                refine ⟨1889740259593402424319269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1259826839728934949546179 1889740259593402424319269)
                ·
                  refine ⟨354326298673762954559863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1889740259593402424319269 354326298673762954559863)
                  ·
                    rfl

theorem cell21_1552608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 1, 4].length) (baseStart_1552608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1552608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1552608 prefixEnd_1552608 := by exact prefixLift 1552608
  have htrace : WordTrace (prefixWord ++ tailWord_1552608) baseStart_1552608 baseEnd_1552608 := by
    simpa [prefixWord, tailWord_1552608, baseEnd_1552608] using wordTrace_append hprefix tailTrace_1552608
  have hstable : (prefixWord ++ tailWord_1552608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552608).length < 2 ^ (prefixWord ++ tailWord_1552608).sum := by decide
  have hdescent : baseEnd_1552608 < baseStart_1552608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552732 : List Nat := [2, 2, 4, 3, 1, 1, 3, 5]
def baseStart_1552732 : Nat := 118140960795 + 1552732 * 2 ^ 59
def prefixEnd_1552732 : Nat := 4983230072969 + 3 ^ 40 * 1552732 * 2
def baseEnd_1552732 : Nat := 118118199054388764830981

theorem tailTrace_1552732 : CollatzResearch.WordTrace tailWord_1552732 prefixEnd_1552732 118118199054388764830981 := by
  unfold tailWord_1552732
  simp only [CollatzResearch.WordTrace]
  refine ⟨28316394305362312179106225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37755192407149749572141633 28316394305362312179106225)
  ·
    refine ⟨21237295729021734134329669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28316394305362312179106225 21237295729021734134329669)
    ·
      refine ⟨3981992949191575150186813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21237295729021734134329669 3981992949191575150186813)
      ·
        refine ⟨1493247355946840681320055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3981992949191575150186813 1493247355946840681320055)
        ·
          refine ⟨2239871033920261021980083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1493247355946840681320055 2239871033920261021980083)
          ·
            refine ⟨3359806550880391532970125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2239871033920261021980083 3359806550880391532970125)
            ·
              refine ⟨1259927456580146824863797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3359806550880391532970125 1259927456580146824863797)
              ·
                refine ⟨118118199054388764830981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1259927456580146824863797 118118199054388764830981)
                ·
                  rfl

theorem cell21_1552732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 5].length) (baseStart_1552732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1552732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1552732 prefixEnd_1552732 := by exact prefixLift 1552732
  have htrace : WordTrace (prefixWord ++ tailWord_1552732) baseStart_1552732 baseEnd_1552732 := by
    simpa [prefixWord, tailWord_1552732, baseEnd_1552732] using wordTrace_append hprefix tailTrace_1552732
  have hstable : (prefixWord ++ tailWord_1552732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552732).length < 2 ^ (prefixWord ++ tailWord_1552732).sum := by decide
  have hdescent : baseEnd_1552732 < baseStart_1552732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552746 : List Nat := [3, 1, 3, 3, 1, 1, 1, 5, 3]
def baseStart_1552746 : Nat := 118140960795 + 1552746 * 2 ^ 59
def prefixEnd_1552746 : Nat := 4983230072969 + 3 ^ 40 * 1552746 * 2
def baseEnd_1552746 : Nat := 354357792153905381259581

theorem tailTrace_1552746 : CollatzResearch.WordTrace tailWord_1552746 prefixEnd_1552746 354357792153905381259581 := by
  unfold tailWord_1552746
  simp only [CollatzResearch.WordTrace]
  refine ⟨14158324808168476187305523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37755532821782603166148061 14158324808168476187305523)
  ·
    refine ⟨21237487212252714280958285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14158324808168476187305523 21237487212252714280958285)
    ·
      refine ⟨7964057704594767855359357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21237487212252714280958285 7964057704594767855359357)
      ·
        refine ⟨2986521639223037945759759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7964057704594767855359357 2986521639223037945759759)
        ·
          refine ⟨4479782458834556918639639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2986521639223037945759759 4479782458834556918639639)
          ·
            refine ⟨6719673688251835377959459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4479782458834556918639639 6719673688251835377959459)
            ·
              refine ⟨10079510532377753066939189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6719673688251835377959459 10079510532377753066939189)
              ·
                refine ⟨944954112410414350025549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10079510532377753066939189 944954112410414350025549)
                ·
                  refine ⟨354357792153905381259581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 944954112410414350025549 354357792153905381259581)
                  ·
                    rfl

theorem cell21_1552746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 5, 3].length) (baseStart_1552746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1552746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1552746 prefixEnd_1552746 := by exact prefixLift 1552746
  have htrace : WordTrace (prefixWord ++ tailWord_1552746) baseStart_1552746 baseEnd_1552746 := by
    simpa [prefixWord, tailWord_1552746, baseEnd_1552746] using wordTrace_append hprefix tailTrace_1552746
  have hstable : (prefixWord ++ tailWord_1552746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552746).length < 2 ^ (prefixWord ++ tailWord_1552746).sum := by decide
  have hdescent : baseEnd_1552746 < baseStart_1552746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552847 : List Nat := [1, 1, 2, 1, 1, 4, 1, 3, 7]
def baseStart_1552847 : Nat := 118140960795 + 1552847 * 2 ^ 59
def prefixEnd_1552847 : Nat := 4983230072969 + 3 ^ 40 * 1552847 * 2
def baseEnd_1552847 : Nat := 354380841729951650076041

theorem tailTrace_1552847 : CollatzResearch.WordTrace tailWord_1552847 prefixEnd_1552847 354380841729951650076041 := by
  unfold tailWord_1552847
  simp only [CollatzResearch.WordTrace]
  refine ⟨56636983005307998998648795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37757988670205332665765863 56636983005307998998648795)
  ·
    refine ⟨84955474507961998497973193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56636983005307998998648795 84955474507961998497973193)
    ·
      refine ⟨63716605880971498873479895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84955474507961998497973193 63716605880971498873479895)
      ·
        refine ⟨95574908821457248310219843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63716605880971498873479895 95574908821457248310219843)
        ·
          refine ⟨143362363232185872465329765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95574908821457248310219843 143362363232185872465329765)
          ·
            refine ⟨26880443106034851087249331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143362363232185872465329765 26880443106034851087249331)
            ·
              refine ⟨40320664659052276630873997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26880443106034851087249331 40320664659052276630873997)
              ·
                refine ⟨15120249247144603736577749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40320664659052276630873997 15120249247144603736577749)
                ·
                  refine ⟨354380841729951650076041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15120249247144603736577749 354380841729951650076041)
                  ·
                    rfl

theorem cell21_1552847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 7].length) (baseStart_1552847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1552847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1552847 prefixEnd_1552847 := by exact prefixLift 1552847
  have htrace : WordTrace (prefixWord ++ tailWord_1552847) baseStart_1552847 baseEnd_1552847 := by
    simpa [prefixWord, tailWord_1552847, baseEnd_1552847] using wordTrace_append hprefix tailTrace_1552847
  have hstable : (prefixWord ++ tailWord_1552847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552847).length < 2 ^ (prefixWord ++ tailWord_1552847).sum := by decide
  have hdescent : baseEnd_1552847 < baseStart_1552847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552881 : List Nat := [1, 2, 2, 2, 3, 1, 3, 4, 3]
def baseStart_1552881 : Nat := 118140960795 + 1552881 * 2 ^ 59
def prefixEnd_1552881 : Nat := 4983230072969 + 3 ^ 40 * 1552881 * 2
def baseEnd_1552881 : Nat := 354388600993175146509305

theorem tailTrace_1552881 : CollatzResearch.WordTrace tailWord_1552881 prefixEnd_1552881 354388600993175146509305 := by
  unfold tailWord_1552881
  simp only [CollatzResearch.WordTrace]
  refine ⟨56638223087184822805386497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37758815391456548536924331 56638223087184822805386497)
  ·
    refine ⟨42478667315388617104039873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56638223087184822805386497 42478667315388617104039873)
    ·
      refine ⟨31859000486541462828029905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42478667315388617104039873 31859000486541462828029905)
      ·
        refine ⟨23894250364906097121022429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31859000486541462828029905 23894250364906097121022429)
        ·
          refine ⟨8960343886839786420383411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23894250364906097121022429 8960343886839786420383411)
          ·
            refine ⟨13440515830259679630575117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8960343886839786420383411 13440515830259679630575117)
            ·
              refine ⟨5040193436347379861465669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13440515830259679630575117 5040193436347379861465669)
              ·
                refine ⟨945036269315133724024813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5040193436347379861465669 945036269315133724024813)
                ·
                  refine ⟨354388600993175146509305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 945036269315133724024813 354388600993175146509305)
                  ·
                    rfl

theorem cell21_1552881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 4, 3].length) (baseStart_1552881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1552881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1552881 prefixEnd_1552881 := by exact prefixLift 1552881
  have htrace : WordTrace (prefixWord ++ tailWord_1552881) baseStart_1552881 baseEnd_1552881 := by
    simpa [prefixWord, tailWord_1552881, baseEnd_1552881] using wordTrace_append hprefix tailTrace_1552881
  have hstable : (prefixWord ++ tailWord_1552881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552881).length < 2 ^ (prefixWord ++ tailWord_1552881).sum := by decide
  have hdescent : baseEnd_1552881 < baseStart_1552881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552898 : List Nat := [3, 4, 1, 2, 2, 1, 1, 2, 5]
def baseStart_1552898 : Nat := 118140960795 + 1552898 * 2 ^ 59
def prefixEnd_1552898 : Nat := 4983230072969 + 3 ^ 40 * 1552898 * 2
def baseEnd_1552898 : Nat := 354392480624786894725937

theorem tailTrace_1552898 : CollatzResearch.WordTrace tailWord_1552898 prefixEnd_1552898 354392480624786894725937 := by
  unfold tailWord_1552898
  simp only [CollatzResearch.WordTrace]
  refine ⟨14159710782030808677188837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37759228752082156472503565 14159710782030808677188837)
  ·
    refine ⟨2654945771630776626972907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14159710782030808677188837 2654945771630776626972907)
    ·
      refine ⟨3982418657446164940459361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2654945771630776626972907 3982418657446164940459361)
      ·
        refine ⟨2986813993084623705344521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3982418657446164940459361 2986813993084623705344521)
        ·
          refine ⟨2240110494813467779008391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2986813993084623705344521 2240110494813467779008391)
          ·
            refine ⟨3360165742220201668512587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2240110494813467779008391 3360165742220201668512587)
            ·
              refine ⟨5040248613330302502768881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3360165742220201668512587 5040248613330302502768881)
              ·
                refine ⟨3780186459997726877076661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5040248613330302502768881 3780186459997726877076661)
                ·
                  refine ⟨354392480624786894725937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3780186459997726877076661 354392480624786894725937)
                  ·
                    rfl

theorem cell21_1552898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_1552898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1552898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1552898 prefixEnd_1552898 := by exact prefixLift 1552898
  have htrace : WordTrace (prefixWord ++ tailWord_1552898) baseStart_1552898 baseEnd_1552898 := by
    simpa [prefixWord, tailWord_1552898, baseEnd_1552898] using wordTrace_append hprefix tailTrace_1552898
  have hstable : (prefixWord ++ tailWord_1552898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552898).length < 2 ^ (prefixWord ++ tailWord_1552898).sum := by decide
  have hdescent : baseEnd_1552898 < baseStart_1552898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553005 : List Nat := [1, 5, 1, 1, 3, 3, 2, 1, 4]
def baseStart_1553005 : Nat := 118140960795 + 1553005 * 2 ^ 59
def prefixEnd_1553005 : Nat := 4983230072969 + 3 ^ 40 * 1553005 * 2
def baseEnd_1553005 : Nat := 354416899482578486442385

theorem tailTrace_1553005 : CollatzResearch.WordTrace tailWord_1553005 prefixEnd_1553005 354416899482578486442385 := by
  unfold tailWord_1553005
  simp only [CollatzResearch.WordTrace]
  refine ⟨56642745738735591982900469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37761830492490394655266979 56642745738735591982900469)
  ·
    refine ⟨5310257413006461748396919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56642745738735591982900469 5310257413006461748396919)
    ·
      refine ⟨7965386119509692622595379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5310257413006461748396919 7965386119509692622595379)
      ·
        refine ⟨11948079179264538933893069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7965386119509692622595379 11948079179264538933893069)
        ·
          refine ⟨4480529692224202100209901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11948079179264538933893069 4480529692224202100209901)
          ·
            refine ⟨1680198634584075787578713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4480529692224202100209901 1680198634584075787578713)
            ·
              refine ⟨1260148975938056840684035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1680198634584075787578713 1260148975938056840684035)
              ·
                refine ⟨1890223463907085261026053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1260148975938056840684035 1890223463907085261026053)
                ·
                  refine ⟨354416899482578486442385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1890223463907085261026053 354416899482578486442385)
                  ·
                    rfl

theorem cell21_1553005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_1553005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1553005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1553005 prefixEnd_1553005 := by exact prefixLift 1553005
  have htrace : WordTrace (prefixWord ++ tailWord_1553005) baseStart_1553005 baseEnd_1553005 := by
    simpa [prefixWord, tailWord_1553005, baseEnd_1553005] using wordTrace_append hprefix tailTrace_1553005
  have hstable : (prefixWord ++ tailWord_1553005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553005).length < 2 ^ (prefixWord ++ tailWord_1553005).sum := by decide
  have hdescent : baseEnd_1553005 < baseStart_1553005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553047 : List Nat := [1, 1, 3, 3, 2, 1, 4, 2, 4]
def baseStart_1553047 : Nat := 118140960795 + 1553047 * 2 ^ 59
def prefixEnd_1553047 : Nat := 4983230072969 + 3 ^ 40 * 1553047 * 2
def baseEnd_1553047 : Nat := 354426484454795746742299

theorem tailTrace_1553047 : CollatzResearch.WordTrace tailWord_1553047 prefixEnd_1553047 354426484454795746742299 := by
  unfold tailWord_1553047
  simp only [CollatzResearch.WordTrace]
  refine ⟨56644277604583433155929395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37762851736388955437286263 56644277604583433155929395)
  ·
    refine ⟨84966416406875149733894093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56644277604583433155929395 84966416406875149733894093)
    ·
      refine ⟨31862406152578181150210285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84966416406875149733894093 31862406152578181150210285)
      ·
        refine ⟨11948402307216817931328857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31862406152578181150210285 11948402307216817931328857)
        ·
          refine ⟨8961301730412613448496643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11948402307216817931328857 8961301730412613448496643)
          ·
            refine ⟨13441952595618920172744965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8961301730412613448496643 13441952595618920172744965)
            ·
              refine ⟨2520366111678547532389681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13441952595618920172744965 2520366111678547532389681)
              ·
                refine ⟨1890274583758910649292261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2520366111678547532389681 1890274583758910649292261)
                ·
                  refine ⟨354426484454795746742299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1890274583758910649292261 354426484454795746742299)
                  ·
                    rfl

theorem cell21_1553047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2, 4].length) (baseStart_1553047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1553047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1553047 prefixEnd_1553047 := by exact prefixLift 1553047
  have htrace : WordTrace (prefixWord ++ tailWord_1553047) baseStart_1553047 baseEnd_1553047 := by
    simpa [prefixWord, tailWord_1553047, baseEnd_1553047] using wordTrace_append hprefix tailTrace_1553047
  have hstable : (prefixWord ++ tailWord_1553047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553047).length < 2 ^ (prefixWord ++ tailWord_1553047).sum := by decide
  have hdescent : baseEnd_1553047 < baseStart_1553047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553075 : List Nat := [1, 1, 1, 2, 3, 4, 1, 1, 7]
def baseStart_1553075 : Nat := 118140960795 + 1553075 * 2 ^ 59
def prefixEnd_1553075 : Nat := 4983230072969 + 3 ^ 40 * 1553075 * 2
def baseEnd_1553075 : Nat := 354432874436273920275575

theorem tailTrace_1553075 : CollatzResearch.WordTrace tailWord_1553075 prefixEnd_1553075 354432874436273920275575 := by
  unfold tailWord_1553075
  simp only [CollatzResearch.WordTrace]
  refine ⟨56645298848481993937948679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37763532565654662625299119 56645298848481993937948679)
  ·
    refine ⟨84967948272722990906923019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56645298848481993937948679 84967948272722990906923019)
    ·
      refine ⟨127451922409084486360384529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84967948272722990906923019 127451922409084486360384529)
      ·
        refine ⟨95588941806813364770288397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127451922409084486360384529 95588941806813364770288397)
        ·
          refine ⟨35845853177555011788858149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95588941806813364770288397 35845853177555011788858149)
          ·
            refine ⟨6721097470791564710410903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35845853177555011788858149 6721097470791564710410903)
            ·
              refine ⟨10081646206187347065616355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6721097470791564710410903 10081646206187347065616355)
              ·
                refine ⟨15122469309281020598424533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10081646206187347065616355 15122469309281020598424533)
                ·
                  refine ⟨354432874436273920275575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15122469309281020598424533 354432874436273920275575)
                  ·
                    rfl

theorem cell21_1553075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 7].length) (baseStart_1553075 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1553075 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1553075 prefixEnd_1553075 := by exact prefixLift 1553075
  have htrace : WordTrace (prefixWord ++ tailWord_1553075) baseStart_1553075 baseEnd_1553075 := by
    simpa [prefixWord, tailWord_1553075, baseEnd_1553075] using wordTrace_append hprefix tailTrace_1553075
  have hstable : (prefixWord ++ tailWord_1553075).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553075).length < 2 ^ (prefixWord ++ tailWord_1553075).sum := by decide
  have hdescent : baseEnd_1553075 < baseStart_1553075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553120 : List Nat := [2, 1, 1, 3, 1, 2, 1, 10]
def baseStart_1553120 : Nat := 118140960795 + 1553120 * 2 ^ 59
def prefixEnd_1553120 : Nat := 4983230072969 + 3 ^ 40 * 1553120 * 2
def baseEnd_1553120 : Nat := 118147714683121280675161

theorem tailTrace_1553120 : CollatzResearch.WordTrace tailWord_1553120 prefixEnd_1553120 118147714683121280675161 := by
  unfold tailWord_1553120
  simp only [CollatzResearch.WordTrace]
  refine ⟨28323470066659483311668407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37764626755545977748891209 28323470066659483311668407)
  ·
    refine ⟨42485205099989224967502611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28323470066659483311668407 42485205099989224967502611)
    ·
      refine ⟨63727807649983837451253917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42485205099989224967502611 63727807649983837451253917)
      ·
        refine ⟨23897927868743939044220219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63727807649983837451253917 23897927868743939044220219)
        ·
          refine ⟨35846891803115908566330329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23897927868743939044220219 35846891803115908566330329)
          ·
            refine ⟨26885168852336931424747747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35846891803115908566330329 26885168852336931424747747)
            ·
              refine ⟨40327753278505397137121621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26885168852336931424747747 40327753278505397137121621)
              ·
                refine ⟨118147714683121280675161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 40327753278505397137121621 118147714683121280675161)
                ·
                  rfl

theorem cell21_1553120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 10].length) (baseStart_1553120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1553120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1553120 prefixEnd_1553120 := by exact prefixLift 1553120
  have htrace : WordTrace (prefixWord ++ tailWord_1553120) baseStart_1553120 baseEnd_1553120 := by
    simpa [prefixWord, tailWord_1553120, baseEnd_1553120] using wordTrace_append hprefix tailTrace_1553120
  have hstable : (prefixWord ++ tailWord_1553120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553120).length < 2 ^ (prefixWord ++ tailWord_1553120).sum := by decide
  have hdescent : baseEnd_1553120 < baseStart_1553120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553154 : List Nat := [3, 4, 1, 1, 1, 4, 7]
def baseStart_1553154 : Nat := 118140960795 + 1553154 * 2 ^ 59
def prefixEnd_1553154 : Nat := 4983230072969 + 3 ^ 40 * 1553154 * 2
def baseEnd_1553154 : Nat := 39383433701398593162083

theorem tailTrace_1553154 : CollatzResearch.WordTrace tailWord_1553154 prefixEnd_1553154 39383433701398593162083 := by
  unfold tailWord_1553154
  simp only [CollatzResearch.WordTrace]
  refine ⟨14162045053798947607518629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37765453476797193620049677 14162045053798947607518629)
  ·
    refine ⟨2655383447587302676409743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14162045053798947607518629 2655383447587302676409743)
    ·
      refine ⟨3983075171380954014614615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2655383447587302676409743 3983075171380954014614615)
      ·
        refine ⟨5974612757071431021921923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3983075171380954014614615 5974612757071431021921923)
        ·
          refine ⟨8961919135607146532882885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5974612757071431021921923 8961919135607146532882885)
          ·
            refine ⟨1680359837926339974915541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8961919135607146532882885 1680359837926339974915541)
            ·
              refine ⟨39383433701398593162083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1680359837926339974915541 39383433701398593162083)
              ·
                rfl

theorem cell21_1553154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 7].length) (baseStart_1553154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1553154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1553154 prefixEnd_1553154 := by exact prefixLift 1553154
  have htrace : WordTrace (prefixWord ++ tailWord_1553154) baseStart_1553154 baseEnd_1553154 := by
    simpa [prefixWord, tailWord_1553154, baseEnd_1553154] using wordTrace_append hprefix tailTrace_1553154
  have hstable : (prefixWord ++ tailWord_1553154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553154).length < 2 ^ (prefixWord ++ tailWord_1553154).sum := by decide
  have hdescent : baseEnd_1553154 < baseStart_1553154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553196 : List Nat := [2, 2, 1, 1, 1, 4, 1, 9]
def baseStart_1553196 : Nat := 118140960795 + 1553196 * 2 ^ 59
def prefixEnd_1553196 : Nat := 4983230072969 + 3 ^ 40 * 1553196 * 2
def baseEnd_1553196 : Nat := 118153496094934866252887

theorem tailTrace_1553196 : CollatzResearch.WordTrace tailWord_1553196 prefixEnd_1553196 118153496094934866252887 := by
  unfold tailWord_1553196
  simp only [CollatzResearch.WordTrace]
  refine ⟨28324856040521815801551721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37766474720695754402068961 28324856040521815801551721)
  ·
    refine ⟨21243642030391361851163791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28324856040521815801551721 21243642030391361851163791)
    ·
      refine ⟨31865463045587042776745687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21243642030391361851163791 31865463045587042776745687)
      ·
        refine ⟨47798194568380564165118531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31865463045587042776745687 47798194568380564165118531)
        ·
          refine ⟨71697291852570846247677797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47798194568380564165118531 71697291852570846247677797)
          ·
            refine ⟨13443242222357033671439587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71697291852570846247677797 13443242222357033671439587)
            ·
              refine ⟨20164863333535550507159381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13443242222357033671439587 20164863333535550507159381)
              ·
                refine ⟨118153496094934866252887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20164863333535550507159381 118153496094934866252887)
                ·
                  rfl

theorem cell21_1553196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 9].length) (baseStart_1553196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1553196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1553196 prefixEnd_1553196 := by exact prefixLift 1553196
  have htrace : WordTrace (prefixWord ++ tailWord_1553196) baseStart_1553196 baseEnd_1553196 := by
    simpa [prefixWord, tailWord_1553196, baseEnd_1553196] using wordTrace_append hprefix tailTrace_1553196
  have hstable : (prefixWord ++ tailWord_1553196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553196).length < 2 ^ (prefixWord ++ tailWord_1553196).sum := by decide
  have hdescent : baseEnd_1553196 < baseStart_1553196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553213 : List Nat := [1, 4, 1, 4, 2, 9]
def baseStart_1553213 : Nat := 118140960795 + 1553213 * 2 ^ 59
def prefixEnd_1553213 : Nat := 4983230072969 + 3 ^ 40 * 1553213 * 2
def baseEnd_1553213 : Nat := 13128309922830235073159

theorem tailTrace_1553213 : CollatzResearch.WordTrace tailWord_1553213 prefixEnd_1553213 13128309922830235073159 := by
  unfold tailWord_1553213
  simp only [CollatzResearch.WordTrace]
  refine ⟨56650332121982043506472293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37766888081321362337648195 56650332121982043506472293)
  ·
    refine ⟨10621937272871633157463555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56650332121982043506472293 10621937272871633157463555)
    ·
      refine ⟨15932905909307449736195333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10621937272871633157463555 15932905909307449736195333)
      ·
        refine ⟨2987419857995146825536625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15932905909307449736195333 2987419857995146825536625)
        ·
          refine ⟨2240564893496360119152469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2987419857995146825536625 2240564893496360119152469)
          ·
            refine ⟨13128309922830235073159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2240564893496360119152469 13128309922830235073159)
            ·
              rfl

theorem cell21_1553213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 9].length) (baseStart_1553213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1553213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1553213 prefixEnd_1553213 := by exact prefixLift 1553213
  have htrace : WordTrace (prefixWord ++ tailWord_1553213) baseStart_1553213 baseEnd_1553213 := by
    simpa [prefixWord, tailWord_1553213, baseEnd_1553213] using wordTrace_append hprefix tailTrace_1553213
  have hstable : (prefixWord ++ tailWord_1553213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553213).length < 2 ^ (prefixWord ++ tailWord_1553213).sum := by decide
  have hdescent : baseEnd_1553213 < baseStart_1553213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553244 : List Nat := [2, 2, 4, 2, 1, 1, 1, 1, 7]
def baseStart_1553244 : Nat := 118140960795 + 1553244 * 2 ^ 59
def prefixEnd_1553244 : Nat := 4983230072969 + 3 ^ 40 * 1553244 * 2
def baseEnd_1553244 : Nat := 354471442538767181958563

theorem tailTrace_1553244 : CollatzResearch.WordTrace tailWord_1553244 prefixEnd_1553244 354471442538767181958563 := by
  unfold tailWord_1553244
  simp only [CollatzResearch.WordTrace]
  refine ⟨28325731392434867900425393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37767641856579823867233857 28325731392434867900425393)
  ·
    refine ⟨21244298544326150925319045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28325731392434867900425393 21244298544326150925319045)
    ·
      refine ⟨3983305977061153298497321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21244298544326150925319045 3983305977061153298497321)
      ·
        refine ⟨2987479482795864973872991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3983305977061153298497321 2987479482795864973872991)
        ·
          refine ⟨4481219224193797460809487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2987479482795864973872991 4481219224193797460809487)
          ·
            refine ⟨6721828836290696191214231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4481219224193797460809487 6721828836290696191214231)
            ·
              refine ⟨10082743254436044286821347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6721828836290696191214231 10082743254436044286821347)
              ·
                refine ⟨15124114881654066430232021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10082743254436044286821347 15124114881654066430232021)
                ·
                  refine ⟨354471442538767181958563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15124114881654066430232021 354471442538767181958563)
                  ·
                    rfl

theorem cell21_1553244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 7].length) (baseStart_1553244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1553244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1553244 prefixEnd_1553244 := by exact prefixLift 1553244
  have htrace : WordTrace (prefixWord ++ tailWord_1553244) baseStart_1553244 baseEnd_1553244 := by
    simpa [prefixWord, tailWord_1553244, baseEnd_1553244] using wordTrace_append hprefix tailTrace_1553244
  have hstable : (prefixWord ++ tailWord_1553244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553244).length < 2 ^ (prefixWord ++ tailWord_1553244).sum := by decide
  have hdescent : baseEnd_1553244 < baseStart_1553244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553278 : List Nat := [4, 2, 3, 1, 2, 1, 2, 1, 5]
def baseStart_1553278 : Nat := 118140960795 + 1553278 * 2 ^ 59
def prefixEnd_1553278 : Nat := 4983230072969 + 3 ^ 40 * 1553278 * 2
def baseEnd_1553278 : Nat := 354479201801990678391827

theorem tailTrace_1553278 : CollatzResearch.WordTrace tailWord_1553278 prefixEnd_1553278 354479201801990678391827 := by
  unfold tailWord_1553278
  simp only [CollatzResearch.WordTrace]
  refine ⟨7081587858343319950948561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37768468577831039738392325 7081587858343319950948561)
  ·
    refine ⟨5311190893757489963211421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7081587858343319950948561 5311190893757489963211421)
    ·
      refine ⟨1991696585159058736204283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5311190893757489963211421 1991696585159058736204283)
      ·
        refine ⟨2987544877738588104306425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1991696585159058736204283 2987544877738588104306425)
        ·
          refine ⟨2240658658303941078229819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2987544877738588104306425 2240658658303941078229819)
          ·
            refine ⟨3360987987455911617344729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2240658658303941078229819 3360987987455911617344729)
            ·
              refine ⟨2520740990591933713008547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3360987987455911617344729 2520740990591933713008547)
              ·
                refine ⟨3781111485887900569512821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2520740990591933713008547 3781111485887900569512821)
                ·
                  refine ⟨354479201801990678391827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3781111485887900569512821 354479201801990678391827)
                  ·
                    rfl

theorem cell21_1553278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_1553278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1553278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1553278 prefixEnd_1553278 := by exact prefixLift 1553278
  have htrace : WordTrace (prefixWord ++ tailWord_1553278) baseStart_1553278 baseEnd_1553278 := by
    simpa [prefixWord, tailWord_1553278, baseEnd_1553278] using wordTrace_append hprefix tailTrace_1553278
  have hstable : (prefixWord ++ tailWord_1553278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553278).length < 2 ^ (prefixWord ++ tailWord_1553278).sum := by decide
  have hdescent : baseEnd_1553278 < baseStart_1553278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553303 : List Nat := [1, 1, 3, 3, 1, 2, 1, 4, 5]
def baseStart_1553303 : Nat := 118140960795 + 1553303 * 2 ^ 59
def prefixEnd_1553303 : Nat := 4983230072969 + 3 ^ 40 * 1553303 * 2
def baseEnd_1553303 : Nat := 354484907142596190475109

theorem tailTrace_1553303 : CollatzResearch.WordTrace tailWord_1553303 prefixEnd_1553303 354484907142596190475109 := by
  unfold tailWord_1553303
  simp only [CollatzResearch.WordTrace]
  refine ⟨56653614691655988877248563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37769076461103992584832375 56653614691655988877248563)
  ·
    refine ⟨84980422037483983315872845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56653614691655988877248563 84980422037483983315872845)
    ·
      refine ⟨31867658264056493743452317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84980422037483983315872845 31867658264056493743452317)
      ·
        refine ⟨11950371849021185153794619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31867658264056493743452317 11950371849021185153794619)
        ·
          refine ⟨17925557773531777730691929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11950371849021185153794619 17925557773531777730691929)
          ·
            refine ⟨13444168330148833298018947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17925557773531777730691929 13444168330148833298018947)
            ·
              refine ⟨20166252495223249947028421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13444168330148833298018947 20166252495223249947028421)
              ·
                refine ⟨3781172342854359365067829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20166252495223249947028421 3781172342854359365067829)
                ·
                  refine ⟨354484907142596190475109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3781172342854359365067829 354484907142596190475109)
                  ·
                    rfl

theorem cell21_1553303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 5].length) (baseStart_1553303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1553303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1553303 prefixEnd_1553303 := by exact prefixLift 1553303
  have htrace : WordTrace (prefixWord ++ tailWord_1553303) baseStart_1553303 baseEnd_1553303 := by
    simpa [prefixWord, tailWord_1553303, baseEnd_1553303] using wordTrace_append hprefix tailTrace_1553303
  have hstable : (prefixWord ++ tailWord_1553303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553303).length < 2 ^ (prefixWord ++ tailWord_1553303).sum := by decide
  have hdescent : baseEnd_1553303 < baseStart_1553303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553351 : List Nat := [1, 1, 4, 1, 1, 2, 6, 1, 4]
def baseStart_1553351 : Nat := 118140960795 + 1553351 * 2 ^ 59
def prefixEnd_1553351 : Nat := 4983230072969 + 3 ^ 40 * 1553351 * 2
def baseEnd_1553351 : Nat := 354495861396558773675011

theorem tailTrace_1553351 : CollatzResearch.WordTrace tailWord_1553351 prefixEnd_1553351 354495861396558773675011 := by
  unfold tailWord_1553351
  simp only [CollatzResearch.WordTrace]
  refine ⟨56655365395482093074995907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37770243596988062049997271 56655365395482093074995907)
  ·
    refine ⟨84983048093223139612493861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56655365395482093074995907 84983048093223139612493861)
    ·
      refine ⟨15934321517479338677342599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84983048093223139612493861 15934321517479338677342599)
      ·
        refine ⟨23901482276219008016013899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15934321517479338677342599 23901482276219008016013899)
        ·
          refine ⟨35852223414328512024020849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23901482276219008016013899 35852223414328512024020849)
          ·
            refine ⟨26889167560746384018015637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35852223414328512024020849 26889167560746384018015637)
            ·
              refine ⟨1260429729409986750844483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26889167560746384018015637 1260429729409986750844483)
              ·
                refine ⟨1890644594114980126266725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1260429729409986750844483 1890644594114980126266725)
                ·
                  refine ⟨354495861396558773675011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1890644594114980126266725 354495861396558773675011)
                  ·
                    rfl

theorem cell21_1553351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 1, 4].length) (baseStart_1553351 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1553351 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1553351 prefixEnd_1553351 := by exact prefixLift 1553351
  have htrace : WordTrace (prefixWord ++ tailWord_1553351) baseStart_1553351 baseEnd_1553351 := by
    simpa [prefixWord, tailWord_1553351, baseEnd_1553351] using wordTrace_append hprefix tailTrace_1553351
  have hstable : (prefixWord ++ tailWord_1553351).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553351).length < 2 ^ (prefixWord ++ tailWord_1553351).sum := by decide
  have hdescent : baseEnd_1553351 < baseStart_1553351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553444 : List Nat := [2, 3, 1, 4, 1, 3, 1, 2, 4]
def baseStart_1553444 : Nat := 118140960795 + 1553444 * 2 ^ 59
def prefixEnd_1553444 : Nat := 4983230072969 + 3 ^ 40 * 1553444 * 2
def baseEnd_1553444 : Nat := 354517085263611278624821

theorem tailTrace_1553444 : CollatzResearch.WordTrace tailWord_1553444 prefixEnd_1553444 354517085263611278624821 := by
  unfold tailWord_1553444
  simp only [CollatzResearch.WordTrace]
  refine ⟨28329378692072584979065693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37772504922763446638754257 28329378692072584979065693)
  ·
    refine ⟨10623517009527219367149635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28329378692072584979065693 10623517009527219367149635)
    ·
      refine ⟨15935275514290829050724453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10623517009527219367149635 15935275514290829050724453)
      ·
        refine ⟨2987864158929530447010835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15935275514290829050724453 2987864158929530447010835)
        ·
          refine ⟨4481796238394295670516253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2987864158929530447010835 4481796238394295670516253)
          ·
            refine ⟨1680673589397860876443595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4481796238394295670516253 1680673589397860876443595)
            ·
              refine ⟨2521010384096791314665393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1680673589397860876443595 2521010384096791314665393)
              ·
                refine ⟨1890757788072593485999045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2521010384096791314665393 1890757788072593485999045)
                ·
                  refine ⟨354517085263611278624821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1890757788072593485999045 354517085263611278624821)
                  ·
                    rfl

theorem cell21_1553444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_1553444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1553444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1553444 prefixEnd_1553444 := by exact prefixLift 1553444
  have htrace : WordTrace (prefixWord ++ tailWord_1553444) baseStart_1553444 baseEnd_1553444 := by
    simpa [prefixWord, tailWord_1553444, baseEnd_1553444] using wordTrace_append hprefix tailTrace_1553444
  have hstable : (prefixWord ++ tailWord_1553444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553444).length < 2 ^ (prefixWord ++ tailWord_1553444).sum := by decide
  have hdescent : baseEnd_1553444 < baseStart_1553444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553517 : List Nat := [1, 5, 1, 1, 2, 3, 2, 6]
def baseStart_1553517 : Nat := 118140960795 + 1553517 * 2 ^ 59
def prefixEnd_1553517 : Nat := 4983230072969 + 3 ^ 40 * 1553517 * 2
def baseEnd_1553517 : Nat := 118177914952726457969335

theorem tailTrace_1553517 : CollatzResearch.WordTrace tailWord_1553517 prefixEnd_1553517 118177914952726457969335 := by
  unfold tailWord_1553517
  simp only [CollatzResearch.WordTrace]
  refine ⟨56661419912880703425538805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37774279941920468950359203 56661419912880703425538805)
  ·
    refine ⟨5312008116832565946144263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56661419912880703425538805 5312008116832565946144263)
    ·
      refine ⟨7968012175248848919216395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5312008116832565946144263 7968012175248848919216395)
      ·
        refine ⟨11952018262873273378824593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7968012175248848919216395 11952018262873273378824593)
        ·
          refine ⟨8964013697154955034118445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11952018262873273378824593 8964013697154955034118445)
          ·
            refine ⟨3361505136433108137794417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8964013697154955034118445 3361505136433108137794417)
            ·
              refine ⟨2521128852324831103345813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3361505136433108137794417 2521128852324831103345813)
              ·
                refine ⟨118177914952726457969335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2521128852324831103345813 118177914952726457969335)
                ·
                  rfl

theorem cell21_1553517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 6].length) (baseStart_1553517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1553517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1553517 prefixEnd_1553517 := by exact prefixLift 1553517
  have htrace : WordTrace (prefixWord ++ tailWord_1553517) baseStart_1553517 baseEnd_1553517 := by
    simpa [prefixWord, tailWord_1553517, baseEnd_1553517] using wordTrace_append hprefix tailTrace_1553517
  have hstable : (prefixWord ++ tailWord_1553517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553517).length < 2 ^ (prefixWord ++ tailWord_1553517).sum := by decide
  have hdescent : baseEnd_1553517 < baseStart_1553517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553593 : List Nat := [1, 2, 1, 4, 1, 4, 3, 5]
def baseStart_1553593 : Nat := 118140960795 + 1553593 * 2 ^ 59
def prefixEnd_1553593 : Nat := 4983230072969 + 3 ^ 40 * 1553593 * 2
def baseEnd_1553593 : Nat := 118183696364540043547061

theorem tailTrace_1553593 : CollatzResearch.WordTrace tailWord_1553593 prefixEnd_1553593 118183696364540043547061 := by
  unfold tailWord_1553593
  simp only [CollatzResearch.WordTrace]
  refine ⟨56664191860605368405305433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37776127907070245603536955 56664191860605368405305433)
  ·
    refine ⟨42498143895454026303979075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56664191860605368405305433 42498143895454026303979075)
    ·
      refine ⟨63747215843181039455968613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42498143895454026303979075 63747215843181039455968613)
      ·
        refine ⟨11952602970596444897994115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63747215843181039455968613 11952602970596444897994115)
        ·
          refine ⟨17928904455894667346991173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11952602970596444897994115 17928904455894667346991173)
          ·
            refine ⟨3361669585480250127560845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17928904455894667346991173 3361669585480250127560845)
            ·
              refine ⟨1260626094555093797835317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3361669585480250127560845 1260626094555093797835317)
              ·
                refine ⟨118183696364540043547061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1260626094555093797835317 118183696364540043547061)
                ·
                  rfl

theorem cell21_1553593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 5].length) (baseStart_1553593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1553593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1553593 prefixEnd_1553593 := by exact prefixLift 1553593
  have htrace : WordTrace (prefixWord ++ tailWord_1553593) baseStart_1553593 baseEnd_1553593 := by
    simpa [prefixWord, tailWord_1553593, baseEnd_1553593] using wordTrace_append hprefix tailTrace_1553593
  have hstable : (prefixWord ++ tailWord_1553593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553593).length < 2 ^ (prefixWord ++ tailWord_1553593).sum := by decide
  have hdescent : baseEnd_1553593 < baseStart_1553593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553624 : List Nat := [2, 1, 2, 2, 5, 1, 2, 1, 5]
def baseStart_1553624 : Nat := 118140960795 + 1553624 * 2 ^ 59
def prefixEnd_1553624 : Nat := 4983230072969 + 3 ^ 40 * 1553624 * 2
def baseEnd_1553624 : Nat := 354558163715970965624453

theorem tailTrace_1553624 : CollatzResearch.WordTrace tailWord_1553624 prefixEnd_1553624 354558163715970965624453 := by
  unfold tailWord_1553624
  simp only [CollatzResearch.WordTrace]
  refine ⟨28332661261746530349841963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37776881682328707133122617 28332661261746530349841963)
  ·
    refine ⟨42498991892619795524762945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28332661261746530349841963 42498991892619795524762945)
    ·
      refine ⟨31874243919464846643572209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42498991892619795524762945 31874243919464846643572209)
      ·
        refine ⟨23905682939598634982679157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31874243919464846643572209 23905682939598634982679157)
        ·
          refine ⟨2241157775587372029626171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23905682939598634982679157 2241157775587372029626171)
          ·
            refine ⟨3361736663381058044439257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2241157775587372029626171 3361736663381058044439257)
            ·
              refine ⟨2521302497535793533329443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3361736663381058044439257 2521302497535793533329443)
              ·
                refine ⟨3781953746303690299994165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2521302497535793533329443 3781953746303690299994165)
                ·
                  refine ⟨354558163715970965624453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3781953746303690299994165 354558163715970965624453)
                  ·
                    rfl

theorem cell21_1553624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 5].length) (baseStart_1553624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1553624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1553624 prefixEnd_1553624 := by exact prefixLift 1553624
  have htrace : WordTrace (prefixWord ++ tailWord_1553624) baseStart_1553624 baseEnd_1553624 := by
    simpa [prefixWord, tailWord_1553624, baseEnd_1553624] using wordTrace_append hprefix tailTrace_1553624
  have hstable : (prefixWord ++ tailWord_1553624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553624).length < 2 ^ (prefixWord ++ tailWord_1553624).sum := by decide
  have hdescent : baseEnd_1553624 < baseStart_1553624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553776 : List Nat := [2, 1, 1, 1, 4, 2, 4, 3, 3]
def baseStart_1553776 : Nat := 118140960795 + 1553776 * 2 ^ 59
def prefixEnd_1553776 : Nat := 4983230072969 + 3 ^ 40 * 1553776 * 2
def baseEnd_1553776 : Nat := 354592852186852479090809

theorem tailTrace_1553776 : CollatzResearch.WordTrace tailWord_1553776 prefixEnd_1553776 354592852186852479090809 := by
  unfold tailWord_1553776
  simp only [CollatzResearch.WordTrace]
  refine ⟨28335433209471195329608591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37780577612628260439478121 28335433209471195329608591)
  ·
    refine ⟨42503149814206792994412887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28335433209471195329608591 42503149814206792994412887)
    ·
      refine ⟨63754724721310189491619331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42503149814206792994412887 63754724721310189491619331)
      ·
        refine ⟨95632087081965284237428997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63754724721310189491619331 95632087081965284237428997)
        ·
          refine ⟨17931016327868490794517937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95632087081965284237428997 17931016327868490794517937)
          ·
            refine ⟨13448262245901368095888453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17931016327868490794517937 13448262245901368095888453)
            ·
              refine ⟨2521549171106506517979085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13448262245901368095888453 2521549171106506517979085)
              ·
                refine ⟨945580939164939944242157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2521549171106506517979085 945580939164939944242157)
                ·
                  refine ⟨354592852186852479090809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 945580939164939944242157 354592852186852479090809)
                  ·
                    rfl

theorem cell21_1553776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 3, 3].length) (baseStart_1553776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1553776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1553776 prefixEnd_1553776 := by exact prefixLift 1553776
  have htrace : WordTrace (prefixWord ++ tailWord_1553776) baseStart_1553776 baseEnd_1553776 := by
    simpa [prefixWord, tailWord_1553776, baseEnd_1553776] using wordTrace_append hprefix tailTrace_1553776
  have hstable : (prefixWord ++ tailWord_1553776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553776).length < 2 ^ (prefixWord ++ tailWord_1553776).sum := by decide
  have hdescent : baseEnd_1553776 < baseStart_1553776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553787 : List Nat := [1, 1, 1, 1, 1, 6, 10]
def baseStart_1553787 : Nat := 118140960795 + 1553787 * 2 ^ 59
def prefixEnd_1553787 : Nat := 4983230072969 + 3 ^ 40 * 1553787 * 2
def baseEnd_1553787 : Nat := 39399484726302100489717

theorem tailTrace_1553787 : CollatzResearch.WordTrace tailWord_1553787 prefixEnd_1553787 39399484726302100489717 := by
  unfold tailWord_1553787
  simp only [CollatzResearch.WordTrace]
  refine ⟨56671267621902539537867615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37780845081268359691911743 56671267621902539537867615)
  ·
    refine ⟨85006901432853809306801423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56671267621902539537867615 85006901432853809306801423)
    ·
      refine ⟨127510352149280713960202135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85006901432853809306801423 127510352149280713960202135)
      ·
        refine ⟨191265528223921070940303203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127510352149280713960202135 191265528223921070940303203)
        ·
          refine ⟨286898292335881606410454805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191265528223921070940303203 286898292335881606410454805)
          ·
            refine ⟨13448357453244450300490069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 286898292335881606410454805 13448357453244450300490069)
            ·
              refine ⟨39399484726302100489717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13448357453244450300490069 39399484726302100489717)
              ·
                rfl

theorem cell21_1553787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 10].length) (baseStart_1553787 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1553787 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1553787 prefixEnd_1553787 := by exact prefixLift 1553787
  have htrace : WordTrace (prefixWord ++ tailWord_1553787) baseStart_1553787 baseEnd_1553787 := by
    simpa [prefixWord, tailWord_1553787, baseEnd_1553787] using wordTrace_append hprefix tailTrace_1553787
  have hstable : (prefixWord ++ tailWord_1553787).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553787).length < 2 ^ (prefixWord ++ tailWord_1553787).sum := by decide
  have hdescent : baseEnd_1553787 < baseStart_1553787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553821 : List Nat := [1, 4, 2, 1, 3, 1, 4, 5]
def baseStart_1553821 : Nat := 118140960795 + 1553821 * 2 ^ 59
def prefixEnd_1553821 : Nat := 4983230072969 + 3 ^ 40 * 1553821 * 2
def baseEnd_1553821 : Nat := 118201040599980800280239

theorem tailTrace_1553821 : CollatzResearch.WordTrace tailWord_1553821 prefixEnd_1553821 118201040599980800280239 := by
  unfold tailWord_1553821
  simp only [CollatzResearch.WordTrace]
  refine ⟨56672507703779363344605317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37781671802519575563070211 56672507703779363344605317)
  ·
    refine ⟨10626095194458630627113497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56672507703779363344605317 10626095194458630627113497)
    ·
      refine ⟨7969571395843972970335123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10626095194458630627113497 7969571395843972970335123)
      ·
        refine ⟨11954357093765959455502685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7969571395843972970335123 11954357093765959455502685)
        ·
          refine ⟨4482883910162234795813507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11954357093765959455502685 4482883910162234795813507)
          ·
            refine ⟨6724325865243352193720261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4482883910162234795813507 6724325865243352193720261)
            ·
              refine ⟨1260811099733128536322549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6724325865243352193720261 1260811099733128536322549)
              ·
                refine ⟨118201040599980800280239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1260811099733128536322549 118201040599980800280239)
                ·
                  rfl

theorem cell21_1553821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 5].length) (baseStart_1553821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1553821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1553821 prefixEnd_1553821 := by exact prefixLift 1553821
  have htrace : WordTrace (prefixWord ++ tailWord_1553821) baseStart_1553821 baseEnd_1553821 := by
    simpa [prefixWord, tailWord_1553821, baseEnd_1553821] using wordTrace_append hprefix tailTrace_1553821
  have hstable : (prefixWord ++ tailWord_1553821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553821).length < 2 ^ (prefixWord ++ tailWord_1553821).sum := by decide
  have hdescent : baseEnd_1553821 < baseStart_1553821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553858 : List Nat := [3, 5, 2, 1, 1, 1, 1, 3, 4]
def baseStart_1553858 : Nat := 118140960795 + 1553858 * 2 ^ 59
def prefixEnd_1553858 : Nat := 4983230072969 + 3 ^ 40 * 1553858 * 2
def baseEnd_1553858 : Nat := 354611565704038558723975

theorem tailTrace_1553858 : CollatzResearch.WordTrace tailWord_1553858 prefixEnd_1553858 354611565704038558723975 := by
  unfold tailWord_1553858
  simp only [CollatzResearch.WordTrace]
  refine ⟨14168464301161329665925557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37782571469763545775801485 14168464301161329665925557)
  ·
    refine ⟨1328293528233874656180521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14168464301161329665925557 1328293528233874656180521)
    ·
      refine ⟨996220146175405992135391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1328293528233874656180521 996220146175405992135391)
      ·
        refine ⟨1494330219263108988203087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 996220146175405992135391 1494330219263108988203087)
        ·
          refine ⟨2241495328894663482304631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1494330219263108988203087 2241495328894663482304631)
          ·
            refine ⟨3362242993341995223456947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2241495328894663482304631 3362242993341995223456947)
            ·
              refine ⟨5043364490012992835185421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3362242993341995223456947 5043364490012992835185421)
              ·
                refine ⟨1891261683754872313194533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5043364490012992835185421 1891261683754872313194533)
                ·
                  refine ⟨354611565704038558723975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1891261683754872313194533 354611565704038558723975)
                  ·
                    rfl

theorem cell21_1553858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_1553858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1553858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1553858 prefixEnd_1553858 := by exact prefixLift 1553858
  have htrace : WordTrace (prefixWord ++ tailWord_1553858) baseStart_1553858 baseEnd_1553858 := by
    simpa [prefixWord, tailWord_1553858, baseEnd_1553858] using wordTrace_append hprefix tailTrace_1553858
  have hstable : (prefixWord ++ tailWord_1553858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553858).length < 2 ^ (prefixWord ++ tailWord_1553858).sum := by decide
  have hdescent : baseEnd_1553858 < baseStart_1553858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553866 : List Nat := [3, 1, 2, 1, 2, 4, 1, 3, 4]
def baseStart_1553866 : Nat := 118140960795 + 1553866 * 2 ^ 59
def prefixEnd_1553866 : Nat := 4983230072969 + 3 ^ 40 * 1553866 * 2
def baseEnd_1553866 : Nat := 354613391413032322590625

theorem tailTrace_1553866 : CollatzResearch.WordTrace tailWord_1553866 prefixEnd_1553866 354613391413032322590625 := by
  unfold tailWord_1553866
  simp only [CollatzResearch.WordTrace]
  refine ⟨14168537247154084007498363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37782765992410890686662301 14168537247154084007498363)
  ·
    refine ⟨21252805870731126011247545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14168537247154084007498363 21252805870731126011247545)
    ·
      refine ⟨15939604403048344508435659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21252805870731126011247545 15939604403048344508435659)
      ·
        refine ⟨23909406604572516762653489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15939604403048344508435659 23909406604572516762653489)
        ·
          refine ⟨17932054953429387571990117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23909406604572516762653489 17932054953429387571990117)
          ·
            refine ⟨3362260303768010169748147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17932054953429387571990117 3362260303768010169748147)
            ·
              refine ⟨5043390455652015254622221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3362260303768010169748147 5043390455652015254622221)
              ·
                refine ⟨1891271420869505720483333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5043390455652015254622221 1891271420869505720483333)
                ·
                  refine ⟨354613391413032322590625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1891271420869505720483333 354613391413032322590625)
                  ·
                    rfl

theorem cell21_1553866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3, 4].length) (baseStart_1553866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1553866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1553866 prefixEnd_1553866 := by exact prefixLift 1553866
  have htrace : WordTrace (prefixWord ++ tailWord_1553866) baseStart_1553866 baseEnd_1553866 := by
    simpa [prefixWord, tailWord_1553866, baseEnd_1553866] using wordTrace_append hprefix tailTrace_1553866
  have hstable : (prefixWord ++ tailWord_1553866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553866).length < 2 ^ (prefixWord ++ tailWord_1553866).sum := by decide
  have hdescent : baseEnd_1553866 < baseStart_1553866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553990 : List Nat := [6, 1, 1, 1, 3, 1, 1, 7]
def baseStart_1553990 : Nat := 118140960795 + 1553990 * 2 ^ 59
def prefixEnd_1553990 : Nat := 4983230072969 + 3 ^ 40 * 1553990 * 2
def baseEnd_1553990 : Nat := 118213896634145220841235

theorem tailTrace_1553990 : CollatzResearch.WordTrace tailWord_1553990 prefixEnd_1553990 118213896634145220841235 := by
  unfold tailWord_1553990
  simp only [CollatzResearch.WordTrace]
  refine ⟨1771208488755222037734607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37785781093444736805004949 1771208488755222037734607)
  ·
    refine ⟨2656812733132833056601911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1771208488755222037734607 2656812733132833056601911)
    ·
      refine ⟨3985219099699249584902867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2656812733132833056601911 3985219099699249584902867)
      ·
        refine ⟨5977828649548874377354301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3985219099699249584902867 5977828649548874377354301)
        ·
          refine ⟨2241685743580827891507863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5977828649548874377354301 2241685743580827891507863)
          ·
            refine ⟨3362528615371241837261795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2241685743580827891507863 3362528615371241837261795)
            ·
              refine ⟨5043792923056862755892693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3362528615371241837261795 5043792923056862755892693)
              ·
                refine ⟨118213896634145220841235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5043792923056862755892693 118213896634145220841235)
                ·
                  rfl

theorem cell21_1553990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_1553990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1553990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1553990 prefixEnd_1553990 := by exact prefixLift 1553990
  have htrace : WordTrace (prefixWord ++ tailWord_1553990) baseStart_1553990 baseEnd_1553990 := by
    simpa [prefixWord, tailWord_1553990, baseEnd_1553990] using wordTrace_append hprefix tailTrace_1553990
  have hstable : (prefixWord ++ tailWord_1553990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553990).length < 2 ^ (prefixWord ++ tailWord_1553990).sum := by decide
  have hdescent : baseEnd_1553990 < baseStart_1553990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554021 : List Nat := [1, 3, 1, 3, 3, 2, 3, 2, 3]
def baseStart_1554021 : Nat := 118140960795 + 1554021 * 2 ^ 59
def prefixEnd_1554021 : Nat := 4983230072969 + 3 ^ 40 * 1554021 * 2
def baseEnd_1554021 : Nat := 354648764524786497506975

theorem tailTrace_1554021 : CollatzResearch.WordTrace tailWord_1554021 prefixEnd_1554021 354648764524786497506975 := by
  unfold tailWord_1554021
  simp only [CollatzResearch.WordTrace]
  refine ⟨56679802303054797501885917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37786534868703198334590611 56679802303054797501885917)
  ·
    refine ⟨21254925863645549063207219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56679802303054797501885917 21254925863645549063207219)
    ·
      refine ⟨31882388795468323594810829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21254925863645549063207219 31882388795468323594810829)
      ·
        refine ⟨11955895798300621348054061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31882388795468323594810829 11955895798300621348054061)
        ·
          refine ⟨4483460924362733005520273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11955895798300621348054061 4483460924362733005520273)
          ·
            refine ⟨3362595693272049754140205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4483460924362733005520273 3362595693272049754140205)
            ·
              refine ⟨1260973384977018657802577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3362595693272049754140205 1260973384977018657802577)
              ·
                refine ⟨945730038732763993351933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1260973384977018657802577 945730038732763993351933)
                ·
                  refine ⟨354648764524786497506975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 945730038732763993351933 354648764524786497506975)
                  ·
                    rfl

theorem cell21_1554021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 2, 3].length) (baseStart_1554021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1554021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1554021 prefixEnd_1554021 := by exact prefixLift 1554021
  have htrace : WordTrace (prefixWord ++ tailWord_1554021) baseStart_1554021 baseEnd_1554021 := by
    simpa [prefixWord, tailWord_1554021, baseEnd_1554021] using wordTrace_append hprefix tailTrace_1554021
  have hstable : (prefixWord ++ tailWord_1554021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554021).length < 2 ^ (prefixWord ++ tailWord_1554021).sum := by decide
  have hdescent : baseEnd_1554021 < baseStart_1554021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554032 : List Nat := [2, 1, 1, 1, 6, 2, 2, 6]
def baseStart_1554032 : Nat := 118140960795 + 1554032 * 2 ^ 59
def prefixEnd_1554032 : Nat := 4983230072969 + 3 ^ 40 * 1554032 * 2
def baseEnd_1554032 : Nat := 118217091624884307607873

theorem tailTrace_1554032 : CollatzResearch.WordTrace tailWord_1554032 prefixEnd_1554032 118217091624884307607873 := by
  unfold tailWord_1554032
  simp only [CollatzResearch.WordTrace]
  refine ⟨28340101753007473190268175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37786802337343297587024233 28340101753007473190268175)
  ·
    refine ⟨42510152629511209785402263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28340101753007473190268175 42510152629511209785402263)
    ·
      refine ⟨63765228944266814678103395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42510152629511209785402263 63765228944266814678103395)
      ·
        refine ⟨95647843416400222017155093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63765228944266814678103395 95647843416400222017155093)
        ·
          refine ⟨4483492660143760407054145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 95647843416400222017155093 4483492660143760407054145)
          ·
            refine ⟨3362619495107820305290609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4483492660143760407054145 3362619495107820305290609)
            ·
              refine ⟨2521964621330865228967957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3362619495107820305290609 2521964621330865228967957)
              ·
                refine ⟨118217091624884307607873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2521964621330865228967957 118217091624884307607873)
                ·
                  rfl

theorem cell21_1554032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 6].length) (baseStart_1554032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1554032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1554032 prefixEnd_1554032 := by exact prefixLift 1554032
  have htrace : WordTrace (prefixWord ++ tailWord_1554032) baseStart_1554032 baseEnd_1554032 := by
    simpa [prefixWord, tailWord_1554032, baseEnd_1554032] using wordTrace_append hprefix tailTrace_1554032
  have hstable : (prefixWord ++ tailWord_1554032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554032).length < 2 ^ (prefixWord ++ tailWord_1554032).sum := by decide
  have hdescent : baseEnd_1554032 < baseStart_1554032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554080 : List Nat := [2, 1, 1, 4, 3, 2, 1, 4, 3]
def baseStart_1554080 : Nat := 118140960795 + 1554080 * 2 ^ 59
def prefixEnd_1554080 : Nat := 4983230072969 + 3 ^ 40 * 1554080 * 2
def baseEnd_1554080 : Nat := 354662229128615506023521

theorem tailTrace_1554080 : CollatzResearch.WordTrace tailWord_1554080 prefixEnd_1554080 354662229128615506023521 := by
  unfold tailWord_1554080
  simp only [CollatzResearch.WordTrace]
  refine ⟨28340977104920525289141847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37787969473227367052189129 28340977104920525289141847)
  ·
    refine ⟨42511465657380787933712771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28340977104920525289141847 42511465657380787933712771)
    ·
      refine ⟨63767198486071181900569157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42511465657380787933712771 63767198486071181900569157)
      ·
        refine ⟨11956349716138346606356717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63767198486071181900569157 11956349716138346606356717)
        ·
          refine ⟨4483631143551879977383769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11956349716138346606356717 4483631143551879977383769)
          ·
            refine ⟨3362723357663909983037827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4483631143551879977383769 3362723357663909983037827)
            ·
              refine ⟨5044085036495864974556741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3362723357663909983037827 5044085036495864974556741)
              ·
                refine ⟨945765944342974682729389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5044085036495864974556741 945765944342974682729389)
                ·
                  refine ⟨354662229128615506023521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 945765944342974682729389 354662229128615506023521)
                  ·
                    rfl

theorem cell21_1554080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 4, 3].length) (baseStart_1554080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1554080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1554080 prefixEnd_1554080 := by exact prefixLift 1554080
  have htrace : WordTrace (prefixWord ++ tailWord_1554080) baseStart_1554080 baseEnd_1554080 := by
    simpa [prefixWord, tailWord_1554080, baseEnd_1554080] using wordTrace_append hprefix tailTrace_1554080
  have hstable : (prefixWord ++ tailWord_1554080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554080).length < 2 ^ (prefixWord ++ tailWord_1554080).sum := by decide
  have hdescent : baseEnd_1554080 < baseStart_1554080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554125 : List Nat := [1, 6, 2, 1, 1, 2, 8]
def baseStart_1554125 : Nat := 118140960795 + 1554125 * 2 ^ 59
def prefixEnd_1554125 : Nat := 4983230072969 + 3 ^ 40 * 1554125 * 2
def baseEnd_1554125 : Nat := 39408055415745047530381

theorem tailTrace_1554125 : CollatzResearch.WordTrace tailWord_1554125 prefixEnd_1554125 39408055415745047530381 := by
  unfold tailWord_1554125
  simp only [CollatzResearch.WordTrace]
  refine ⟨56683595494678023263671829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37789063663118682175781219 56683595494678023263671829)
  ·
    refine ⟨2657043538813032340484617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 56683595494678023263671829 2657043538813032340484617)
    ·
      refine ⟨1992782654109774255363463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2657043538813032340484617 1992782654109774255363463)
      ·
        refine ⟨2989173981164661383045195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1992782654109774255363463 2989173981164661383045195)
        ·
          refine ⟨4483760971746992074567793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2989173981164661383045195 4483760971746992074567793)
          ·
            refine ⟨3362820728810244055925845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4483760971746992074567793 3362820728810244055925845)
            ·
              refine ⟨39408055415745047530381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3362820728810244055925845 39408055415745047530381)
              ·
                rfl

theorem cell21_1554125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 8].length) (baseStart_1554125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1554125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1554125 prefixEnd_1554125 := by exact prefixLift 1554125
  have htrace : WordTrace (prefixWord ++ tailWord_1554125) baseStart_1554125 baseEnd_1554125 := by
    simpa [prefixWord, tailWord_1554125, baseEnd_1554125] using wordTrace_append hprefix tailTrace_1554125
  have hstable : (prefixWord ++ tailWord_1554125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554125).length < 2 ^ (prefixWord ++ tailWord_1554125).sum := by decide
  have hdescent : baseEnd_1554125 < baseStart_1554125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554260 : List Nat := [2, 4, 1, 1, 3, 1, 3, 6]
def baseStart_1554260 : Nat := 118140960795 + 1554260 * 2 ^ 59
def prefixEnd_1554260 : Nat := 4983230072969 + 3 ^ 40 * 1554260 * 2
def baseEnd_1554260 : Nat := 118234435860325064341051

theorem tailTrace_1554260 : CollatzResearch.WordTrace tailWord_1554260 prefixEnd_1554260 118234435860325064341051 := by
  unfold tailWord_1554260
  simp only [CollatzResearch.WordTrace]
  refine ⟨28344259674594470659918117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37792346232792627546557489 28344259674594470659918117)
  ·
    refine ⟨5314548688986463248734647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28344259674594470659918117 5314548688986463248734647)
    ·
      refine ⟨7971823033479694873101971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5314548688986463248734647 7971823033479694873101971)
      ·
        refine ⟨11957734550219542309652957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7971823033479694873101971 11957734550219542309652957)
        ·
          refine ⟨4484150456332328366119859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11957734550219542309652957 4484150456332328366119859)
          ·
            refine ⟨6726225684498492549179789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4484150456332328366119859 6726225684498492549179789)
            ·
              refine ⟨2522334631686934705942421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6726225684498492549179789 2522334631686934705942421)
              ·
                refine ⟨118234435860325064341051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2522334631686934705942421 118234435860325064341051)
                ·
                  rfl

theorem cell21_1554260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 6].length) (baseStart_1554260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1554260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1554260 prefixEnd_1554260 := by exact prefixLift 1554260
  have htrace : WordTrace (prefixWord ++ tailWord_1554260) baseStart_1554260 baseEnd_1554260 := by
    simpa [prefixWord, tailWord_1554260, baseEnd_1554260] using wordTrace_append hprefix tailTrace_1554260
  have hstable : (prefixWord ++ tailWord_1554260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554260).length < 2 ^ (prefixWord ++ tailWord_1554260).sum := by decide
  have hdescent : baseEnd_1554260 < baseStart_1554260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554288 : List Nat := [2, 1, 1, 1, 4, 1, 1, 4, 6]
def baseStart_1554288 : Nat := 118140960795 + 1554288 * 2 ^ 59
def prefixEnd_1554288 : Nat := 4983230072969 + 3 ^ 40 * 1554288 * 2
def baseEnd_1554288 : Nat := 354709697562453366556429

theorem tailTrace_1554288 : CollatzResearch.WordTrace tailWord_1554288 prefixEnd_1554288 354709697562453366556429 := by
  unfold tailWord_1554288
  simp only [CollatzResearch.WordTrace]
  refine ⟨28344770296543751050927759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37793027062058334734570345 28344770296543751050927759)
  ·
    refine ⟨42517155444815626576391639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28344770296543751050927759 42517155444815626576391639)
    ·
      refine ⟨63775733167223439864587459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42517155444815626576391639 63775733167223439864587459)
      ·
        refine ⟨95663599750835159796881189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63775733167223439864587459 95663599750835159796881189)
        ·
          refine ⟨17936924953281592461915223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95663599750835159796881189 17936924953281592461915223)
          ·
            refine ⟨26905387429922388692872835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17936924953281592461915223 26905387429922388692872835)
            ·
              refine ⟨40358081144883583039309253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26905387429922388692872835 40358081144883583039309253)
              ·
                refine ⟨7567140214665671819870485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40358081144883583039309253 7567140214665671819870485)
                ·
                  refine ⟨354709697562453366556429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7567140214665671819870485 354709697562453366556429)
                  ·
                    rfl

theorem cell21_1554288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 6].length) (baseStart_1554288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1554288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1554288 prefixEnd_1554288 := by exact prefixLift 1554288
  have htrace : WordTrace (prefixWord ++ tailWord_1554288) baseStart_1554288 baseEnd_1554288 := by
    simpa [prefixWord, tailWord_1554288, baseEnd_1554288] using wordTrace_append hprefix tailTrace_1554288
  have hstable : (prefixWord ++ tailWord_1554288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554288).length < 2 ^ (prefixWord ++ tailWord_1554288).sum := by decide
  have hdescent : baseEnd_1554288 < baseStart_1554288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554460 : List Nat := [2, 2, 3, 1, 3, 2, 2, 3, 3]
def baseStart_1554460 : Nat := 118140960795 + 1554460 * 2 ^ 59
def prefixEnd_1554460 : Nat := 4983230072969 + 3 ^ 40 * 1554460 * 2
def baseEnd_1554460 : Nat := 354748950305819289689411

theorem tailTrace_1554460 : CollatzResearch.WordTrace tailWord_1554460 prefixEnd_1554460 354748950305819289689411 := by
  unfold tailWord_1554460
  simp only [CollatzResearch.WordTrace]
  refine ⟨28347906974232187738558417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37797209298976250318077889 28347906974232187738558417)
  ·
    refine ⟨21260930230674140803918813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28347906974232187738558417 21260930230674140803918813)
    ·
      refine ⟨7972848836502802801469555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21260930230674140803918813 7972848836502802801469555)
      ·
        refine ⟨11959273254754204202204333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7972848836502802801469555 11959273254754204202204333)
        ·
          refine ⟨4484727470532826575826625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11959273254754204202204333 4484727470532826575826625)
          ·
            refine ⟨3363545602899619931869969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4484727470532826575826625 3363545602899619931869969)
            ·
              refine ⟨2522659202174714948902477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3363545602899619931869969 2522659202174714948902477)
              ·
                refine ⟨945997200815518105838429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2522659202174714948902477 945997200815518105838429)
                ·
                  refine ⟨354748950305819289689411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 945997200815518105838429 354748950305819289689411)
                  ·
                    rfl

theorem cell21_1554460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 3, 3].length) (baseStart_1554460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1554460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1554460 prefixEnd_1554460 := by exact prefixLift 1554460
  have htrace : WordTrace (prefixWord ++ tailWord_1554460) baseStart_1554460 baseEnd_1554460 := by
    simpa [prefixWord, tailWord_1554460, baseEnd_1554460] using wordTrace_append hprefix tailTrace_1554460
  have hstable : (prefixWord ++ tailWord_1554460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554460).length < 2 ^ (prefixWord ++ tailWord_1554460).sum := by decide
  have hdescent : baseEnd_1554460 < baseStart_1554460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554474 : List Nat := [3, 1, 4, 1, 2, 1, 3, 2, 4]
def baseStart_1554474 : Nat := 118140960795 + 1554474 * 2 ^ 59
def prefixEnd_1554474 : Nat := 4983230072969 + 3 ^ 40 * 1554474 * 2
def baseEnd_1554474 : Nat := 354752145296558376456049

theorem tailTrace_1554474 : CollatzResearch.WordTrace tailWord_1554474 prefixEnd_1554474 354752145296558376456049 := by
  unfold tailWord_1554474
  simp only [CollatzResearch.WordTrace]
  refine ⟨14174081142603413967031619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37797549713609103912084317 14174081142603413967031619)
  ·
    refine ⟨21261121713905120950547429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14174081142603413967031619 21261121713905120950547429)
    ·
      refine ⟨3986460321357210178227643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21261121713905120950547429 3986460321357210178227643)
      ·
        refine ⟨5979690482035815267341465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3986460321357210178227643 5979690482035815267341465)
        ·
          refine ⟨4484767861526861450506099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5979690482035815267341465 4484767861526861450506099)
          ·
            refine ⟨6727151792290292175759149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4484767861526861450506099 6727151792290292175759149)
            ·
              refine ⟨2522681922108859565909681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6727151792290292175759149 2522681922108859565909681)
              ·
                refine ⟨1892011441581644674432261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2522681922108859565909681 1892011441581644674432261)
                ·
                  refine ⟨354752145296558376456049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1892011441581644674432261 354752145296558376456049)
                  ·
                    rfl

theorem cell21_1554474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2, 4].length) (baseStart_1554474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1554474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1554474 prefixEnd_1554474 := by exact prefixLift 1554474
  have htrace : WordTrace (prefixWord ++ tailWord_1554474) baseStart_1554474 baseEnd_1554474 := by
    simpa [prefixWord, tailWord_1554474, baseEnd_1554474] using wordTrace_append hprefix tailTrace_1554474
  have hstable : (prefixWord ++ tailWord_1554474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554474).length < 2 ^ (prefixWord ++ tailWord_1554474).sum := by decide
  have hdescent : baseEnd_1554474 < baseStart_1554474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554519 : List Nat := [1, 1, 3, 2, 2, 1, 5, 3, 3]
def baseStart_1554519 : Nat := 118140960795 + 1554519 * 2 ^ 59
def prefixEnd_1554519 : Nat := 4983230072969 + 3 ^ 40 * 1554519 * 2
def baseEnd_1554519 : Nat := 354762414909648298205957

theorem tailTrace_1554519 : CollatzResearch.WordTrace tailWord_1554519 prefixEnd_1554519 354762414909648298205957 := by
  unfold tailWord_1554519
  simp only [CollatzResearch.WordTrace]
  refine ⟨56697965855250628553514611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37798643903500419035676407 56697965855250628553514611)
  ·
    refine ⟨85046948782875942830271917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56697965855250628553514611 85046948782875942830271917)
    ·
      refine ⟨31892605793578478561351969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85046948782875942830271917 31892605793578478561351969)
      ·
        refine ⟨23919454345183858921013977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31892605793578478561351969 23919454345183858921013977)
        ·
          refine ⟨17939590758887894190760483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23919454345183858921013977 17939590758887894190760483)
          ·
            refine ⟨26909386138331841286140725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17939590758887894190760483 26909386138331841286140725)
            ·
              refine ⟨2522754950468610120575693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26909386138331841286140725 2522754950468610120575693)
              ·
                refine ⟨946033106425728795215885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2522754950468610120575693 946033106425728795215885)
                ·
                  refine ⟨354762414909648298205957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 946033106425728795215885 354762414909648298205957)
                  ·
                    rfl

theorem cell21_1554519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 3, 3].length) (baseStart_1554519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1554519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1554519 prefixEnd_1554519 := by exact prefixLift 1554519
  have htrace : WordTrace (prefixWord ++ tailWord_1554519) baseStart_1554519 baseEnd_1554519 := by
    simpa [prefixWord, tailWord_1554519, baseEnd_1554519] using wordTrace_append hprefix tailTrace_1554519
  have hstable : (prefixWord ++ tailWord_1554519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554519).length < 2 ^ (prefixWord ++ tailWord_1554519).sum := by decide
  have hdescent : baseEnd_1554519 < baseStart_1554519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554550 : List Nat := [5, 1, 1, 2, 1, 3, 1, 3, 4]
def baseStart_1554550 : Nat := 118140960795 + 1554550 * 2 ^ 59
def prefixEnd_1554550 : Nat := 4983230072969 + 3 ^ 40 * 1554550 * 2
def baseEnd_1554550 : Nat := 354769489531999133189227

theorem tailTrace_1554550 : CollatzResearch.WordTrace tailWord_1554550 prefixEnd_1554550 354769489531999133189227 := by
  unfold tailWord_1554550
  simp only [CollatzResearch.WordTrace]
  refine ⟨3543693532383645052993319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37799397678758880565262069 3543693532383645052993319)
  ·
    refine ⟨5315540298575467579489979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3543693532383645052993319 5315540298575467579489979)
    ·
      refine ⟨7973310447863201369234969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5315540298575467579489979 7973310447863201369234969)
      ·
        refine ⟨5979982835897401026926227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7973310447863201369234969 5979982835897401026926227)
        ·
          refine ⟨8969974253846101540389341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5979982835897401026926227 8969974253846101540389341)
          ·
            refine ⟨3363740345192288077646003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8969974253846101540389341 3363740345192288077646003)
            ·
              refine ⟨5045610517788432116469005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3363740345192288077646003 5045610517788432116469005)
              ·
                refine ⟨1892103944170662043675877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5045610517788432116469005 1892103944170662043675877)
                ·
                  refine ⟨354769489531999133189227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1892103944170662043675877 354769489531999133189227)
                  ·
                    rfl

theorem cell21_1554550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_1554550 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1554550 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1554550 prefixEnd_1554550 := by exact prefixLift 1554550
  have htrace : WordTrace (prefixWord ++ tailWord_1554550) baseStart_1554550 baseEnd_1554550 := by
    simpa [prefixWord, tailWord_1554550, baseEnd_1554550] using wordTrace_append hprefix tailTrace_1554550
  have hstable : (prefixWord ++ tailWord_1554550).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554550).length < 2 ^ (prefixWord ++ tailWord_1554550).sum := by decide
  have hdescent : baseEnd_1554550 < baseStart_1554550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554789 : List Nat := [1, 3, 1, 3, 1, 3, 1, 1, 7]
def baseStart_1554789 : Nat := 118140960795 + 1554789 * 2 ^ 59
def prefixEnd_1554789 : Nat := 4983230072969 + 3 ^ 40 * 1554789 * 2
def baseEnd_1554789 : Nat := 354824032588187828705405

theorem tailTrace_1554789 : CollatzResearch.WordTrace tailWord_1554789 prefixEnd_1554789 354824032588187828705405 := by
  unfold tailWord_1554789
  simp only [CollatzResearch.WordTrace]
  refine ⟨56707813564272464665843421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37805209042848309777228947 56707813564272464665843421)
  ·
    refine ⟨21265430086602174249691283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56707813564272464665843421 21265430086602174249691283)
    ·
      refine ⟨31898145129903261374536925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21265430086602174249691283 31898145129903261374536925)
      ·
        refine ⟨11961804423713723015451347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31898145129903261374536925 11961804423713723015451347)
        ·
          refine ⟨17942706635570584523177021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11961804423713723015451347 17942706635570584523177021)
          ·
            refine ⟨6728514988338969196191383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17942706635570584523177021 6728514988338969196191383)
            ·
              refine ⟨10092772482508453794287075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6728514988338969196191383 10092772482508453794287075)
              ·
                refine ⟨15139158723762680691430613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10092772482508453794287075 15139158723762680691430613)
                ·
                  refine ⟨354824032588187828705405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15139158723762680691430613 354824032588187828705405)
                  ·
                    rfl

theorem cell21_1554789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_1554789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1554789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1554789 prefixEnd_1554789 := by exact prefixLift 1554789
  have htrace : WordTrace (prefixWord ++ tailWord_1554789) baseStart_1554789 baseEnd_1554789 := by
    simpa [prefixWord, tailWord_1554789, baseEnd_1554789] using wordTrace_append hprefix tailTrace_1554789
  have hstable : (prefixWord ++ tailWord_1554789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554789).length < 2 ^ (prefixWord ++ tailWord_1554789).sum := by decide
  have hdescent : baseEnd_1554789 < baseStart_1554789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554792 : List Nat := [2, 1, 4, 2, 2, 2, 3, 5]
def baseStart_1554792 : Nat := 118140960795 + 1554792 * 2 ^ 59
def prefixEnd_1554792 : Nat := 4983230072969 + 3 ^ 40 * 1554792 * 2
def baseEnd_1554792 : Nat := 118274905743020163385133

theorem tailTrace_1554792 : CollatzResearch.WordTrace tailWord_1554792 prefixEnd_1554792 118274905743020163385133 := by
  unfold tailWord_1554792
  simp only [CollatzResearch.WordTrace]
  refine ⟨28353961491630798089101315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37805281988841064118801753 28353961491630798089101315)
  ·
    refine ⟨42530942237446197133651973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28353961491630798089101315 42530942237446197133651973)
    ·
      refine ⟨7974551669521161962559745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42530942237446197133651973 7974551669521161962559745)
      ·
        refine ⟨5980913752140871471919809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7974551669521161962559745 5980913752140871471919809)
        ·
          refine ⟨4485685314105653603939857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5980913752140871471919809 4485685314105653603939857)
          ·
            refine ⟨3364263985579240202954893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4485685314105653603939857 3364263985579240202954893)
            ·
              refine ⟨1261598994592215076108085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3364263985579240202954893 1261598994592215076108085)
              ·
                refine ⟨118274905743020163385133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1261598994592215076108085 118274905743020163385133)
                ·
                  rfl

theorem cell21_1554792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 5].length) (baseStart_1554792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1554792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1554792 prefixEnd_1554792 := by exact prefixLift 1554792
  have htrace : WordTrace (prefixWord ++ tailWord_1554792) baseStart_1554792 baseEnd_1554792 := by
    simpa [prefixWord, tailWord_1554792, baseEnd_1554792] using wordTrace_append hprefix tailTrace_1554792
  have hstable : (prefixWord ++ tailWord_1554792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554792).length < 2 ^ (prefixWord ++ tailWord_1554792).sum := by decide
  have hdescent : baseEnd_1554792 < baseStart_1554792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554803 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 8]
def baseStart_1554803 : Nat := 118140960795 + 1554803 * 2 ^ 59
def prefixEnd_1554803 : Nat := 4983230072969 + 3 ^ 40 * 1554803 * 2
def baseEnd_1554803 : Nat := 354827227578926915472043

theorem tailTrace_1554803 : CollatzResearch.WordTrace tailWord_1554803 prefixEnd_1554803 354827227578926915472043 := by
  unfold tailWord_1554803
  simp only [CollatzResearch.WordTrace]
  refine ⟨56708324186221745056853063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37805549457481163371235375 56708324186221745056853063)
  ·
    refine ⟨85062486279332617585279595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56708324186221745056853063 85062486279332617585279595)
    ·
      refine ⟨127593729418998926377919393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85062486279332617585279595 127593729418998926377919393)
      ·
        refine ⟨95695297064249194783439545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127593729418998926377919393 95695297064249194783439545)
        ·
          refine ⟨71771472798186896087579659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95695297064249194783439545 71771472798186896087579659)
          ·
            refine ⟨107657209197280344131369489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71771472798186896087579659 107657209197280344131369489)
            ·
              refine ⟨80742906897960258098527117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107657209197280344131369489 80742906897960258098527117)
              ·
                refine ⟨30278590086735096786947669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80742906897960258098527117 30278590086735096786947669)
                ·
                  refine ⟨354827227578926915472043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30278590086735096786947669 354827227578926915472043)
                  ·
                    rfl

theorem cell21_1554803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 8].length) (baseStart_1554803 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1554803 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1554803 prefixEnd_1554803 := by exact prefixLift 1554803
  have htrace : WordTrace (prefixWord ++ tailWord_1554803) baseStart_1554803 baseEnd_1554803 := by
    simpa [prefixWord, tailWord_1554803, baseEnd_1554803] using wordTrace_append hprefix tailTrace_1554803
  have hstable : (prefixWord ++ tailWord_1554803).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554803).length < 2 ^ (prefixWord ++ tailWord_1554803).sum := by decide
  have hdescent : baseEnd_1554803 < baseStart_1554803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554820 : List Nat := [2, 3, 2, 1, 1, 2, 3, 1, 6]
def baseStart_1554820 : Nat := 118140960795 + 1554820 * 2 ^ 59
def prefixEnd_1554820 : Nat := 4983230072969 + 3 ^ 40 * 1554820 * 2
def baseEnd_1554820 : Nat := 354831107210538663688675

theorem tailTrace_1554820 : CollatzResearch.WordTrace tailWord_1554820 prefixEnd_1554820 354831107210538663688675 := by
  unfold tailWord_1554820
  simp only [CollatzResearch.WordTrace]
  refine ⟨28354472113580078480110957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37805962818106771306814609 28354472113580078480110957)
  ·
    refine ⟨10632927042592529430041609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28354472113580078480110957 10632927042592529430041609)
    ·
      refine ⟨7974695281944397072531207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10632927042592529430041609 7974695281944397072531207)
      ·
        refine ⟨11962042922916595608796811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7974695281944397072531207 11962042922916595608796811)
        ·
          refine ⟨17943064384374893413195217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11962042922916595608796811 17943064384374893413195217)
          ·
            refine ⟨13457298288281170059896413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17943064384374893413195217 13457298288281170059896413)
            ·
              refine ⟨5046486858105438772461155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13457298288281170059896413 5046486858105438772461155)
              ·
                refine ⟨7569730287158158158691733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5046486858105438772461155 7569730287158158158691733)
                ·
                  refine ⟨354831107210538663688675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7569730287158158158691733 354831107210538663688675)
                  ·
                    rfl

theorem cell21_1554820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_1554820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1554820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1554820 prefixEnd_1554820 := by exact prefixLift 1554820
  have htrace : WordTrace (prefixWord ++ tailWord_1554820) baseStart_1554820 baseEnd_1554820 := by
    simpa [prefixWord, tailWord_1554820, baseEnd_1554820] using wordTrace_append hprefix tailTrace_1554820
  have hstable : (prefixWord ++ tailWord_1554820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554820).length < 2 ^ (prefixWord ++ tailWord_1554820).sum := by decide
  have hdescent : baseEnd_1554820 < baseStart_1554820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554851 : List Nat := [1, 1, 1, 4, 1, 4, 4, 5]
def baseStart_1554851 : Nat := 118140960795 + 1554851 * 2 ^ 59
def prefixEnd_1554851 : Nat := 4983230072969 + 3 ^ 40 * 1554851 * 2
def baseEnd_1554851 : Nat := 118279393944296499557315

theorem tailTrace_1554851 : CollatzResearch.WordTrace tailWord_1554851 prefixEnd_1554851 118279393944296499557315 := by
  unfold tailWord_1554851
  simp only [CollatzResearch.WordTrace]
  refine ⟨56710074890047849254600407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37806716593365232836400271 56710074890047849254600407)
  ·
    refine ⟨85065112335071773881900611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56710074890047849254600407 85065112335071773881900611)
    ·
      refine ⟨127597668502607660822850917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85065112335071773881900611 127597668502607660822850917)
      ·
        refine ⟨23924562844238936404284547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127597668502607660822850917 23924562844238936404284547)
        ·
          refine ⟨35886844266358404606426821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23924562844238936404284547 35886844266358404606426821)
          ·
            refine ⟨6728783299942200863705029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35886844266358404606426821 6728783299942200863705029)
            ·
              refine ⟨1261646868739162661944693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6728783299942200863705029 1261646868739162661944693)
              ·
                refine ⟨118279393944296499557315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1261646868739162661944693 118279393944296499557315)
                ·
                  rfl

theorem cell21_1554851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 5].length) (baseStart_1554851 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1554851 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1554851 prefixEnd_1554851 := by exact prefixLift 1554851
  have htrace : WordTrace (prefixWord ++ tailWord_1554851) baseStart_1554851 baseEnd_1554851 := by
    simpa [prefixWord, tailWord_1554851, baseEnd_1554851] using wordTrace_append hprefix tailTrace_1554851
  have hstable : (prefixWord ++ tailWord_1554851).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554851).length < 2 ^ (prefixWord ++ tailWord_1554851).sum := by decide
  have hdescent : baseEnd_1554851 < baseStart_1554851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554930 : List Nat := [3, 2, 1, 4, 2, 1, 2, 2, 4]
def baseStart_1554930 : Nat := 118140960795 + 1554930 * 2 ^ 59
def prefixEnd_1554930 : Nat := 4983230072969 + 3 ^ 40 * 1554930 * 2
def baseEnd_1554930 : Nat := 354856210709202916855117

theorem tailTrace_1554930 : CollatzResearch.WordTrace tailWord_1554930 prefixEnd_1554930 354856210709202916855117 := by
  unfold tailWord_1554930
  simp only [CollatzResearch.WordTrace]
  refine ⟨14178239064190411436681561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37808637504507763831150829 14178239064190411436681561)
  ·
    refine ⟨10633679298142808577511171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14178239064190411436681561 10633679298142808577511171)
    ·
      refine ⟨15950518947214212866266757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10633679298142808577511171 15950518947214212866266757)
      ·
        refine ⟨2990722302602664912425017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15950518947214212866266757 2990722302602664912425017)
        ·
          refine ⟨2243041726951998684318763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2990722302602664912425017 2243041726951998684318763)
          ·
            refine ⟨3364562590427998026478145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2243041726951998684318763 3364562590427998026478145)
            ·
              refine ⟨2523421942820998519858609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3364562590427998026478145 2523421942820998519858609)
              ·
                refine ⟨1892566457115748889893957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2523421942820998519858609 1892566457115748889893957)
                ·
                  refine ⟨354856210709202916855117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1892566457115748889893957 354856210709202916855117)
                  ·
                    rfl

theorem cell21_1554930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_1554930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1554930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1554930 prefixEnd_1554930 := by exact prefixLift 1554930
  have htrace : WordTrace (prefixWord ++ tailWord_1554930) baseStart_1554930 baseEnd_1554930 := by
    simpa [prefixWord, tailWord_1554930, baseEnd_1554930] using wordTrace_append hprefix tailTrace_1554930
  have hstable : (prefixWord ++ tailWord_1554930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554930).length < 2 ^ (prefixWord ++ tailWord_1554930).sum := by decide
  have hdescent : baseEnd_1554930 < baseStart_1554930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554941 : List Nat := [1, 4, 1, 1, 1, 3, 2, 3, 5]
def baseStart_1554941 : Nat := 118140960795 + 1554941 * 2 ^ 59
def prefixEnd_1554941 : Nat := 4983230072969 + 3 ^ 40 * 1554941 * 2
def baseEnd_1554941 : Nat := 354858721059069342171761

theorem tailTrace_1554941 : CollatzResearch.WordTrace tailWord_1554941 prefixEnd_1554941 354858721059069342171761 := by
  unfold tailWord_1554941
  simp only [CollatzResearch.WordTrace]
  refine ⟨56713357459721794625376677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37808904973147863083584451 56713357459721794625376677)
  ·
    refine ⟨10633754523697836492258127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56713357459721794625376677 10633754523697836492258127)
    ·
      refine ⟨15950631785546754738387191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10633754523697836492258127 15950631785546754738387191)
      ·
        refine ⟨23925947678320132107580787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15950631785546754738387191 23925947678320132107580787)
        ·
          refine ⟨35888921517480198161371181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23925947678320132107580787 35888921517480198161371181)
          ·
            refine ⟨13458345569055074310514193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35888921517480198161371181 13458345569055074310514193)
            ·
              refine ⟨10093759176791305732885645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13458345569055074310514193 10093759176791305732885645)
              ·
                refine ⟨3785159691296739649832117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10093759176791305732885645 3785159691296739649832117)
                ·
                  refine ⟨354858721059069342171761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3785159691296739649832117 354858721059069342171761)
                  ·
                    rfl

theorem cell21_1554941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_1554941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1554941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1554941 prefixEnd_1554941 := by exact prefixLift 1554941
  have htrace : WordTrace (prefixWord ++ tailWord_1554941) baseStart_1554941 baseEnd_1554941 := by
    simpa [prefixWord, tailWord_1554941, baseEnd_1554941] using wordTrace_append hprefix tailTrace_1554941
  have hstable : (prefixWord ++ tailWord_1554941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554941).length < 2 ^ (prefixWord ++ tailWord_1554941).sum := by decide
  have hdescent : baseEnd_1554941 < baseStart_1554941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554958 : List Nat := [4, 1, 1, 2, 3, 2, 1, 2, 5]
def baseStart_1554958 : Nat := 118140960795 + 1554958 * 2 ^ 59
def prefixEnd_1554958 : Nat := 4983230072969 + 3 ^ 40 * 1554958 * 2
def baseEnd_1554958 : Nat := 354862600690681090388393

theorem tailTrace_1554958 : CollatzResearch.WordTrace tailWord_1554958 prefixEnd_1554958 354862600690681090388393 := by
  unfold tailWord_1554958
  simp only [CollatzResearch.WordTrace]
  refine ⟨7089247187582525816093191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37809318333773471019163685 7089247187582525816093191)
  ·
    refine ⟨10633870781373788724139787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7089247187582525816093191 10633870781373788724139787)
    ·
      refine ⟨15950806172060683086209681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10633870781373788724139787 15950806172060683086209681)
      ·
        refine ⟨11963104629045512314657261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15950806172060683086209681 11963104629045512314657261)
        ·
          refine ⟨4486164235892067117996473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11963104629045512314657261 4486164235892067117996473)
          ·
            refine ⟨3364623176919050338497355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4486164235892067117996473 3364623176919050338497355)
            ·
              refine ⟨5046934765378575507746033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3364623176919050338497355 5046934765378575507746033)
              ·
                refine ⟨3785201074033931630809525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5046934765378575507746033 3785201074033931630809525)
                ·
                  refine ⟨354862600690681090388393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3785201074033931630809525 354862600690681090388393)
                  ·
                    rfl

theorem cell21_1554958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_1554958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1554958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1554958 prefixEnd_1554958 := by exact prefixLift 1554958
  have htrace : WordTrace (prefixWord ++ tailWord_1554958) baseStart_1554958 baseEnd_1554958 := by
    simpa [prefixWord, tailWord_1554958, baseEnd_1554958] using wordTrace_append hprefix tailTrace_1554958
  have hstable : (prefixWord ++ tailWord_1554958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554958).length < 2 ^ (prefixWord ++ tailWord_1554958).sum := by decide
  have hdescent : baseEnd_1554958 < baseStart_1554958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555031 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 8]
def baseStart_1555031 : Nat := 118140960795 + 1555031 * 2 ^ 59
def prefixEnd_1555031 : Nat := 4983230072969 + 3 ^ 40 * 1555031 * 2
def baseEnd_1555031 : Nat := 354879260285249185671577

theorem tailTrace_1555031 : CollatzResearch.WordTrace tailWord_1555031 prefixEnd_1555031 354879260285249185671577 := by
  unfold tailWord_1555031
  simp only [CollatzResearch.WordTrace]
  refine ⟨56716640029395739996152947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37811093352930493330768631 56716640029395739996152947)
  ·
    refine ⟨85074960044093609994229421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56716640029395739996152947 85074960044093609994229421)
    ·
      refine ⟨31903110016535103747836033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85074960044093609994229421 31903110016535103747836033)
      ·
        refine ⟨23927332512401327810877025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31903110016535103747836033 23927332512401327810877025)
        ·
          refine ⟨17945499384300995858157769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23927332512401327810877025 17945499384300995858157769)
          ·
            refine ⟨13459124538225746893618327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17945499384300995858157769 13459124538225746893618327)
            ·
              refine ⟨20188686807338620340427491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13459124538225746893618327 20188686807338620340427491)
              ·
                refine ⟨30283030211007930510641237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20188686807338620340427491 30283030211007930510641237)
                ·
                  refine ⟨354879260285249185671577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30283030211007930510641237 354879260285249185671577)
                  ·
                    rfl

theorem cell21_1555031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 8].length) (baseStart_1555031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1555031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1555031 prefixEnd_1555031 := by exact prefixLift 1555031
  have htrace : WordTrace (prefixWord ++ tailWord_1555031) baseStart_1555031 baseEnd_1555031 := by
    simpa [prefixWord, tailWord_1555031, baseEnd_1555031] using wordTrace_append hprefix tailTrace_1555031
  have hstable : (prefixWord ++ tailWord_1555031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555031).length < 2 ^ (prefixWord ++ tailWord_1555031).sum := by decide
  have hdescent : baseEnd_1555031 < baseStart_1555031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555065 : List Nat := [1, 2, 1, 3, 3, 2, 4, 1, 4]
def baseStart_1555065 : Nat := 118140960795 + 1555065 * 2 ^ 59
def prefixEnd_1555065 : Nat := 4983230072969 + 3 ^ 40 * 1555065 * 2
def baseEnd_1555065 : Nat := 354887019548472682104841

theorem tailTrace_1555065 : CollatzResearch.WordTrace tailWord_1555065 prefixEnd_1555065 354887019548472682104841 := by
  unfold tailWord_1555065
  simp only [CollatzResearch.WordTrace]
  refine ⟨56717880111272563802890649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37811920074181709201927099 56717880111272563802890649)
  ·
    refine ⟨42538410083454422852167987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56717880111272563802890649 42538410083454422852167987)
    ·
      refine ⟨63807615125181634278251981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42538410083454422852167987 63807615125181634278251981)
      ·
        refine ⟨23927855671943112854344493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63807615125181634278251981 23927855671943112854344493)
        ·
          refine ⟨8972945876978667320379185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23927855671943112854344493 8972945876978667320379185)
          ·
            refine ⟨6729709407734000490284389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8972945876978667320379185 6729709407734000490284389)
            ·
              refine ⟨1261820513950125091928323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6729709407734000490284389 1261820513950125091928323)
              ·
                refine ⟨1892730770925187637892485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1261820513950125091928323 1892730770925187637892485)
                ·
                  refine ⟨354887019548472682104841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1892730770925187637892485 354887019548472682104841)
                  ·
                    rfl

theorem cell21_1555065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 1, 4].length) (baseStart_1555065 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1555065 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1555065 prefixEnd_1555065 := by exact prefixLift 1555065
  have htrace : WordTrace (prefixWord ++ tailWord_1555065) baseStart_1555065 baseEnd_1555065 := by
    simpa [prefixWord, tailWord_1555065, baseEnd_1555065] using wordTrace_append hprefix tailTrace_1555065
  have hstable : (prefixWord ++ tailWord_1555065).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555065).length < 2 ^ (prefixWord ++ tailWord_1555065).sum := by decide
  have hdescent : baseEnd_1555065 < baseStart_1555065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555169 : List Nat := [1, 2, 3, 1, 4, 1, 1, 3, 5]
def baseStart_1555169 : Nat := 118140960795 + 1555169 * 2 ^ 59
def prefixEnd_1555169 : Nat := 4983230072969 + 3 ^ 40 * 1555169 * 2
def baseEnd_1555169 : Nat := 354910753765391612371295

theorem tailTrace_1555169 : CollatzResearch.WordTrace tailWord_1555169 prefixEnd_1555169 354910753765391612371295 := by
  unfold tailWord_1555169
  simp only [CollatzResearch.WordTrace]
  refine ⟨56721673302895789564676561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37814448868597193043117707 56721673302895789564676561)
  ·
    refine ⟨42541254977171842173507421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56721673302895789564676561 42541254977171842173507421)
    ·
      refine ⟨15952970616439440815065283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42541254977171842173507421 15952970616439440815065283)
      ·
        refine ⟨23929455924659161222597925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15952970616439440815065283 23929455924659161222597925)
        ·
          refine ⟨4486772985873592729237111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23929455924659161222597925 4486772985873592729237111)
          ·
            refine ⟨6730159478810389093855667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4486772985873592729237111 6730159478810389093855667)
            ·
              refine ⟨10095239218215583640783501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6730159478810389093855667 10095239218215583640783501)
              ·
                refine ⟨3785714706830843865293813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10095239218215583640783501 3785714706830843865293813)
                ·
                  refine ⟨354910753765391612371295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3785714706830843865293813 354910753765391612371295)
                  ·
                    rfl

theorem cell21_1555169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 5].length) (baseStart_1555169 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1555169 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1555169 prefixEnd_1555169 := by exact prefixLift 1555169
  have htrace : WordTrace (prefixWord ++ tailWord_1555169) baseStart_1555169 baseEnd_1555169 := by
    simpa [prefixWord, tailWord_1555169, baseEnd_1555169] using wordTrace_append hprefix tailTrace_1555169
  have hstable : (prefixWord ++ tailWord_1555169).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555169).length < 2 ^ (prefixWord ++ tailWord_1555169).sum := by decide
  have hdescent : baseEnd_1555169 < baseStart_1555169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555189 : List Nat := [1, 3, 6, 1, 1, 1, 1, 7]
def baseStart_1555189 : Nat := 118140960795 + 1555189 * 2 ^ 59
def prefixEnd_1555189 : Nat := 4983230072969 + 3 ^ 40 * 1555189 * 2
def baseEnd_1555189 : Nat := 118305106012625340679307

theorem tailTrace_1555189 : CollatzResearch.WordTrace tailWord_1555189 prefixEnd_1555189 118305106012625340679307 := by
  unfold tailWord_1555189
  simp only [CollatzResearch.WordTrace]
  refine ⟨56722402762823332980404621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37814935175215555320269747 56722402762823332980404621)
  ·
    refine ⟨21270901036058749867651733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56722402762823332980404621 21270901036058749867651733)
    ·
      refine ⟨997073486065253900046175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21270901036058749867651733 997073486065253900046175)
      ·
        refine ⟨1495610229097880850069263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 997073486065253900046175 1495610229097880850069263)
        ·
          refine ⟨2243415343646821275103895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1495610229097880850069263 2243415343646821275103895)
          ·
            refine ⟨3365123015470231912655843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2243415343646821275103895 3365123015470231912655843)
            ·
              refine ⟨5047684523205347868983765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3365123015470231912655843 5047684523205347868983765)
              ·
                refine ⟨118305106012625340679307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5047684523205347868983765 118305106012625340679307)
                ·
                  rfl

theorem cell21_1555189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 7].length) (baseStart_1555189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1555189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1555189 prefixEnd_1555189 := by exact prefixLift 1555189
  have htrace : WordTrace (prefixWord ++ tailWord_1555189) baseStart_1555189 baseEnd_1555189 := by
    simpa [prefixWord, tailWord_1555189, baseEnd_1555189] using wordTrace_append hprefix tailTrace_1555189
  have hstable : (prefixWord ++ tailWord_1555189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555189).length < 2 ^ (prefixWord ++ tailWord_1555189).sum := by decide
  have hdescent : baseEnd_1555189 < baseStart_1555189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555234 : List Nat := [3, 3, 1, 1, 2, 4, 2, 1, 4]
def baseStart_1555234 : Nat := 118140960795 + 1555234 * 2 ^ 59
def prefixEnd_1555234 : Nat := 4983230072969 + 3 ^ 40 * 1555234 * 2
def baseEnd_1555234 : Nat := 354925587650965943787829

theorem tailTrace_1555234 : CollatzResearch.WordTrace tailWord_1555234 prefixEnd_1555234 354925587650965943787829 := by
  unfold tailWord_1555234
  simp only [CollatzResearch.WordTrace]
  refine ⟨14181011011915076416448189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37816029365106870443861837 14181011011915076416448189)
  ·
    refine ⟨5317879129468153656168071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14181011011915076416448189 5317879129468153656168071)
    ·
      refine ⟨7976818694202230484252107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5317879129468153656168071 7976818694202230484252107)
      ·
        refine ⟨11965228041303345726378161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7976818694202230484252107 11965228041303345726378161)
        ·
          refine ⟨8973921030977509294783621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11965228041303345726378161 8973921030977509294783621)
          ·
            refine ⟨1682610193308282992771929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8973921030977509294783621 1682610193308282992771929)
            ·
              refine ⟨1261957644981212244578947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1682610193308282992771929 1261957644981212244578947)
              ·
                refine ⟨1892936467471818366868421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1261957644981212244578947 1892936467471818366868421)
                ·
                  refine ⟨354925587650965943787829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1892936467471818366868421 354925587650965943787829)
                  ·
                    rfl

theorem cell21_1555234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_1555234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1555234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1555234 prefixEnd_1555234 := by exact prefixLift 1555234
  have htrace : WordTrace (prefixWord ++ tailWord_1555234) baseStart_1555234 baseEnd_1555234 := by
    simpa [prefixWord, tailWord_1555234, baseEnd_1555234] using wordTrace_append hprefix tailTrace_1555234
  have hstable : (prefixWord ++ tailWord_1555234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555234).length < 2 ^ (prefixWord ++ tailWord_1555234).sum := by decide
  have hdescent : baseEnd_1555234 < baseStart_1555234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555273 : List Nat := [1, 2, 1, 1, 2, 14]
def baseStart_1555273 : Nat := 118140960795 + 1555273 * 2 ^ 59
def prefixEnd_1555273 : Nat := 4983230072969 + 3 ^ 40 * 1555273 * 2
def baseEnd_1555273 : Nat := 13145721777122612690287

theorem tailTrace_1555273 : CollatzResearch.WordTrace tailWord_1555273 prefixEnd_1555273 13145721777122612690287 := by
  unfold tailWord_1555273
  simp only [CollatzResearch.WordTrace]
  refine ⟨56725466494519015326462473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37816977663012676884308315 56725466494519015326462473)
  ·
    refine ⟨42544099870889261494846855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56725466494519015326462473 42544099870889261494846855)
    ·
      refine ⟨63816149806333892242270283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42544099870889261494846855 63816149806333892242270283)
      ·
        refine ⟨95724224709500838363405425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63816149806333892242270283 95724224709500838363405425)
        ·
          refine ⟨71793168532125628772554069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95724224709500838363405425 71793168532125628772554069)
          ·
            refine ⟨13145721777122612690287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 71793168532125628772554069 13145721777122612690287)
            ·
              rfl

theorem cell21_1555273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 14].length) (baseStart_1555273 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1555273 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1555273 prefixEnd_1555273 := by exact prefixLift 1555273
  have htrace : WordTrace (prefixWord ++ tailWord_1555273) baseStart_1555273 baseEnd_1555273 := by
    simpa [prefixWord, tailWord_1555273, baseEnd_1555273] using wordTrace_append hprefix tailTrace_1555273
  have hstable : (prefixWord ++ tailWord_1555273).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555273).length < 2 ^ (prefixWord ++ tailWord_1555273).sum := by decide
  have hdescent : baseEnd_1555273 < baseStart_1555273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555276 : List Nat := [2, 2, 1, 3, 3, 1, 1, 4, 4]
def baseStart_1555276 : Nat := 118140960795 + 1555276 * 2 ^ 59
def prefixEnd_1555276 : Nat := 4983230072969 + 3 ^ 40 * 1555276 * 2
def baseEnd_1555276 : Nat := 354935172623183204087743

theorem tailTrace_1555276 : CollatzResearch.WordTrace tailWord_1555276 prefixEnd_1555276 354935172623183204087743 := by
  unfold tailWord_1555276
  simp only [CollatzResearch.WordTrace]
  refine ⟨28362787956754073419410841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37817050609005431225881121 28362787956754073419410841)
  ·
    refine ⟨21272090967565555064558131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28362787956754073419410841 21272090967565555064558131)
    ·
      refine ⟨31908136451348332596837197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21272090967565555064558131 31908136451348332596837197)
      ·
        refine ⟨11965551169255624723813949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31908136451348332596837197 11965551169255624723813949)
        ·
          refine ⟨4487081688470859271430231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11965551169255624723813949 4487081688470859271430231)
          ·
            refine ⟨6730622532706288907145347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4487081688470859271430231 6730622532706288907145347)
            ·
              refine ⟨10095933799059433360718021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6730622532706288907145347 10095933799059433360718021)
              ·
                refine ⟨1892987587323643755134629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10095933799059433360718021 1892987587323643755134629)
                ·
                  refine ⟨354935172623183204087743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1892987587323643755134629 354935172623183204087743)
                  ·
                    rfl

theorem cell21_1555276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4, 4].length) (baseStart_1555276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1555276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1555276 prefixEnd_1555276 := by exact prefixLift 1555276
  have htrace : WordTrace (prefixWord ++ tailWord_1555276) baseStart_1555276 baseEnd_1555276 := by
    simpa [prefixWord, tailWord_1555276, baseEnd_1555276] using wordTrace_append hprefix tailTrace_1555276
  have hstable : (prefixWord ++ tailWord_1555276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555276).length < 2 ^ (prefixWord ++ tailWord_1555276).sum := by decide
  have hdescent : baseEnd_1555276 < baseStart_1555276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555290 : List Nat := [3, 1, 1, 2, 1, 4, 3, 6]
def baseStart_1555290 : Nat := 118140960795 + 1555290 * 2 ^ 59
def prefixEnd_1555290 : Nat := 4983230072969 + 3 ^ 40 * 1555290 * 2
def baseEnd_1555290 : Nat := 118312789204640763618127

theorem tailTrace_1555290 : CollatzResearch.WordTrace tailWord_1555290 prefixEnd_1555290 118312789204640763618127 := by
  unfold tailWord_1555290
  simp only [CollatzResearch.WordTrace]
  refine ⟨14181521633864356807457831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37817391023638284819887549 14181521633864356807457831)
  ·
    refine ⟨21272282450796535211186747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14181521633864356807457831 21272282450796535211186747)
    ·
      refine ⟨31908423676194802816780121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21272282450796535211186747 31908423676194802816780121)
      ·
        refine ⟨23931317757146102112585091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31908423676194802816780121 23931317757146102112585091)
        ·
          refine ⟨35896976635719153168877637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23931317757146102112585091 35896976635719153168877637)
          ·
            refine ⟨6730683119197341219164557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35896976635719153168877637 6730683119197341219164557)
            ·
              refine ⟨2524006169699002957186709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6730683119197341219164557 2524006169699002957186709)
              ·
                refine ⟨118312789204640763618127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2524006169699002957186709 118312789204640763618127)
                ·
                  rfl

theorem cell21_1555290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 6].length) (baseStart_1555290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1555290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1555290 prefixEnd_1555290 := by exact prefixLift 1555290
  have htrace : WordTrace (prefixWord ++ tailWord_1555290) baseStart_1555290 baseEnd_1555290 := by
    simpa [prefixWord, tailWord_1555290, baseEnd_1555290] using wordTrace_append hprefix tailTrace_1555290
  have hstable : (prefixWord ++ tailWord_1555290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555290).length < 2 ^ (prefixWord ++ tailWord_1555290).sum := by decide
  have hdescent : baseEnd_1555290 < baseStart_1555290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555338 : List Nat := [3, 1, 2, 4, 1, 2, 2, 1, 5]
def baseStart_1555338 : Nat := 118140960795 + 1555338 * 2 ^ 59
def prefixEnd_1555338 : Nat := 4983230072969 + 3 ^ 40 * 1555338 * 2
def baseEnd_1555338 : Nat := 354949321867884874054283

theorem tailTrace_1555338 : CollatzResearch.WordTrace tailWord_1555338 prefixEnd_1555338 354949321867884874054283 := by
  unfold tailWord_1555338
  simp only [CollatzResearch.WordTrace]
  refine ⟨14181959309820882856894667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37818558159522354285052445 14181959309820882856894667)
  ·
    refine ⟨21272938964731324285342001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14181959309820882856894667 21272938964731324285342001)
    ·
      refine ⟨15954704223548493214006501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21272938964731324285342001 15954704223548493214006501)
      ·
        refine ⟨2991507041915342477626219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15954704223548493214006501 2991507041915342477626219)
        ·
          refine ⟨4487260562873013716439329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2991507041915342477626219 4487260562873013716439329)
          ·
            refine ⟨3365445422154760287329497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4487260562873013716439329 3365445422154760287329497)
            ·
              refine ⟨2524084066616070215497123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3365445422154760287329497 2524084066616070215497123)
              ·
                refine ⟨3786126099924105323245685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2524084066616070215497123 3786126099924105323245685)
                ·
                  refine ⟨354949321867884874054283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3786126099924105323245685 354949321867884874054283)
                  ·
                    rfl

theorem cell21_1555338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 5].length) (baseStart_1555338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1555338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1555338 prefixEnd_1555338 := by exact prefixLift 1555338
  have htrace : WordTrace (prefixWord ++ tailWord_1555338) baseStart_1555338 baseEnd_1555338 := by
    simpa [prefixWord, tailWord_1555338, baseEnd_1555338] using wordTrace_append hprefix tailTrace_1555338
  have hstable : (prefixWord ++ tailWord_1555338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555338).length < 2 ^ (prefixWord ++ tailWord_1555338).sum := by decide
  have hdescent : baseEnd_1555338 < baseStart_1555338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555442 : List Nat := [3, 2, 1, 5, 10]
def baseStart_1555442 : Nat := 118140960795 + 1555442 * 2 ^ 59
def prefixEnd_1555442 : Nat := 4983230072969 + 3 ^ 40 * 1555442 * 2
def baseEnd_1555442 : Nat := 4382383408454367954577

theorem tailTrace_1555442 : CollatzResearch.WordTrace tailWord_1555442 prefixEnd_1555442 4382383408454367954577 := by
  unfold tailWord_1555442
  simp only [CollatzResearch.WordTrace]
  refine ⟨14182907607726689297341145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37821086953937838126243053 14182907607726689297341145)
  ·
    refine ⟨10637180705795016973005859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14182907607726689297341145 10637180705795016973005859)
    ·
      refine ⟨15955771058692525459508789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10637180705795016973005859 15955771058692525459508789)
      ·
        refine ⟨1495853536752424261828949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15955771058692525459508789 1495853536752424261828949)
        ·
          refine ⟨4382383408454367954577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1495853536752424261828949 4382383408454367954577)
          ·
            rfl

theorem cell21_1555442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 10].length) (baseStart_1555442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1555442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1555442 prefixEnd_1555442 := by exact prefixLift 1555442
  have htrace : WordTrace (prefixWord ++ tailWord_1555442) baseStart_1555442 baseEnd_1555442 := by
    simpa [prefixWord, tailWord_1555442, baseEnd_1555442] using wordTrace_append hprefix tailTrace_1555442
  have hstable : (prefixWord ++ tailWord_1555442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555442).length < 2 ^ (prefixWord ++ tailWord_1555442).sum := by decide
  have hdescent : baseEnd_1555442 < baseStart_1555442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555490 : List Nat := [3, 3, 1, 1, 1, 3, 1, 5, 3]
def baseStart_1555490 : Nat := 118140960795 + 1555490 * 2 ^ 59
def prefixEnd_1555490 : Nat := 4983230072969 + 3 ^ 40 * 1555490 * 2
def baseEnd_1555490 : Nat := 354984010338766387520639

theorem tailTrace_1555490 : CollatzResearch.WordTrace tailWord_1555490 prefixEnd_1555490 354984010338766387520639 := by
  unfold tailWord_1555490
  simp only [CollatzResearch.WordTrace]
  refine ⟨14183345283683215346777981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37822254089821907591407949 14183345283683215346777981)
  ·
    refine ⟨5318754481381205755041743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14183345283683215346777981 5318754481381205755041743)
    ·
      refine ⟨7978131722071808632562615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5318754481381205755041743 7978131722071808632562615)
      ·
        refine ⟨11967197583107712948843923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7978131722071808632562615 11967197583107712948843923)
        ·
          refine ⟨17950796374661569423265885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11967197583107712948843923 17950796374661569423265885)
          ·
            refine ⟨6731548640498088533724707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17950796374661569423265885 6731548640498088533724707)
            ·
              refine ⟨10097322960747132800587061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6731548640498088533724707 10097322960747132800587061)
              ·
                refine ⟨946624027570043700055037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10097322960747132800587061 946624027570043700055037)
                ·
                  refine ⟨354984010338766387520639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 946624027570043700055037 354984010338766387520639)
                  ·
                    rfl

theorem cell21_1555490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_1555490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1555490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1555490 prefixEnd_1555490 := by exact prefixLift 1555490
  have htrace : WordTrace (prefixWord ++ tailWord_1555490) baseStart_1555490 baseEnd_1555490 := by
    simpa [prefixWord, tailWord_1555490, baseEnd_1555490] using wordTrace_append hprefix tailTrace_1555490
  have hstable : (prefixWord ++ tailWord_1555490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555490).length < 2 ^ (prefixWord ++ tailWord_1555490).sum := by decide
  have hdescent : baseEnd_1555490 < baseStart_1555490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555566 : List Nat := [4, 1, 2, 2, 1, 4, 1, 1, 5]
def baseStart_1555566 : Nat := 118140960795 + 1555566 * 2 ^ 59
def prefixEnd_1555566 : Nat := 4983230072969 + 3 ^ 40 * 1555566 * 2
def baseEnd_1555566 : Nat := 355001354574207144253817

theorem tailTrace_1555566 : CollatzResearch.WordTrace tailWord_1555566 prefixEnd_1555566 355001354574207144253817 := by
  unfold tailWord_1555566
  simp only [CollatzResearch.WordTrace]
  refine ⟨7092019135307190795859819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37824102054971684244585701 7092019135307190795859819)
  ·
    refine ⟨10638028702960786193789729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7092019135307190795859819 10638028702960786193789729)
    ·
      refine ⟨7978521527220589645342297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10638028702960786193789729 7978521527220589645342297)
      ·
        refine ⟨5983891145415442234006723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7978521527220589645342297 5983891145415442234006723)
        ·
          refine ⟨8975836718123163351010085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5983891145415442234006723 8975836718123163351010085)
          ·
            refine ⟨1682969384648093128314391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8975836718123163351010085 1682969384648093128314391)
            ·
              refine ⟨2524454076972139692471587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1682969384648093128314391 2524454076972139692471587)
              ·
                refine ⟨3786681115458209538707381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2524454076972139692471587 3786681115458209538707381)
                ·
                  refine ⟨355001354574207144253817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3786681115458209538707381 355001354574207144253817)
                  ·
                    rfl

theorem cell21_1555566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_1555566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1555566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1555566 prefixEnd_1555566 := by exact prefixLift 1555566
  have htrace : WordTrace (prefixWord ++ tailWord_1555566) baseStart_1555566 baseEnd_1555566 := by
    simpa [prefixWord, tailWord_1555566, baseEnd_1555566] using wordTrace_append hprefix tailTrace_1555566
  have hstable : (prefixWord ++ tailWord_1555566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555566).length < 2 ^ (prefixWord ++ tailWord_1555566).sum := by decide
  have hdescent : baseEnd_1555566 < baseStart_1555566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555639 : List Nat := [1, 1, 3, 1, 4, 1, 1, 5, 4]
def baseStart_1555639 : Nat := 118140960795 + 1555639 * 2 ^ 59
def prefixEnd_1555639 : Nat := 4983230072969 + 3 ^ 40 * 1555639 * 2
def baseEnd_1555639 : Nat := 355018014168775239537001

theorem tailTrace_1555639 : CollatzResearch.WordTrace tailWord_1555639 prefixEnd_1555639 355018014168775239537001 := by
  unfold tailWord_1555639
  simp only [CollatzResearch.WordTrace]
  refine ⟨56738815611193059834285971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37825877074128706556190647 56738815611193059834285971)
  ·
    refine ⟨85108223416789589751428957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56738815611193059834285971 85108223416789589751428957)
    ·
      refine ⟨31915583781296096156785859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85108223416789589751428957 31915583781296096156785859)
      ·
        refine ⟨47873375671944144235178789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31915583781296096156785859 47873375671944144235178789)
        ·
          refine ⟨8976257938489527044096023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47873375671944144235178789 8976257938489527044096023)
          ·
            refine ⟨13464386907734290566144035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8976257938489527044096023 13464386907734290566144035)
            ·
              refine ⟨20196580361601435849216053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13464386907734290566144035 20196580361601435849216053)
              ·
                refine ⟨1893429408900134610864005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20196580361601435849216053 1893429408900134610864005)
                ·
                  refine ⟨355018014168775239537001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1893429408900134610864005 355018014168775239537001)
                  ·
                    rfl

theorem cell21_1555639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5, 4].length) (baseStart_1555639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1555639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1555639 prefixEnd_1555639 := by exact prefixLift 1555639
  have htrace : WordTrace (prefixWord ++ tailWord_1555639) baseStart_1555639 baseEnd_1555639 := by
    simpa [prefixWord, tailWord_1555639, baseEnd_1555639] using wordTrace_append hprefix tailTrace_1555639
  have hstable : (prefixWord ++ tailWord_1555639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555639).length < 2 ^ (prefixWord ++ tailWord_1555639).sum := by decide
  have hdescent : baseEnd_1555639 < baseStart_1555639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555684 : List Nat := [2, 3, 1, 1, 1, 2, 3, 3, 5]
def baseStart_1555684 : Nat := 118140960795 + 1555684 * 2 ^ 59
def prefixEnd_1555684 : Nat := 4983230072969 + 3 ^ 40 * 1555684 * 2
def baseEnd_1555684 : Nat := 355028283781865161286909

theorem tailTrace_1555684 : CollatzResearch.WordTrace tailWord_1555684 prefixEnd_1555684 355028283781865161286909 := by
  unfold tailWord_1555684
  simp only [CollatzResearch.WordTrace]
  refine ⟨28370228448015016259837053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37826971264020021679782737 28370228448015016259837053)
  ·
    refine ⟨10638835668005631097438895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28370228448015016259837053 10638835668005631097438895)
    ·
      refine ⟨15958253502008446646158343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10638835668005631097438895 15958253502008446646158343)
      ·
        refine ⟨23937380253012669969237515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15958253502008446646158343 23937380253012669969237515)
        ·
          refine ⟨35906070379519004953856273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23937380253012669969237515 35906070379519004953856273)
          ·
            refine ⟨26929552784639253715392205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35906070379519004953856273 26929552784639253715392205)
            ·
              refine ⟨10098582294239720143272077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26929552784639253715392205 10098582294239720143272077)
              ·
                refine ⟨3786968360339895053727029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10098582294239720143272077 3786968360339895053727029)
                ·
                  refine ⟨355028283781865161286909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3786968360339895053727029 355028283781865161286909)
                  ·
                    rfl

theorem cell21_1555684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_1555684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1555684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1555684 prefixEnd_1555684 := by exact prefixLift 1555684
  have htrace : WordTrace (prefixWord ++ tailWord_1555684) baseStart_1555684 baseEnd_1555684 := by
    simpa [prefixWord, tailWord_1555684, baseEnd_1555684] using wordTrace_append hprefix tailTrace_1555684
  have hstable : (prefixWord ++ tailWord_1555684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555684).length < 2 ^ (prefixWord ++ tailWord_1555684).sum := by decide
  have hdescent : baseEnd_1555684 < baseStart_1555684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555749 : List Nat := [1, 3, 1, 2, 4, 3, 2, 1, 4]
def baseStart_1555749 : Nat := 118140960795 + 1555749 * 2 ^ 59
def prefixEnd_1555749 : Nat := 4983230072969 + 3 ^ 40 * 1555749 * 2
def baseEnd_1555749 : Nat := 355043117667439492703443

theorem tailTrace_1555749 : CollatzResearch.WordTrace tailWord_1555749 prefixEnd_1555749 355043117667439492703443 := by
  unfold tailWord_1555749
  simp only [CollatzResearch.WordTrace]
  refine ⟨56742827640794548620790301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37828551760529699080526867 56742827640794548620790301)
  ·
    refine ⟨21278560365297955732796363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56742827640794548620790301 21278560365297955732796363)
    ·
      refine ⟨31917840547946933599194545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21278560365297955732796363 31917840547946933599194545)
      ·
        refine ⟨23938380410960200199395909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31917840547946933599194545 23938380410960200199395909)
        ·
          refine ⟨4488446327055037537386733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23938380410960200199395909 4488446327055037537386733)
          ·
            refine ⟨1683167372645639076520025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4488446327055037537386733 1683167372645639076520025)
            ·
              refine ⟨1262375529484229307390019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1683167372645639076520025 1262375529484229307390019)
              ·
                refine ⟨1893563294226343961085029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1262375529484229307390019 1893563294226343961085029)
                ·
                  refine ⟨355043117667439492703443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1893563294226343961085029 355043117667439492703443)
                  ·
                    rfl

theorem cell21_1555749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 1, 4].length) (baseStart_1555749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1555749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1555749 prefixEnd_1555749 := by exact prefixLift 1555749
  have htrace : WordTrace (prefixWord ++ tailWord_1555749) baseStart_1555749 baseEnd_1555749 := by
    simpa [prefixWord, tailWord_1555749, baseEnd_1555749] using wordTrace_append hprefix tailTrace_1555749
  have hstable : (prefixWord ++ tailWord_1555749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555749).length < 2 ^ (prefixWord ++ tailWord_1555749).sum := by decide
  have hdescent : baseEnd_1555749 < baseStart_1555749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555842 : List Nat := [3, 4, 2, 1, 1, 3, 1, 2, 4]
def baseStart_1555842 : Nat := 118140960795 + 1555842 * 2 ^ 59
def prefixEnd_1555842 : Nat := 4983230072969 + 3 ^ 40 * 1555842 * 2
def baseEnd_1555842 : Nat := 355064341534491997653253

theorem tailTrace_1555842 : CollatzResearch.WordTrace tailWord_1555842 prefixEnd_1555842 355064341534491997653253 := by
  unfold tailWord_1555842
  simp only [CollatzResearch.WordTrace]
  refine ⟨14186554907364406375981445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37830813086305083669283853 14186554907364406375981445)
  ·
    refine ⟨2659979045130826195496521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14186554907364406375981445 2659979045130826195496521)
    ·
      refine ⟨1994984283848119646622391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2659979045130826195496521 1994984283848119646622391)
      ·
        refine ⟨2992476425772179469933587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1994984283848119646622391 2992476425772179469933587)
        ·
          refine ⟨4488714638658269204900381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2992476425772179469933587 4488714638658269204900381)
          ·
            refine ⟨1683267989496850951837643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4488714638658269204900381 1683267989496850951837643)
            ·
              refine ⟨2524901984245276427756465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1683267989496850951837643 2524901984245276427756465)
              ·
                refine ⟨1893676488183957320817349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2524901984245276427756465 1893676488183957320817349)
                ·
                  refine ⟨355064341534491997653253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1893676488183957320817349 355064341534491997653253)
                  ·
                    rfl

theorem cell21_1555842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_1555842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1555842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1555842 prefixEnd_1555842 := by exact prefixLift 1555842
  have htrace : WordTrace (prefixWord ++ tailWord_1555842) baseStart_1555842 baseEnd_1555842 := by
    simpa [prefixWord, tailWord_1555842, baseEnd_1555842] using wordTrace_append hprefix tailTrace_1555842
  have hstable : (prefixWord ++ tailWord_1555842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555842).length < 2 ^ (prefixWord ++ tailWord_1555842).sum := by decide
  have hdescent : baseEnd_1555842 < baseStart_1555842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556019 : List Nat := [1, 1, 1, 2, 4, 3, 3, 2, 4]
def baseStart_1556019 : Nat := 118140960795 + 1556019 * 2 ^ 59
def prefixEnd_1556019 : Nat := 4983230072969 + 3 ^ 40 * 1556019 * 2
def baseEnd_1556019 : Nat := 355104735345979023202891

theorem tailTrace_1556019 : CollatzResearch.WordTrace tailWord_1556019 prefixEnd_1556019 355104735345979023202891 := by
  unfold tailWord_1556019
  simp only [CollatzResearch.WordTrace]
  refine ⟨56752675349816384733119111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37835116899877589822079407 56752675349816384733119111)
  ·
    refine ⟨85129013024724577099678667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56752675349816384733119111 85129013024724577099678667)
    ·
      refine ⟨127693519537086865649518001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85129013024724577099678667 127693519537086865649518001)
      ·
        refine ⟨95770139652815149237138501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127693519537086865649518001 95770139652815149237138501)
        ·
          refine ⟨17956901184902840481963469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95770139652815149237138501 17956901184902840481963469)
          ·
            refine ⟨6733837944338565180736301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17956901184902840481963469 6733837944338565180736301)
            ·
              refine ⟨2525189229126961942776113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6733837944338565180736301 2525189229126961942776113)
              ·
                refine ⟨1893891921845221457082085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2525189229126961942776113 1893891921845221457082085)
                ·
                  refine ⟨355104735345979023202891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1893891921845221457082085 355104735345979023202891)
                  ·
                    rfl

theorem cell21_1556019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2, 4].length) (baseStart_1556019 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1556019 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1556019 prefixEnd_1556019 := by exact prefixLift 1556019
  have htrace : WordTrace (prefixWord ++ tailWord_1556019) baseStart_1556019 baseEnd_1556019 := by
    simpa [prefixWord, tailWord_1556019, baseEnd_1556019] using wordTrace_append hprefix tailTrace_1556019
  have hstable : (prefixWord ++ tailWord_1556019).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556019).length < 2 ^ (prefixWord ++ tailWord_1556019).sum := by decide
  have hdescent : baseEnd_1556019 < baseStart_1556019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556022 : List Nat := [5, 1, 2, 1, 3, 1, 2, 1, 5]
def baseStart_1556022 : Nat := 118140960795 + 1556022 * 2 ^ 59
def prefixEnd_1556022 : Nat := 4983230072969 + 3 ^ 40 * 1556022 * 2
def baseEnd_1556022 : Nat := 355105419986851684652885

theorem tailTrace_1556022 : CollatzResearch.WordTrace tailWord_1556022 prefixEnd_1556022 355105419986851684652885 := by
  unfold tailWord_1556022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3547049048050344765342395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37835189845870344163652213 3547049048050344765342395)
  ·
    refine ⟨5320573572075517148013593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3547049048050344765342395 5320573572075517148013593)
    ·
      refine ⟨3990430179056637861010195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5320573572075517148013593 3990430179056637861010195)
      ·
        refine ⟨5985645268584956791515293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3990430179056637861010195 5985645268584956791515293)
        ·
          refine ⟨2244616975719358796818235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5985645268584956791515293 2244616975719358796818235)
          ·
            refine ⟨3366925463579038195227353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2244616975719358796818235 3366925463579038195227353)
            ·
              refine ⟨2525194097684278646420515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3366925463579038195227353 2525194097684278646420515)
              ·
                refine ⟨3787791146526417969630773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2525194097684278646420515 3787791146526417969630773)
                ·
                  refine ⟨355105419986851684652885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3787791146526417969630773 355105419986851684652885)
                  ·
                    rfl

theorem cell21_1556022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_1556022 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1556022 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1556022 prefixEnd_1556022 := by exact prefixLift 1556022
  have htrace : WordTrace (prefixWord ++ tailWord_1556022) baseStart_1556022 baseEnd_1556022 := by
    simpa [prefixWord, tailWord_1556022, baseEnd_1556022] using wordTrace_append hprefix tailTrace_1556022
  have hstable : (prefixWord ++ tailWord_1556022).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556022).length < 2 ^ (prefixWord ++ tailWord_1556022).sum := by decide
  have hdescent : baseEnd_1556022 < baseStart_1556022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556033 : List Nat := [1, 2, 5, 1, 1, 1, 2, 8]
def baseStart_1556033 : Nat := 118140960795 + 1556033 * 2 ^ 59
def prefixEnd_1556033 : Nat := 4983230072969 + 3 ^ 40 * 1556033 * 2
def baseEnd_1556033 : Nat := 118369310112239369989843

theorem tailTrace_1556033 : CollatzResearch.WordTrace tailWord_1556033 prefixEnd_1556033 118369310112239369989843 := by
  unfold tailWord_1556033
  simp only [CollatzResearch.WordTrace]
  refine ⟨56753185971765665124128753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37835457314510443416085835 56753185971765665124128753)
  ·
    refine ⟨42564889478824248843096565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56753185971765665124128753 42564889478824248843096565)
    ·
      refine ⟨3990458388639773329040303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42564889478824248843096565 3990458388639773329040303)
      ·
        refine ⟨5985687582959659993560455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3990458388639773329040303 5985687582959659993560455)
        ·
          refine ⟨8978531374439489990340683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5985687582959659993560455 8978531374439489990340683)
          ·
            refine ⟨13467797061659234985511025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8978531374439489990340683 13467797061659234985511025)
            ·
              refine ⟨10100847796244426239133269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13467797061659234985511025 10100847796244426239133269)
              ·
                refine ⟨118369310112239369989843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10100847796244426239133269 118369310112239369989843)
                ·
                  rfl

theorem cell21_1556033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 8].length) (baseStart_1556033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1556033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1556033 prefixEnd_1556033 := by exact prefixLift 1556033
  have htrace : WordTrace (prefixWord ++ tailWord_1556033) baseStart_1556033 baseEnd_1556033 := by
    simpa [prefixWord, tailWord_1556033, baseEnd_1556033] using wordTrace_append hprefix tailTrace_1556033
  have hstable : (prefixWord ++ tailWord_1556033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556033).length < 2 ^ (prefixWord ++ tailWord_1556033).sum := by decide
  have hdescent : baseEnd_1556033 < baseStart_1556033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556050 : List Nat := [3, 2, 2, 1, 2, 2, 4, 5]
def baseStart_1556050 : Nat := 118140960795 + 1556050 * 2 ^ 59
def prefixEnd_1556050 : Nat := 4983230072969 + 3 ^ 40 * 1556050 * 2
def baseEnd_1556050 : Nat := 118370603322776619395387

theorem tailTrace_1556050 : CollatzResearch.WordTrace tailWord_1556050 prefixEnd_1556050 118370603322776619395387 := by
  unfold tailWord_1556050
  simp only [CollatzResearch.WordTrace]
  refine ⟨14188451503176019256874401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37835870675136051351665069 14188451503176019256874401)
  ·
    refine ⟨10641338627382014442655801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14188451503176019256874401 10641338627382014442655801)
    ·
      refine ⟨7981003970536510831991851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10641338627382014442655801 7981003970536510831991851)
      ·
        refine ⟨11971505955804766247987777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7981003970536510831991851 11971505955804766247987777)
        ·
          refine ⟨8978629466853574685990833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11971505955804766247987777 8978629466853574685990833)
          ·
            refine ⟨6733972100140181014493125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8978629466853574685990833 6733972100140181014493125)
            ·
              refine ⟨1262619768776283940217461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6733972100140181014493125 1262619768776283940217461)
              ·
                refine ⟨118370603322776619395387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1262619768776283940217461 118370603322776619395387)
                ·
                  rfl

theorem cell21_1556050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 5].length) (baseStart_1556050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1556050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1556050 prefixEnd_1556050 := by exact prefixLift 1556050
  have htrace : WordTrace (prefixWord ++ tailWord_1556050) baseStart_1556050 baseEnd_1556050 := by
    simpa [prefixWord, tailWord_1556050, baseEnd_1556050] using wordTrace_append hprefix tailTrace_1556050
  have hstable : (prefixWord ++ tailWord_1556050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556050).length < 2 ^ (prefixWord ++ tailWord_1556050).sum := by decide
  have hdescent : baseEnd_1556050 < baseStart_1556050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556188 : List Nat := [2, 2, 5, 1, 2, 1, 1, 1, 6]
def baseStart_1556188 : Nat := 118140960795 + 1556188 * 2 ^ 59
def prefixEnd_1556188 : Nat := 4983230072969 + 3 ^ 40 * 1556188 * 2
def baseEnd_1556188 : Nat := 355143303448472284885879

theorem tailTrace_1556188 : CollatzResearch.WordTrace tailWord_1556188 prefixEnd_1556188 355143303448472284885879 := by
  unfold tailWord_1556188
  simp only [CollatzResearch.WordTrace]
  refine ⟨28379419643102063298010609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37839226190802751064014145 28379419643102063298010609)
  ·
    refine ⟨21284564732326547473507957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28379419643102063298010609 21284564732326547473507957)
    ·
      refine ⟨1995427943655613825641371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21284564732326547473507957 1995427943655613825641371)
      ·
        refine ⟨2993141915483420738462057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1995427943655613825641371 2993141915483420738462057)
        ·
          refine ⟨2244856436612565553846543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2993141915483420738462057 2244856436612565553846543)
          ·
            refine ⟨3367284654918848330769815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2244856436612565553846543 3367284654918848330769815)
            ·
              refine ⟨5050926982378272496154723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3367284654918848330769815 5050926982378272496154723)
              ·
                refine ⟨7576390473567408744232085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5050926982378272496154723 7576390473567408744232085)
                ·
                  refine ⟨355143303448472284885879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7576390473567408744232085 355143303448472284885879)
                  ·
                    rfl

theorem cell21_1556188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 6].length) (baseStart_1556188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1556188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1556188 prefixEnd_1556188 := by exact prefixLift 1556188
  have htrace : WordTrace (prefixWord ++ tailWord_1556188) baseStart_1556188 baseEnd_1556188 := by
    simpa [prefixWord, tailWord_1556188, baseEnd_1556188] using wordTrace_append hprefix tailTrace_1556188
  have hstable : (prefixWord ++ tailWord_1556188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556188).length < 2 ^ (prefixWord ++ tailWord_1556188).sum := by decide
  have hdescent : baseEnd_1556188 < baseStart_1556188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556250 : List Nat := [3, 1, 1, 3, 2, 3, 3, 2, 3]
def baseStart_1556250 : Nat := 118140960795 + 1556250 * 2 ^ 59
def prefixEnd_1556250 : Nat := 4983230072969 + 3 ^ 40 * 1556250 * 2
def baseEnd_1556250 : Nat := 355157452693173954852419

theorem tailTrace_1556250 : CollatzResearch.WordTrace tailWord_1556250 prefixEnd_1556250 355157452693173954852419 := by
  unfold tailWord_1556250
  simp only [CollatzResearch.WordTrace]
  refine ⟨14190275152994877796194551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37840733741319674123185469 14190275152994877796194551)
  ·
    refine ⟨21285412729492316694291827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14190275152994877796194551 21285412729492316694291827)
    ·
      refine ⟨31928119094238475041437741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21285412729492316694291827 31928119094238475041437741)
      ·
        refine ⟨11973044660339428140539153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31928119094238475041437741 11973044660339428140539153)
        ·
          refine ⟨8979783495254571105404365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11973044660339428140539153 8979783495254571105404365)
          ·
            refine ⟨3367418810720464164526637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8979783495254571105404365 3367418810720464164526637)
            ·
              refine ⟨1262782054020174061697489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3367418810720464164526637 1262782054020174061697489)
              ·
                refine ⟨947086540515130546273117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1262782054020174061697489 947086540515130546273117)
                ·
                  refine ⟨355157452693173954852419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 947086540515130546273117 355157452693173954852419)
                  ·
                    rfl

theorem cell21_1556250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 2, 3].length) (baseStart_1556250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1556250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1556250 prefixEnd_1556250 := by exact prefixLift 1556250
  have htrace : WordTrace (prefixWord ++ tailWord_1556250) baseStart_1556250 baseEnd_1556250 := by
    simpa [prefixWord, tailWord_1556250, baseEnd_1556250] using wordTrace_append hprefix tailTrace_1556250
  have hstable : (prefixWord ++ tailWord_1556250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556250).length < 2 ^ (prefixWord ++ tailWord_1556250).sum := by decide
  have hdescent : baseEnd_1556250 < baseStart_1556250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556261 : List Nat := [1, 3, 1, 2, 3, 3, 2, 6]
def baseStart_1556261 : Nat := 118140960795 + 1556261 * 2 ^ 59
def prefixEnd_1556261 : Nat := 4983230072969 + 3 ^ 40 * 1556261 * 2
def baseEnd_1556261 : Nat := 118386654347680126723021

theorem tailTrace_1556261 : CollatzResearch.WordTrace tailWord_1556261 prefixEnd_1556261 118386654347680126723021 := by
  unfold tailWord_1556261
  simp only [CollatzResearch.WordTrace]
  refine ⟨56761501814939660063428637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37841001209959773375619091 56761501814939660063428637)
  ·
    refine ⟨21285563180602372523785739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56761501814939660063428637 21285563180602372523785739)
    ·
      refine ⟨31928344770903558785678609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21285563180602372523785739 31928344770903558785678609)
      ·
        refine ⟨23946258578177669089258957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31928344770903558785678609 23946258578177669089258957)
        ·
          refine ⟨8979846966816625908472109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23946258578177669089258957 8979846966816625908472109)
          ·
            refine ⟨3367442612556234715677041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8979846966816625908472109 3367442612556234715677041)
            ·
              refine ⟨2525581959417176036757781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3367442612556234715677041 2525581959417176036757781)
              ·
                refine ⟨118386654347680126723021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2525581959417176036757781 118386654347680126723021)
                ·
                  rfl

theorem cell21_1556261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 6].length) (baseStart_1556261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1556261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1556261 prefixEnd_1556261 := by exact prefixLift 1556261
  have htrace : WordTrace (prefixWord ++ tailWord_1556261) baseStart_1556261 baseEnd_1556261 := by
    simpa [prefixWord, tailWord_1556261, baseEnd_1556261] using wordTrace_append hprefix tailTrace_1556261
  have hstable : (prefixWord ++ tailWord_1556261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556261).length < 2 ^ (prefixWord ++ tailWord_1556261).sum := by decide
  have hdescent : baseEnd_1556261 < baseStart_1556261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556264 : List Nat := [2, 1, 5, 1, 1, 2, 4, 1, 4]
def baseStart_1556264 : Nat := 118140960795 + 1556264 * 2 ^ 59
def prefixEnd_1556264 : Nat := 4983230072969 + 3 ^ 40 * 1556264 * 2
def baseEnd_1556264 : Nat := 355160647683913041619057

theorem tailTrace_1556264 : CollatzResearch.WordTrace tailWord_1556264 prefixEnd_1556264 355160647683913041619057 := by
  unfold tailWord_1556264
  simp only [CollatzResearch.WordTrace]
  refine ⟨28380805616964395787893923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37841074155952527717191897 28380805616964395787893923)
  ·
    refine ⟨42571208425446593681840885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28380805616964395787893923 42571208425446593681840885)
    ·
      refine ⟨3991050789885618157672583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42571208425446593681840885 3991050789885618157672583)
      ·
        refine ⟨5986576184828427236508875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3991050789885618157672583 5986576184828427236508875)
        ·
          refine ⟨8979864277242640854763313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5986576184828427236508875 8979864277242640854763313)
          ·
            refine ⟨6734898207931980641072485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8979864277242640854763313 6734898207931980641072485)
            ·
              refine ⟨1262793413987246370201091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6734898207931980641072485 1262793413987246370201091)
              ·
                refine ⟨1894190120980869555301637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1262793413987246370201091 1894190120980869555301637)
                ·
                  refine ⟨355160647683913041619057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1894190120980869555301637 355160647683913041619057)
                  ·
                    rfl

theorem cell21_1556264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 1, 4].length) (baseStart_1556264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1556264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1556264 prefixEnd_1556264 := by exact prefixLift 1556264
  have htrace : WordTrace (prefixWord ++ tailWord_1556264) baseStart_1556264 baseEnd_1556264 := by
    simpa [prefixWord, tailWord_1556264, baseEnd_1556264] using wordTrace_append hprefix tailTrace_1556264
  have hstable : (prefixWord ++ tailWord_1556264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556264).length < 2 ^ (prefixWord ++ tailWord_1556264).sum := by decide
  have hdescent : baseEnd_1556264 < baseStart_1556264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556278 : List Nat := [5, 1, 2, 2, 1, 1, 2, 7]
def baseStart_1556278 : Nat := 118140960795 + 1556278 * 2 ^ 59
def prefixEnd_1556278 : Nat := 4983230072969 + 3 ^ 40 * 1556278 * 2
def baseEnd_1556278 : Nat := 118387947558217376128565

theorem tailTrace_1556278 : CollatzResearch.WordTrace tailWord_1556278 prefixEnd_1556278 118387947558217376128565 := by
  unfold tailWord_1556278
  simp only [CollatzResearch.WordTrace]
  refine ⟨3547632615992379497924843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37841414570585381311198325 3547632615992379497924843)
  ·
    refine ⟨5321448923988569246887265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3547632615992379497924843 5321448923988569246887265)
    ·
      refine ⟨3991086692991426935165449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5321448923988569246887265 3991086692991426935165449)
      ·
        refine ⟨2993315019743570201374087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3991086692991426935165449 2993315019743570201374087)
        ·
          refine ⟨4489972529615355302061131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2993315019743570201374087 4489972529615355302061131)
          ·
            refine ⟨6734958794423032953091697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4489972529615355302061131 6734958794423032953091697)
            ·
              refine ⟨5051219095817274714818773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6734958794423032953091697 5051219095817274714818773)
              ·
                refine ⟨118387947558217376128565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5051219095817274714818773 118387947558217376128565)
                ·
                  rfl

theorem cell21_1556278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_1556278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1556278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1556278 prefixEnd_1556278 := by exact prefixLift 1556278
  have htrace : WordTrace (prefixWord ++ tailWord_1556278) baseStart_1556278 baseEnd_1556278 := by
    simpa [prefixWord, tailWord_1556278, baseEnd_1556278] using wordTrace_append hprefix tailTrace_1556278
  have hstable : (prefixWord ++ tailWord_1556278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556278).length < 2 ^ (prefixWord ++ tailWord_1556278).sum := by decide
  have hdescent : baseEnd_1556278 < baseStart_1556278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556309 : List Nat := [1, 3, 2, 2, 2, 3, 1, 4, 3]
def baseStart_1556309 : Nat := 118140960795 + 1556309 * 2 ^ 59
def prefixEnd_1556309 : Nat := 4983230072969 + 3 ^ 40 * 1556309 * 2
def baseEnd_1556309 : Nat := 355170917297002963368965

theorem tailTrace_1556309 : CollatzResearch.WordTrace tailWord_1556309 prefixEnd_1556309 355170917297002963368965 := by
  unfold tailWord_1556309
  simp only [CollatzResearch.WordTrace]
  refine ⟨56763252518765764261175981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37842168345843842840783987 56763252518765764261175981)
  ·
    refine ⟨21286219694537161597940993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56763252518765764261175981 21286219694537161597940993)
    ·
      refine ⟨15964664770902871198455745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21286219694537161597940993 15964664770902871198455745)
      ·
        refine ⟨11973498578177153398841809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15964664770902871198455745 11973498578177153398841809)
        ·
          refine ⟨8980123933632865049131357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11973498578177153398841809 8980123933632865049131357)
          ·
            refine ⟨3367546475112324393424259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8980123933632865049131357 3367546475112324393424259)
            ·
              refine ⟨5051319712668486590136389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3367546475112324393424259 5051319712668486590136389)
              ·
                refine ⟨947122446125341235650573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5051319712668486590136389 947122446125341235650573)
                ·
                  refine ⟨355170917297002963368965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 947122446125341235650573 355170917297002963368965)
                  ·
                    rfl

theorem cell21_1556309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 4, 3].length) (baseStart_1556309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1556309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1556309 prefixEnd_1556309 := by exact prefixLift 1556309
  have htrace : WordTrace (prefixWord ++ tailWord_1556309) baseStart_1556309 baseEnd_1556309 := by
    simpa [prefixWord, tailWord_1556309, baseEnd_1556309] using wordTrace_append hprefix tailTrace_1556309
  have hstable : (prefixWord ++ tailWord_1556309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556309).length < 2 ^ (prefixWord ++ tailWord_1556309).sum := by decide
  have hdescent : baseEnd_1556309 < baseStart_1556309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556337 : List Nat := [1, 2, 2, 2, 1, 3, 5, 5]
def baseStart_1556337 : Nat := 118140960795 + 1556337 * 2 ^ 59
def prefixEnd_1556337 : Nat := 4983230072969 + 3 ^ 40 * 1556337 * 2
def baseEnd_1556337 : Nat := 118392435759493712300747

theorem tailTrace_1556337 : CollatzResearch.WordTrace tailWord_1556337 prefixEnd_1556337 118392435759493712300747 := by
  unfold tailWord_1556337
  simp only [CollatzResearch.WordTrace]
  refine ⟨56764273762664325043195265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37842849175109550028796843 56764273762664325043195265)
  ·
    refine ⟨42573205321998243782396449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56764273762664325043195265 42573205321998243782396449)
    ·
      refine ⟨31929903991498682836797337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42573205321998243782396449 31929903991498682836797337)
      ·
        refine ⟨23947427993624012127598003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31929903991498682836797337 23947427993624012127598003)
        ·
          refine ⟨35921141990436018191397005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23947427993624012127598003 35921141990436018191397005)
          ·
            refine ⟨13470428246413506821773877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35921141990436018191397005 13470428246413506821773877)
            ·
              refine ⟨1262852648101266264541301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13470428246413506821773877 1262852648101266264541301)
              ·
                refine ⟨118392435759493712300747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1262852648101266264541301 118392435759493712300747)
                ·
                  rfl

theorem cell21_1556337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 5].length) (baseStart_1556337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1556337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1556337 prefixEnd_1556337 := by exact prefixLift 1556337
  have htrace : WordTrace (prefixWord ++ tailWord_1556337) baseStart_1556337 baseEnd_1556337 := by
    simpa [prefixWord, tailWord_1556337, baseEnd_1556337] using wordTrace_append hprefix tailTrace_1556337
  have hstable : (prefixWord ++ tailWord_1556337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556337).length < 2 ^ (prefixWord ++ tailWord_1556337).sum := by decide
  have hdescent : baseEnd_1556337 < baseStart_1556337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556413 : List Nat := [1, 4, 1, 2, 3, 3, 7]
def baseStart_1556413 : Nat := 118140960795 + 1556413 * 2 ^ 59
def prefixEnd_1556413 : Nat := 4983230072969 + 3 ^ 40 * 1556413 * 2
def baseEnd_1556413 : Nat := 39466072390435765959491

theorem tailTrace_1556413 : CollatzResearch.WordTrace tailWord_1556413 prefixEnd_1556413 39466072390435765959491 := by
  unfold tailWord_1556413
  simp only [CollatzResearch.WordTrace]
  refine ⟨56767045710388990022961893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37844697140259326681974595 56767045710388990022961893)
  ·
    refine ⟨10643821070697935629305355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56767045710388990022961893 10643821070697935629305355)
    ·
      refine ⟨15965731606046903443958033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10643821070697935629305355 15965731606046903443958033)
      ·
        refine ⟨11974298704535177582968525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15965731606046903443958033 11974298704535177582968525)
        ·
          refine ⟨4490362014200691593613197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11974298704535177582968525 4490362014200691593613197)
          ·
            refine ⟨1683885755325259347604949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4490362014200691593613197 1683885755325259347604949)
            ·
              refine ⟨39466072390435765959491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1683885755325259347604949 39466072390435765959491)
              ·
                rfl

theorem cell21_1556413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 7].length) (baseStart_1556413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1556413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1556413 prefixEnd_1556413 := by exact prefixLift 1556413
  have htrace : WordTrace (prefixWord ++ tailWord_1556413) baseStart_1556413 baseEnd_1556413 := by
    simpa [prefixWord, tailWord_1556413, baseEnd_1556413] using wordTrace_append hprefix tailTrace_1556413
  have hstable : (prefixWord ++ tailWord_1556413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556413).length < 2 ^ (prefixWord ++ tailWord_1556413).sum := by decide
  have hdescent : baseEnd_1556413 < baseStart_1556413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556478 : List Nat := [4, 2, 2, 2, 1, 2, 1, 4, 3]
def baseStart_1556478 : Nat := 118140960795 + 1556478 * 2 ^ 59
def prefixEnd_1556478 : Nat := 4983230072969 + 3 ^ 40 * 1556478 * 2
def baseEnd_1556478 : Nat := 355209485399496225051953

theorem tailTrace_1556478 : CollatzResearch.WordTrace tailWord_1556478 prefixEnd_1556478 355209485399496225051953 := by
  unfold tailWord_1556478
  simp only [CollatzResearch.WordTrace]
  refine ⟨7096177056894188265509761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37846277636769004082718725 7096177056894188265509761)
  ·
    refine ⟨5322132792670641199132321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7096177056894188265509761 5322132792670641199132321)
    ·
      refine ⟨3991599594502980899349241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5322132792670641199132321 3991599594502980899349241)
      ·
        refine ⟨2993699695877235674511931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3991599594502980899349241 2993699695877235674511931)
        ·
          refine ⟨4490549543815853511767897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2993699695877235674511931 4490549543815853511767897)
          ·
            refine ⟨3367912157861890133825923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4490549543815853511767897 3367912157861890133825923)
            ·
              refine ⟨5051868236792835200738885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3367912157861890133825923 5051868236792835200738885)
              ·
                refine ⟨947225294398656600138541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5051868236792835200738885 947225294398656600138541)
                ·
                  refine ⟨355209485399496225051953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 947225294398656600138541 355209485399496225051953)
                  ·
                    rfl

theorem cell21_1556478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_1556478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1556478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1556478 prefixEnd_1556478 := by exact prefixLift 1556478
  have htrace : WordTrace (prefixWord ++ tailWord_1556478) baseStart_1556478 baseEnd_1556478 := by
    simpa [prefixWord, tailWord_1556478, baseEnd_1556478] using wordTrace_append hprefix tailTrace_1556478
  have hstable : (prefixWord ++ tailWord_1556478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556478).length < 2 ^ (prefixWord ++ tailWord_1556478).sum := by decide
  have hdescent : baseEnd_1556478 < baseStart_1556478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556551 : List Nat := [1, 1, 4, 1, 3, 1, 5, 1, 4]
def baseStart_1556551 : Nat := 118140960795 + 1556551 * 2 ^ 59
def prefixEnd_1556551 : Nat := 4983230072969 + 3 ^ 40 * 1556551 * 2
def baseEnd_1556551 : Nat := 355226144994064320335137

theorem tailTrace_1556551 : CollatzResearch.WordTrace tailWord_1556551 prefixEnd_1556551 355226144994064320335137 := by
  unfold tailWord_1556551
  simp only [CollatzResearch.WordTrace]
  refine ⟨56772078983889039591485507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37848052655926026394323671 56772078983889039591485507)
  ·
    refine ⟨85158118475833559387228261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56772078983889039591485507 85158118475833559387228261)
    ·
      refine ⟨15967147214218792385105299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85158118475833559387228261 15967147214218792385105299)
      ·
        refine ⟨23950720821328188577657949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15967147214218792385105299 23950720821328188577657949)
        ·
          refine ⟨8981520307998070716621731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23950720821328188577657949 8981520307998070716621731)
          ·
            refine ⟨13472280461997106074932597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8981520307998070716621731 13472280461997106074932597)
            ·
              refine ⟨1263026293312228694524931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13472280461997106074932597 1263026293312228694524931)
              ·
                refine ⟨1894539439968343041787397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1263026293312228694524931 1894539439968343041787397)
                ·
                  refine ⟨355226144994064320335137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1894539439968343041787397 355226144994064320335137)
                  ·
                    rfl

theorem cell21_1556551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 1, 4].length) (baseStart_1556551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1556551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1556551 prefixEnd_1556551 := by exact prefixLift 1556551
  have htrace : WordTrace (prefixWord ++ tailWord_1556551) baseStart_1556551 baseEnd_1556551 := by
    simpa [prefixWord, tailWord_1556551, baseEnd_1556551] using wordTrace_append hprefix tailTrace_1556551
  have hstable : (prefixWord ++ tailWord_1556551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556551).length < 2 ^ (prefixWord ++ tailWord_1556551).sum := by decide
  have hdescent : baseEnd_1556551 < baseStart_1556551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556565 : List Nat := [1, 3, 2, 2, 1, 3, 4, 5]
def baseStart_1556565 : Nat := 118140960795 + 1556565 * 2 ^ 59
def prefixEnd_1556565 : Nat := 4983230072969 + 3 ^ 40 * 1556565 * 2
def baseEnd_1556565 : Nat := 118409779994934469033925

theorem tailTrace_1556565 : CollatzResearch.WordTrace tailWord_1556565 prefixEnd_1556565 118409779994934469033925 := by
  unfold tailWord_1556565
  simp only [CollatzResearch.WordTrace]
  refine ⟨56772589605838319982495149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37848393070558879988330099 56772589605838319982495149)
  ·
    refine ⟨21289721102189369993435681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56772589605838319982495149 21289721102189369993435681)
    ·
      refine ⟨15967290826642027495076761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21289721102189369993435681 15967290826642027495076761)
      ·
        refine ⟨11975468119981520621307571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15967290826642027495076761 11975468119981520621307571)
        ·
          refine ⟨17963202179972280931961357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11975468119981520621307571 17963202179972280931961357)
          ·
            refine ⟨6736200817489605349485509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17963202179972280931961357 6736200817489605349485509)
            ·
              refine ⟨1263037653279301003028533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6736200817489605349485509 1263037653279301003028533)
              ·
                refine ⟨118409779994934469033925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1263037653279301003028533 118409779994934469033925)
                ·
                  rfl

theorem cell21_1556565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 5].length) (baseStart_1556565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1556565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1556565 prefixEnd_1556565 := by exact prefixLift 1556565
  have htrace : WordTrace (prefixWord ++ tailWord_1556565) baseStart_1556565 baseEnd_1556565 := by
    simpa [prefixWord, tailWord_1556565, baseEnd_1556565] using wordTrace_append hprefix tailTrace_1556565
  have hstable : (prefixWord ++ tailWord_1556565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556565).length < 2 ^ (prefixWord ++ tailWord_1556565).sum := by decide
  have hdescent : baseEnd_1556565 < baseStart_1556565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556593 : List Nat := [1, 2, 2, 2, 1, 1, 3, 3, 6]
def baseStart_1556593 : Nat := 118140960795 + 1556593 * 2 ^ 59
def prefixEnd_1556593 : Nat := 4983230072969 + 3 ^ 40 * 1556593 * 2
def baseEnd_1556593 : Nat := 355235729966281580635051

theorem tailTrace_1556593 : CollatzResearch.WordTrace tailWord_1556593 prefixEnd_1556593 355235729966281580635051 := by
  unfold tailWord_1556593
  simp only [CollatzResearch.WordTrace]
  refine ⟨56773610849736880764514433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37849073899824587176342955 56773610849736880764514433)
  ·
    refine ⟨42580208137302660573385825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56773610849736880764514433 42580208137302660573385825)
    ·
      refine ⟨31935156102976995430039369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42580208137302660573385825 31935156102976995430039369)
      ·
        refine ⟨23951367077232746572529527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31935156102976995430039369 23951367077232746572529527)
        ·
          refine ⟨35927050615849119858794291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23951367077232746572529527 35927050615849119858794291)
          ·
            refine ⟨53890575923773679788191437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35927050615849119858794291 53890575923773679788191437)
            ·
              refine ⟨20208965971415129920571789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53890575923773679788191437 20208965971415129920571789)
              ·
                refine ⟨7578362239280673720214421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20208965971415129920571789 7578362239280673720214421)
                ·
                  refine ⟨355235729966281580635051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7578362239280673720214421 355235729966281580635051)
                  ·
                    rfl

theorem cell21_1556593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 6].length) (baseStart_1556593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1556593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1556593 prefixEnd_1556593 := by exact prefixLift 1556593
  have htrace : WordTrace (prefixWord ++ tailWord_1556593) baseStart_1556593 baseEnd_1556593 := by
    simpa [prefixWord, tailWord_1556593, baseEnd_1556593] using wordTrace_append hprefix tailTrace_1556593
  have hstable : (prefixWord ++ tailWord_1556593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556593).length < 2 ^ (prefixWord ++ tailWord_1556593).sum := by decide
  have hdescent : baseEnd_1556593 < baseStart_1556593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556647 : List Nat := [1, 1, 6, 2, 2, 2, 2, 2, 3]
def baseStart_1556647 : Nat := 118140960795 + 1556647 * 2 ^ 59
def prefixEnd_1556647 : Nat := 4983230072969 + 3 ^ 40 * 1556647 * 2
def baseEnd_1556647 : Nat := 355248053501989486734941

theorem tailTrace_1556647 : CollatzResearch.WordTrace tailWord_1556647 prefixEnd_1556647 355248053501989486734941 := by
  unfold tailWord_1556647
  simp only [CollatzResearch.WordTrace]
  refine ⟨56775580391541247986980195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37850386927694165324653463 56775580391541247986980195)
  ·
    refine ⟨85163370587311871980470293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56775580391541247986980195 85163370587311871980470293)
    ·
      refine ⟨3992032996280243999084545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 85163370587311871980470293 3992032996280243999084545)
      ·
        refine ⟨2994024747210182999313409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3992032996280243999084545 2994024747210182999313409)
        ·
          refine ⟨2245518560407637249485057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2994024747210182999313409 2245518560407637249485057)
          ·
            refine ⟨1684138920305727937113793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2245518560407637249485057 1684138920305727937113793)
            ·
              refine ⟨1263104190229295952835345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1684138920305727937113793 1263104190229295952835345)
              ·
                refine ⟨947328142671971964626509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1263104190229295952835345 947328142671971964626509)
                ·
                  refine ⟨355248053501989486734941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 947328142671971964626509 355248053501989486734941)
                  ·
                    rfl

theorem cell21_1556647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 2, 3].length) (baseStart_1556647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1556647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1556647 prefixEnd_1556647 := by exact prefixLift 1556647
  have htrace : WordTrace (prefixWord ++ tailWord_1556647) baseStart_1556647 baseEnd_1556647 := by
    simpa [prefixWord, tailWord_1556647, baseEnd_1556647] using wordTrace_append hprefix tailTrace_1556647
  have hstable : (prefixWord ++ tailWord_1556647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556647).length < 2 ^ (prefixWord ++ tailWord_1556647).sum := by decide
  have hdescent : baseEnd_1556647 < baseStart_1556647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556669 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 8]
def baseStart_1556669 : Nat := 118140960795 + 1556669 * 2 ^ 59
def prefixEnd_1556669 : Nat := 4983230072969 + 3 ^ 40 * 1556669 * 2
def baseEnd_1556669 : Nat := 355253074201722337368229

theorem tailTrace_1556669 : CollatzResearch.WordTrace tailWord_1556669 prefixEnd_1556669 355253074201722337368229 := by
  unfold tailWord_1556669
  simp only [CollatzResearch.WordTrace]
  refine ⟨56776382797461545744281061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37850921864974363829520707 56776382797461545744281061)
  ·
    refine ⟨10645571774524039827052699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56776382797461545744281061 10645571774524039827052699)
    ·
      refine ⟨15968357661786059740579049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10645571774524039827052699 15968357661786059740579049)
      ·
        refine ⟨11976268246339544805434287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15968357661786059740579049 11976268246339544805434287)
        ·
          refine ⟨17964402369509317208151431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11976268246339544805434287 17964402369509317208151431)
          ·
            refine ⟨26946603554263975812227147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17964402369509317208151431 26946603554263975812227147)
            ·
              refine ⟨40419905331395963718340721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26946603554263975812227147 40419905331395963718340721)
              ·
                refine ⟨30314928998546972788755541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40419905331395963718340721 30314928998546972788755541)
                ·
                  refine ⟨355253074201722337368229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30314928998546972788755541 355253074201722337368229)
                  ·
                    rfl

theorem cell21_1556669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_1556669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1556669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1556669 prefixEnd_1556669 := by exact prefixLift 1556669
  have htrace : WordTrace (prefixWord ++ tailWord_1556669) baseStart_1556669 baseEnd_1556669 := by
    simpa [prefixWord, tailWord_1556669, baseEnd_1556669] using wordTrace_append hprefix tailTrace_1556669
  have hstable : (prefixWord ++ tailWord_1556669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556669).length < 2 ^ (prefixWord ++ tailWord_1556669).sum := by decide
  have hdescent : baseEnd_1556669 < baseStart_1556669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556745 : List Nat := [1, 2, 1, 1, 3, 4, 1, 2, 6]
def baseStart_1556745 : Nat := 118140960795 + 1556745 * 2 ^ 59
def prefixEnd_1556745 : Nat := 4983230072969 + 3 ^ 40 * 1556745 * 2
def baseEnd_1556745 : Nat := 355270418437163094101407

theorem tailTrace_1556745 : CollatzResearch.WordTrace tailWord_1556745 prefixEnd_1556745 355270418437163094101407 := by
  unfold tailWord_1556745
  simp only [CollatzResearch.WordTrace]
  refine ⟨56779154745186210724047689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37852769830124140482698459 56779154745186210724047689)
  ·
    refine ⟨42584366058889658043035767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56779154745186210724047689 42584366058889658043035767)
    ·
      refine ⟨63876549088334487064553651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42584366058889658043035767 63876549088334487064553651)
      ·
        refine ⟨95814823632501730596830477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63876549088334487064553651 95814823632501730596830477)
        ·
          refine ⟨35930558862188148973811429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95814823632501730596830477 35930558862188148973811429)
          ·
            refine ⟨6736979786660277932589643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35930558862188148973811429 6736979786660277932589643)
            ·
              refine ⟨10105469679990416898884465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6736979786660277932589643 10105469679990416898884465)
              ·
                refine ⟨7579102259992812674163349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10105469679990416898884465 7579102259992812674163349)
                ·
                  refine ⟨355270418437163094101407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7579102259992812674163349 355270418437163094101407)
                  ·
                    rfl

theorem cell21_1556745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 6].length) (baseStart_1556745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1556745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1556745 prefixEnd_1556745 := by exact prefixLift 1556745
  have htrace : WordTrace (prefixWord ++ tailWord_1556745) baseStart_1556745 baseEnd_1556745 := by
    simpa [prefixWord, tailWord_1556745, baseEnd_1556745] using wordTrace_append hprefix tailTrace_1556745
  have hstable : (prefixWord ++ tailWord_1556745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556745).length < 2 ^ (prefixWord ++ tailWord_1556745).sum := by decide
  have hdescent : baseEnd_1556745 < baseStart_1556745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556765 : List Nat := [1, 4, 2, 3, 2, 2, 1, 1, 5]
def baseStart_1556765 : Nat := 118140960795 + 1556765 * 2 ^ 59
def prefixEnd_1556765 : Nat := 4983230072969 + 3 ^ 40 * 1556765 * 2
def baseEnd_1556765 : Nat := 355274982709647503768033

theorem tailTrace_1556765 : CollatzResearch.WordTrace tailWord_1556765 prefixEnd_1556765 355274982709647503768033 := by
  unfold tailWord_1556765
  simp only [CollatzResearch.WordTrace]
  refine ⟨56779884205113754139775749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37853256136742502759850499 56779884205113754139775749)
  ·
    refine ⟨10646228288458828901207953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56779884205113754139775749 10646228288458828901207953)
    ·
      refine ⟨7984671216344121675905965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10646228288458828901207953 7984671216344121675905965)
      ·
        refine ⟨2994251706129045628464737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7984671216344121675905965 2994251706129045628464737)
        ·
          refine ⟨2245688779596784221348553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2994251706129045628464737 2245688779596784221348553)
          ·
            refine ⟨1684266584697588166011415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2245688779596784221348553 1684266584697588166011415)
            ·
              refine ⟨2526399877046382249017123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1684266584697588166011415 2526399877046382249017123)
              ·
                refine ⟨3789599815569573373525685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2526399877046382249017123 3789599815569573373525685)
                ·
                  refine ⟨355274982709647503768033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3789599815569573373525685 355274982709647503768033)
                  ·
                    rfl

theorem cell21_1556765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_1556765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1556765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1556765 prefixEnd_1556765 := by exact prefixLift 1556765
  have htrace : WordTrace (prefixWord ++ tailWord_1556765) baseStart_1556765 baseEnd_1556765 := by
    simpa [prefixWord, tailWord_1556765, baseEnd_1556765] using wordTrace_append hprefix tailTrace_1556765
  have hstable : (prefixWord ++ tailWord_1556765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556765).length < 2 ^ (prefixWord ++ tailWord_1556765).sum := by decide
  have hdescent : baseEnd_1556765 < baseStart_1556765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556948 : List Nat := [2, 4, 1, 2, 2, 3, 2, 1, 4]
def baseStart_1556948 : Nat := 118140960795 + 1556948 * 2 ^ 59
def prefixEnd_1556948 : Nat := 4983230072969 + 3 ^ 40 * 1556948 * 2
def baseEnd_1556948 : Nat := 355316745802879852217659

theorem tailTrace_1556948 : CollatzResearch.WordTrace tailWord_1556948 prefixEnd_1556948 355316745802879852217659 := by
  unfold tailWord_1556948
  simp only [CollatzResearch.WordTrace]
  refine ⟨28393279381725388196843749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37857705842300517595791665 28393279381725388196843749)
  ·
    refine ⟨5323739884073510286908203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28393279381725388196843749 5323739884073510286908203)
    ·
      refine ⟨7985609826110265430362305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5323739884073510286908203 7985609826110265430362305)
      ·
        refine ⟨5989207369582699072771729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7985609826110265430362305 5989207369582699072771729)
        ·
          refine ⟨4491905527187024304578797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5989207369582699072771729 4491905527187024304578797)
          ·
            refine ⟨1684464572695134114217049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4491905527187024304578797 1684464572695134114217049)
            ·
              refine ⟨1263348429521350585662787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1684464572695134114217049 1263348429521350585662787)
              ·
                refine ⟨1895022644282025878494181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1263348429521350585662787 1895022644282025878494181)
                ·
                  refine ⟨355316745802879852217659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1895022644282025878494181 355316745802879852217659)
                  ·
                    rfl

theorem cell21_1556948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_1556948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1556948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1556948 prefixEnd_1556948 := by exact prefixLift 1556948
  have htrace : WordTrace (prefixWord ++ tailWord_1556948) baseStart_1556948 baseEnd_1556948 := by
    simpa [prefixWord, tailWord_1556948, baseEnd_1556948] using wordTrace_append hprefix tailTrace_1556948
  have hstable : (prefixWord ++ tailWord_1556948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556948).length < 2 ^ (prefixWord ++ tailWord_1556948).sum := by decide
  have hdescent : baseEnd_1556948 < baseStart_1556948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556993 : List Nat := [1, 2, 4, 1, 3, 1, 4, 2, 3]
def baseStart_1556993 : Nat := 118140960795 + 1556993 * 2 ^ 59
def prefixEnd_1556993 : Nat := 4983230072969 + 3 ^ 40 * 1556993 * 2
def baseEnd_1556993 : Nat := 355327015415969773967567

theorem tailTrace_1556993 : CollatzResearch.WordTrace tailWord_1556993 prefixEnd_1556993 355327015415969773967567 := by
  unfold tailWord_1556993
  simp only [CollatzResearch.WordTrace]
  refine ⟨56788200048287749079075633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37858800032191832719383755 56788200048287749079075633)
  ·
    refine ⟨42591150036215811809306725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56788200048287749079075633 42591150036215811809306725)
    ·
      refine ⟨7985840631790464714245011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42591150036215811809306725 7985840631790464714245011)
      ·
        refine ⟨11978760947685697071367517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7985840631790464714245011 11978760947685697071367517)
        ·
          refine ⟨4492035355382136401762819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11978760947685697071367517 4492035355382136401762819)
          ·
            refine ⟨6738053033073204602644229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4492035355382136401762819 6738053033073204602644229)
            ·
              refine ⟨1263384943701225862995793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6738053033073204602644229 1263384943701225862995793)
              ·
                refine ⟨947538707775919397246845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1263384943701225862995793 947538707775919397246845)
                ·
                  refine ⟨355327015415969773967567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 947538707775919397246845 355327015415969773967567)
                  ·
                    rfl

theorem cell21_1556993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 2, 3].length) (baseStart_1556993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1556993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1556993 prefixEnd_1556993 := by exact prefixLift 1556993
  have htrace : WordTrace (prefixWord ++ tailWord_1556993) baseStart_1556993 baseEnd_1556993 := by
    simpa [prefixWord, tailWord_1556993, baseEnd_1556993] using wordTrace_append hprefix tailTrace_1556993
  have hstable : (prefixWord ++ tailWord_1556993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556993).length < 2 ^ (prefixWord ++ tailWord_1556993).sum := by decide
  have hdescent : baseEnd_1556993 < baseStart_1556993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557004 : List Nat := [2, 2, 1, 2, 4, 1, 3, 6]
def baseStart_1557004 : Nat := 118140960795 + 1557004 * 2 ^ 59
def prefixEnd_1557004 : Nat := 4983230072969 + 3 ^ 40 * 1557004 * 2
def baseEnd_1557004 : Nat := 118443175255278733094737

theorem tailTrace_1557004 : CollatzResearch.WordTrace tailWord_1557004 prefixEnd_1557004 118443175255278733094737 := by
  unfold tailWord_1557004
  simp only [CollatzResearch.WordTrace]
  refine ⟨28394300625623948978863033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37859067500831931971817377 28394300625623948978863033)
  ·
    refine ⟨21295725469217961734147275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28394300625623948978863033 21295725469217961734147275)
    ·
      refine ⟨31943588203826942601220913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21295725469217961734147275 31943588203826942601220913)
      ·
        refine ⟨23957691152870206950915685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31943588203826942601220913 23957691152870206950915685)
        ·
          refine ⟨4492067091163163803296691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23957691152870206950915685 4492067091163163803296691)
          ·
            refine ⟨6738100636744745704945037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4492067091163163803296691 6738100636744745704945037)
            ·
              refine ⟨2526787738779279639354389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6738100636744745704945037 2526787738779279639354389)
              ·
                refine ⟨118443175255278733094737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2526787738779279639354389 118443175255278733094737)
                ·
                  rfl

theorem cell21_1557004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 6].length) (baseStart_1557004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1557004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1557004 prefixEnd_1557004 := by exact prefixLift 1557004
  have htrace : WordTrace (prefixWord ++ tailWord_1557004) baseStart_1557004 baseEnd_1557004 := by
    simpa [prefixWord, tailWord_1557004, baseEnd_1557004] using wordTrace_append hprefix tailTrace_1557004
  have hstable : (prefixWord ++ tailWord_1557004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557004).length < 2 ^ (prefixWord ++ tailWord_1557004).sum := by decide
  have hdescent : baseEnd_1557004 < baseStart_1557004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557018 : List Nat := [3, 1, 1, 3, 1, 1, 3, 1, 7]
def baseStart_1557018 : Nat := 118140960795 + 1557018 * 2 ^ 59
def prefixEnd_1557018 : Nat := 4983230072969 + 3 ^ 40 * 1557018 * 2
def baseEnd_1557018 : Nat := 355332720756575286050849

theorem tailTrace_1557018 : CollatzResearch.WordTrace tailWord_1557018 prefixEnd_1557018 355332720756575286050849 := by
  unfold tailWord_1557018
  simp only [CollatzResearch.WordTrace]
  refine ⟨14197277968299294587183927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37859407915464785565823805 14197277968299294587183927)
  ·
    refine ⟨21295916952448941880775891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14197277968299294587183927 21295916952448941880775891)
    ·
      refine ⟨31943875428673412821163837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21295916952448941880775891 31943875428673412821163837)
      ·
        refine ⟨11978953285752529807936439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31943875428673412821163837 11978953285752529807936439)
        ·
          refine ⟨17968429928628794711904659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11978953285752529807936439 17968429928628794711904659)
          ·
            refine ⟨26952644892943192067856989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17968429928628794711904659 26952644892943192067856989)
            ·
              refine ⟨10107241834853697025446371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26952644892943192067856989 10107241834853697025446371)
              ·
                refine ⟨15160862752280545538169557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10107241834853697025446371 15160862752280545538169557)
                ·
                  refine ⟨355332720756575286050849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15160862752280545538169557 355332720756575286050849)
                  ·
                    rfl

theorem cell21_1557018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_1557018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1557018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1557018 prefixEnd_1557018 := by exact prefixLift 1557018
  have htrace : WordTrace (prefixWord ++ tailWord_1557018) baseStart_1557018 baseEnd_1557018 := by
    simpa [prefixWord, tailWord_1557018, baseEnd_1557018] using wordTrace_append hprefix tailTrace_1557018
  have hstable : (prefixWord ++ tailWord_1557018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557018).length < 2 ^ (prefixWord ++ tailWord_1557018).sum := by decide
  have hdescent : baseEnd_1557018 < baseStart_1557018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557021 : List Nat := [1, 4, 2, 2, 1, 3, 3, 5]
def baseStart_1557021 : Nat := 118140960795 + 1557021 * 2 ^ 59
def prefixEnd_1557021 : Nat := 4983230072969 + 3 ^ 40 * 1557021 * 2
def baseEnd_1557021 : Nat := 118444468465815982500281

theorem tailTrace_1557021 : CollatzResearch.WordTrace tailWord_1557021 prefixEnd_1557021 118444468465815982500281 := by
  unfold tailWord_1557021
  simp only [CollatzResearch.WordTrace]
  refine ⟨56789221292186309861094917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37859480861457539907396611 56789221292186309861094917)
  ·
    refine ⟨10647978992284933098955297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56789221292186309861094917 10647978992284933098955297)
    ·
      refine ⟨7985984244213699824216473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10647978992284933098955297 7985984244213699824216473)
      ·
        refine ⟨5989488183160274868162355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7985984244213699824216473 5989488183160274868162355)
        ·
          refine ⟨8984232274740412302243533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5989488183160274868162355 8984232274740412302243533)
          ·
            refine ⟨3369087103027654613341325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8984232274740412302243533 3369087103027654613341325)
            ·
              refine ⟨1263407663635370480002997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3369087103027654613341325 1263407663635370480002997)
              ·
                refine ⟨118444468465815982500281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1263407663635370480002997 118444468465815982500281)
                ·
                  rfl

theorem cell21_1557021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 5].length) (baseStart_1557021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1557021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1557021 prefixEnd_1557021 := by exact prefixLift 1557021
  have htrace : WordTrace (prefixWord ++ tailWord_1557021) baseStart_1557021 baseEnd_1557021 := by
    simpa [prefixWord, tailWord_1557021, baseEnd_1557021] using wordTrace_append hprefix tailTrace_1557021
  have hstable : (prefixWord ++ tailWord_1557021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557021).length < 2 ^ (prefixWord ++ tailWord_1557021).sum := by decide
  have hdescent : baseEnd_1557021 < baseStart_1557021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557049 : List Nat := [1, 2, 1, 5, 1, 1, 3, 1, 6]
def baseStart_1557049 : Nat := 118140960795 + 1557049 * 2 ^ 59
def prefixEnd_1557049 : Nat := 4983230072969 + 3 ^ 40 * 1557049 * 2
def baseEnd_1557049 : Nat := 355339795378926121034119

theorem tailTrace_1557049 : CollatzResearch.WordTrace tailWord_1557049 prefixEnd_1557049 355339795378926121034119 := by
  unfold tailWord_1557049
  simp only [CollatzResearch.WordTrace]
  refine ⟨56790242536084870643114201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37860161690723247095409467 56790242536084870643114201)
  ·
    refine ⟨42592681902063652982335651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56790242536084870643114201 42592681902063652982335651)
    ·
      refine ⟨63889022853095479473503477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42592681902063652982335651 63889022853095479473503477)
      ·
        refine ⟨5989595892477701200640951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63889022853095479473503477 5989595892477701200640951)
        ·
          refine ⟨8984393838716551800961427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5989595892477701200640951 8984393838716551800961427)
          ·
            refine ⟨13476590758074827701442141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8984393838716551800961427 13476590758074827701442141)
            ·
              refine ⟨5053721534278060388040803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13476590758074827701442141 5053721534278060388040803)
              ·
                refine ⟨7580582301417090582061205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5053721534278060388040803 7580582301417090582061205)
                ·
                  refine ⟨355339795378926121034119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7580582301417090582061205 355339795378926121034119)
                  ·
                    rfl

theorem cell21_1557049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 6].length) (baseStart_1557049 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1557049 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1557049 prefixEnd_1557049 := by exact prefixLift 1557049
  have htrace : WordTrace (prefixWord ++ tailWord_1557049) baseStart_1557049 baseEnd_1557049 := by
    simpa [prefixWord, tailWord_1557049, baseEnd_1557049] using wordTrace_append hprefix tailTrace_1557049
  have hstable : (prefixWord ++ tailWord_1557049).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557049).length < 2 ^ (prefixWord ++ tailWord_1557049).sum := by decide
  have hdescent : baseEnd_1557049 < baseStart_1557049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557052 : List Nat := [2, 2, 2, 2, 3, 1, 2, 4, 3]
def baseStart_1557052 : Nat := 118140960795 + 1557052 * 2 ^ 59
def prefixEnd_1557052 : Nat := 4983230072969 + 3 ^ 40 * 1557052 * 2
def baseEnd_1557052 : Nat := 355340480019798782484113

theorem tailTrace_1557052 : CollatzResearch.WordTrace tailWord_1557052 prefixEnd_1557052 355340480019798782484113 := by
  unfold tailWord_1557052
  simp only [CollatzResearch.WordTrace]
  refine ⟨28395175977537001077736705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37860234636716001436982273 28395175977537001077736705)
  ·
    refine ⟨21296381983152750808302529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28395175977537001077736705 21296381983152750808302529)
    ·
      refine ⟨15972286487364563106226897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21296381983152750808302529 15972286487364563106226897)
      ·
        refine ⟨11979214865523422329670173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15972286487364563106226897 11979214865523422329670173)
        ·
          refine ⟨4492205574571283373626315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11979214865523422329670173 4492205574571283373626315)
          ·
            refine ⟨6738308361856925060439473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4492205574571283373626315 6738308361856925060439473)
            ·
              refine ⟨5053731271392693795329605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6738308361856925060439473 5053731271392693795329605)
              ·
                refine ⟨947574613386130086624301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5053731271392693795329605 947574613386130086624301)
                ·
                  refine ⟨355340480019798782484113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 947574613386130086624301 355340480019798782484113)
                  ·
                    rfl

theorem cell21_1557052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 4, 3].length) (baseStart_1557052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1557052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1557052 prefixEnd_1557052 := by exact prefixLift 1557052
  have htrace : WordTrace (prefixWord ++ tailWord_1557052) baseStart_1557052 baseEnd_1557052 := by
    simpa [prefixWord, tailWord_1557052, baseEnd_1557052] using wordTrace_append hprefix tailTrace_1557052
  have hstable : (prefixWord ++ tailWord_1557052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557052).length < 2 ^ (prefixWord ++ tailWord_1557052).sum := by decide
  have hdescent : baseEnd_1557052 < baseStart_1557052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557080 : List Nat := [2, 1, 2, 2, 1, 2, 6, 5]
def baseStart_1557080 : Nat := 118140960795 + 1557080 * 2 ^ 59
def prefixEnd_1557080 : Nat := 4983230072969 + 3 ^ 40 * 1557080 * 2
def baseEnd_1557080 : Nat := 118448956667092318672463

theorem tailTrace_1557080 : CollatzResearch.WordTrace tailWord_1557080 prefixEnd_1557080 118448956667092318672463 := by
  unfold tailWord_1557080
  simp only [CollatzResearch.WordTrace]
  refine ⟨28395686599486281468746347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37860915465981708624995129 28395686599486281468746347)
  ·
    refine ⟨42593529899229422203119521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28395686599486281468746347 42593529899229422203119521)
    ·
      refine ⟨31945147424422066652339641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42593529899229422203119521 31945147424422066652339641)
      ·
        refine ⟨23958860568316549989254731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31945147424422066652339641 23958860568316549989254731)
        ·
          refine ⟨35938290852474824983882097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23958860568316549989254731 35938290852474824983882097)
          ·
            refine ⟨26953718139356118737911573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35938290852474824983882097 26953718139356118737911573)
            ·
              refine ⟨1263455537782318065839605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26953718139356118737911573 1263455537782318065839605)
              ·
                refine ⟨118448956667092318672463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1263455537782318065839605 118448956667092318672463)
                ·
                  rfl

theorem cell21_1557080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 5].length) (baseStart_1557080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1557080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1557080 prefixEnd_1557080 := by exact prefixLift 1557080
  have htrace : WordTrace (prefixWord ++ tailWord_1557080) baseStart_1557080 baseEnd_1557080 := by
    simpa [prefixWord, tailWord_1557080, baseEnd_1557080] using wordTrace_append hprefix tailTrace_1557080
  have hstable : (prefixWord ++ tailWord_1557080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557080).length < 2 ^ (prefixWord ++ tailWord_1557080).sum := by decide
  have hdescent : baseEnd_1557080 < baseStart_1557080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557111 : List Nat := [1, 1, 3, 1, 1, 3, 2, 6, 3]
def baseStart_1557111 : Nat := 118140960795 + 1557111 * 2 ^ 59
def prefixEnd_1557111 : Nat := 4983230072969 + 3 ^ 40 * 1557111 * 2
def baseEnd_1557111 : Nat := 355353944623627791000659

theorem tailTrace_1557111 : CollatzResearch.WordTrace tailWord_1557111 prefixEnd_1557111 355353944623627791000659 := by
  unfold tailWord_1557111
  simp only [CollatzResearch.WordTrace]
  refine ⟨56792503861860255231871187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37861669241240170154580791 56792503861860255231871187)
  ·
    refine ⟨85188755792790382847806781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56792503861860255231871187 85188755792790382847806781)
    ·
      refine ⟨31945783422296393567927543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85188755792790382847806781 31945783422296393567927543)
      ·
        refine ⟨47918675133444590351891315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31945783422296393567927543 47918675133444590351891315)
        ·
          refine ⟨71878012700166885527836973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47918675133444590351891315 71878012700166885527836973)
          ·
            refine ⟨26954254762562582072938865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71878012700166885527836973 26954254762562582072938865)
            ·
              refine ⟨20215691071921936554704149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26954254762562582072938865 20215691071921936554704149)
              ·
                refine ⟨947610518996340776001757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20215691071921936554704149 947610518996340776001757)
                ·
                  refine ⟨355353944623627791000659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 947610518996340776001757 355353944623627791000659)
                  ·
                    rfl

theorem cell21_1557111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 6, 3].length) (baseStart_1557111 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1557111 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1557111 prefixEnd_1557111 := by exact prefixLift 1557111
  have htrace : WordTrace (prefixWord ++ tailWord_1557111) baseStart_1557111 baseEnd_1557111 := by
    simpa [prefixWord, tailWord_1557111, baseEnd_1557111] using wordTrace_append hprefix tailTrace_1557111
  have hstable : (prefixWord ++ tailWord_1557111).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557111).length < 2 ^ (prefixWord ++ tailWord_1557111).sum := by decide
  have hdescent : baseEnd_1557111 < baseStart_1557111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557162 : List Nat := [3, 1, 5, 2, 1, 1, 1, 4, 3]
def baseStart_1557162 : Nat := 118140960795 + 1557162 * 2 ^ 59
def prefixEnd_1557162 : Nat := 4983230072969 + 3 ^ 40 * 1557162 * 2
def baseEnd_1557162 : Nat := 355365583518463035650555

theorem tailTrace_1557162 : CollatzResearch.WordTrace tailWord_1557162 prefixEnd_1557162 355365583518463035650555 := by
  unfold tailWord_1557162
  simp only [CollatzResearch.WordTrace]
  refine ⟨14198590996168872735494435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37862909323116993961318493 14198590996168872735494435)
  ·
    refine ⟨21297886494253309103241653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14198590996168872735494435 21297886494253309103241653)
    ·
      refine ⟨1996676858836247728428905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21297886494253309103241653 1996676858836247728428905)
      ·
        refine ⟨1497507644127185796321679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1996676858836247728428905 1497507644127185796321679)
        ·
          refine ⟨2246261466190778694482519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1497507644127185796321679 2246261466190778694482519)
          ·
            refine ⟨3369392199286168041723779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2246261466190778694482519 3369392199286168041723779)
            ·
              refine ⟨5054088298929252062585669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3369392199286168041723779 5054088298929252062585669)
              ·
                refine ⟨947641556049234761734813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5054088298929252062585669 947641556049234761734813)
                ·
                  refine ⟨355365583518463035650555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 947641556049234761734813 355365583518463035650555)
                  ·
                    rfl

theorem cell21_1557162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 4, 3].length) (baseStart_1557162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1557162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1557162 prefixEnd_1557162 := by exact prefixLift 1557162
  have htrace : WordTrace (prefixWord ++ tailWord_1557162) baseStart_1557162 baseEnd_1557162 := by
    simpa [prefixWord, tailWord_1557162, baseEnd_1557162] using wordTrace_append hprefix tailTrace_1557162
  have hstable : (prefixWord ++ tailWord_1557162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557162).length < 2 ^ (prefixWord ++ tailWord_1557162).sum := by decide
  have hdescent : baseEnd_1557162 < baseStart_1557162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557170 : List Nat := [3, 2, 1, 1, 1, 2, 1, 5, 5]
def baseStart_1557170 : Nat := 118140960795 + 1557170 * 2 ^ 59
def prefixEnd_1557170 : Nat := 4983230072969 + 3 ^ 40 * 1557170 * 2
def baseEnd_1557170 : Nat := 355367409227456799517205

theorem tailTrace_1557170 : CollatzResearch.WordTrace tailWord_1557170 prefixEnd_1557170 355367409227456799517205 := by
  unfold tailWord_1557170
  simp only [CollatzResearch.WordTrace]
  refine ⟨14198663942161627077067241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37863103845764338872179309 14198663942161627077067241)
  ·
    refine ⟨10648997956621220307800431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14198663942161627077067241 10648997956621220307800431)
    ·
      refine ⟨15973496934931830461700647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10648997956621220307800431 15973496934931830461700647)
      ·
        refine ⟨23960245402397745692550971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15973496934931830461700647 23960245402397745692550971)
        ·
          refine ⟨35940368103596618538826457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23960245402397745692550971 35940368103596618538826457)
          ·
            refine ⟨26955276077697463904119843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35940368103596618538826457 26955276077697463904119843)
            ·
              refine ⟨40432914116546195856179765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26955276077697463904119843 40432914116546195856179765)
              ·
                refine ⟨3790585698426205861516853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40432914116546195856179765 3790585698426205861516853)
                ·
                  refine ⟨355367409227456799517205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3790585698426205861516853 355367409227456799517205)
                  ·
                    rfl

theorem cell21_1557170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_1557170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1557170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1557170 prefixEnd_1557170 := by exact prefixLift 1557170
  have htrace : WordTrace (prefixWord ++ tailWord_1557170) baseStart_1557170 baseEnd_1557170 := by
    simpa [prefixWord, tailWord_1557170, baseEnd_1557170] using wordTrace_append hprefix tailTrace_1557170
  have hstable : (prefixWord ++ tailWord_1557170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557170).length < 2 ^ (prefixWord ++ tailWord_1557170).sum := by decide
  have hdescent : baseEnd_1557170 < baseStart_1557170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557173 : List Nat := [1, 3, 3, 3, 1, 3, 1, 6]
def baseStart_1557173 : Nat := 118140960795 + 1557173 * 2 ^ 59
def prefixEnd_1557173 : Nat := 4983230072969 + 3 ^ 40 * 1557173 * 2
def baseEnd_1557173 : Nat := 118456031289443153655733

theorem tailTrace_1557173 : CollatzResearch.WordTrace tailWord_1557173 prefixEnd_1557173 118456031289443153655733 := by
  unfold tailWord_1557173
  simp only [CollatzResearch.WordTrace]
  refine ⟨56794765187635639820628173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37863176791757093213752115 56794765187635639820628173)
  ·
    refine ⟨21298036945363364932735565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56794765187635639820628173 21298036945363364932735565)
    ·
      refine ⟨7986763854511261849775837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21298036945363364932735565 7986763854511261849775837)
      ·
        refine ⟨2995036445441723193665939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7986763854511261849775837 2995036445441723193665939)
        ·
          refine ⟨4492554668162584790498909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2995036445441723193665939 4492554668162584790498909)
          ·
            refine ⟨1684708000560969296437091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4492554668162584790498909 1684708000560969296437091)
            ·
              refine ⟨2527062000841453944655637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1684708000560969296437091 2527062000841453944655637)
              ·
                refine ⟨118456031289443153655733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2527062000841453944655637 118456031289443153655733)
                ·
                  rfl

theorem cell21_1557173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 6].length) (baseStart_1557173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1557173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1557173 prefixEnd_1557173 := by exact prefixLift 1557173
  have htrace : WordTrace (prefixWord ++ tailWord_1557173) baseStart_1557173 baseEnd_1557173 := by
    simpa [prefixWord, tailWord_1557173, baseEnd_1557173] using wordTrace_append hprefix tailTrace_1557173
  have hstable : (prefixWord ++ tailWord_1557173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557173).length < 2 ^ (prefixWord ++ tailWord_1557173).sum := by decide
  have hdescent : baseEnd_1557173 < baseStart_1557173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557215 : List Nat := [1, 1, 2, 3, 2, 4, 8]
def baseStart_1557215 : Nat := 118140960795 + 1557215 * 2 ^ 59
def prefixEnd_1557215 : Nat := 4983230072969 + 3 ^ 40 * 1557215 * 2
def baseEnd_1557215 : Nat := 39486408760060746807457

theorem tailTrace_1557215 : CollatzResearch.WordTrace tailWord_1557215 prefixEnd_1557215 39486408760060746807457 := by
  unfold tailWord_1557215
  simp only [CollatzResearch.WordTrace]
  refine ⟨56796297053483480993657099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37864198035655653995771399 56796297053483480993657099)
  ·
    refine ⟨85194445580225221490485649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56796297053483480993657099 85194445580225221490485649)
    ·
      refine ⟨63895834185168916117864237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85194445580225221490485649 63895834185168916117864237)
      ·
        refine ⟨23960937819438343544199089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63895834185168916117864237 23960937819438343544199089)
        ·
          refine ⟨17970703364578757658149317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23960937819438343544199089 17970703364578757658149317)
          ·
            refine ⟨3369506880858517060902997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17970703364578757658149317 3369506880858517060902997)
            ·
              refine ⟨39486408760060746807457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3369506880858517060902997 39486408760060746807457)
              ·
                rfl

theorem cell21_1557215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 8].length) (baseStart_1557215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1557215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1557215 prefixEnd_1557215 := by exact prefixLift 1557215
  have htrace : WordTrace (prefixWord ++ tailWord_1557215) baseStart_1557215 baseEnd_1557215 := by
    simpa [prefixWord, tailWord_1557215, baseEnd_1557215] using wordTrace_append hprefix tailTrace_1557215
  have hstable : (prefixWord ++ tailWord_1557215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557215).length < 2 ^ (prefixWord ++ tailWord_1557215).sum := by decide
  have hdescent : baseEnd_1557215 < baseStart_1557215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557266 : List Nat := [3, 2, 4, 1, 3, 1, 7]
def baseStart_1557266 : Nat := 118140960795 + 1557266 * 2 ^ 59
def prefixEnd_1557266 : Nat := 4983230072969 + 3 ^ 40 * 1557266 * 2
def baseEnd_1557266 : Nat := 39487701970597996213001

theorem tailTrace_1557266 : CollatzResearch.WordTrace tailWord_1557266 prefixEnd_1557266 39487701970597996213001 := by
  unfold tailWord_1557266
  simp only [CollatzResearch.WordTrace]
  refine ⟨14199539294074679175940913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37865438117532477802509101 14199539294074679175940913)
  ·
    refine ⟨10649654470556009381955685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14199539294074679175940913 10649654470556009381955685)
    ·
      refine ⟨1996810213229251759116691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10649654470556009381955685 1996810213229251759116691)
      ·
        refine ⟨2995215319843877638675037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1996810213229251759116691 2995215319843877638675037)
        ·
          refine ⟨1123205744941454114503139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2995215319843877638675037 1123205744941454114503139)
          ·
            refine ⟨1684808617412181171754709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1123205744941454114503139 1684808617412181171754709)
            ·
              refine ⟨39487701970597996213001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1684808617412181171754709 39487701970597996213001)
              ·
                rfl

theorem cell21_1557266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 7].length) (baseStart_1557266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1557266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1557266 prefixEnd_1557266 := by exact prefixLift 1557266
  have htrace : WordTrace (prefixWord ++ tailWord_1557266) baseStart_1557266 baseEnd_1557266 := by
    simpa [prefixWord, tailWord_1557266, baseEnd_1557266] using wordTrace_append hprefix tailTrace_1557266
  have hstable : (prefixWord ++ tailWord_1557266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557266).length < 2 ^ (prefixWord ++ tailWord_1557266).sum := by decide
  have hdescent : baseEnd_1557266 < baseStart_1557266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557325 : List Nat := [1, 6, 1, 2, 3, 8]
def baseStart_1557325 : Nat := 118140960795 + 1557325 * 2 ^ 59
def prefixEnd_1557325 : Nat := 4983230072969 + 3 ^ 40 * 1557325 * 2
def baseEnd_1557325 : Nat := 13163066012563369423465

theorem tailTrace_1557325 : CollatzResearch.WordTrace tailWord_1557325 prefixEnd_1557325 13163066012563369423465 := by
  unfold tailWord_1557325
  simp only [CollatzResearch.WordTrace]
  refine ⟨56800309083084969780161429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37866872722056646520107619 56800309083084969780161429)
  ·
    refine ⟨2662514488269607958445067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 56800309083084969780161429 2662514488269607958445067)
    ·
      refine ⟨3993771732404411937667601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2662514488269607958445067 3993771732404411937667601)
      ·
        refine ⟨2995328799303308953250701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3993771732404411937667601 2995328799303308953250701)
        ·
          refine ⟨1123248299738740857469013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2995328799303308953250701 1123248299738740857469013)
          ·
            refine ⟨13163066012563369423465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1123248299738740857469013 13163066012563369423465)
            ·
              rfl

theorem cell21_1557325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 8].length) (baseStart_1557325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1557325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1557325 prefixEnd_1557325 := by exact prefixLift 1557325
  have htrace : WordTrace (prefixWord ++ tailWord_1557325) baseStart_1557325 baseEnd_1557325 := by
    simpa [prefixWord, tailWord_1557325, baseEnd_1557325] using wordTrace_append hprefix tailTrace_1557325
  have hstable : (prefixWord ++ tailWord_1557325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557325).length < 2 ^ (prefixWord ++ tailWord_1557325).sum := by decide
  have hdescent : baseEnd_1557325 < baseStart_1557325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557336 : List Nat := [2, 1, 2, 2, 1, 1, 1, 5, 6]
def baseStart_1557336 : Nat := 118140960795 + 1557336 * 2 ^ 59
def prefixEnd_1557336 : Nat := 4983230072969 + 3 ^ 40 * 1557336 * 2
def baseEnd_1557336 : Nat := 355405292689077399750199

theorem tailTrace_1557336 : CollatzResearch.WordTrace tailWord_1557336 prefixEnd_1557336 355405292689077399750199 := by
  unfold tailWord_1557336
  simp only [CollatzResearch.WordTrace]
  refine ⟨28400355143022559329405931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37867140190696745772541241 28400355143022559329405931)
  ·
    refine ⟨42600532714533838994108897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28400355143022559329405931 42600532714533838994108897)
    ·
      refine ⟨31950399535900379245581673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42600532714533838994108897 31950399535900379245581673)
      ·
        refine ⟨23962799651925284434186255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31950399535900379245581673 23962799651925284434186255)
        ·
          refine ⟨35944199477887926651279383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23962799651925284434186255 35944199477887926651279383)
          ·
            refine ⟨53916299216831889976919075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35944199477887926651279383 53916299216831889976919075)
            ·
              refine ⟨80874448825247834965378613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53916299216831889976919075 80874448825247834965378613)
              ·
                refine ⟨7581979577366984528004245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80874448825247834965378613 7581979577366984528004245)
                ·
                  refine ⟨355405292689077399750199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7581979577366984528004245 355405292689077399750199)
                  ·
                    rfl

theorem cell21_1557336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 6].length) (baseStart_1557336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1557336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1557336 prefixEnd_1557336 := by exact prefixLift 1557336
  have htrace : WordTrace (prefixWord ++ tailWord_1557336) baseStart_1557336 baseEnd_1557336 := by
    simpa [prefixWord, tailWord_1557336, baseEnd_1557336] using wordTrace_append hprefix tailTrace_1557336
  have hstable : (prefixWord ++ tailWord_1557336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557336).length < 2 ^ (prefixWord ++ tailWord_1557336).sum := by decide
  have hdescent : baseEnd_1557336 < baseStart_1557336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557432 : List Nat := [2, 1, 2, 1, 2, 6, 1, 3, 3]
def baseStart_1557432 : Nat := 118140960795 + 1557432 * 2 ^ 59
def prefixEnd_1557432 : Nat := 4983230072969 + 3 ^ 40 * 1557432 * 2
def baseEnd_1557432 : Nat := 355427201197002566150003

theorem tailTrace_1557432 : CollatzResearch.WordTrace tailWord_1557432 prefixEnd_1557432 355427201197002566150003 := by
  unfold tailWord_1557432
  simp only [CollatzResearch.WordTrace]
  refine ⟨28402105846848663527153275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37869474462464884702871033 28402105846848663527153275)
  ·
    refine ⟨42603158770272995290729913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28402105846848663527153275 42603158770272995290729913)
    ·
      refine ⟨31952369077704746468047435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42603158770272995290729913 31952369077704746468047435)
      ·
        refine ⟨47928553616557119702071153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31952369077704746468047435 47928553616557119702071153)
        ·
          refine ⟨35946415212417839776553365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47928553616557119702071153 35946415212417839776553365)
          ·
            refine ⟨1684988213082086239525939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 35946415212417839776553365 1684988213082086239525939)
            ·
              refine ⟨2527482319623129359288909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1684988213082086239525939 2527482319623129359288909)
              ·
                refine ⟨947805869858673509733341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2527482319623129359288909 947805869858673509733341)
                ·
                  refine ⟨355427201197002566150003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 947805869858673509733341 355427201197002566150003)
                  ·
                    rfl

theorem cell21_1557432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 3, 3].length) (baseStart_1557432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1557432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1557432 prefixEnd_1557432 := by exact prefixLift 1557432
  have htrace : WordTrace (prefixWord ++ tailWord_1557432) baseStart_1557432 baseEnd_1557432 := by
    simpa [prefixWord, tailWord_1557432, baseEnd_1557432] using wordTrace_append hprefix tailTrace_1557432
  have hstable : (prefixWord ++ tailWord_1557432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557432).length < 2 ^ (prefixWord ++ tailWord_1557432).sum := by decide
  have hdescent : baseEnd_1557432 < baseStart_1557432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557460 : List Nat := [2, 4, 1, 2, 1, 3, 2, 6]
def baseStart_1557460 : Nat := 118140960795 + 1557460 * 2 ^ 59
def prefixEnd_1557460 : Nat := 4983230072969 + 3 ^ 40 * 1557460 * 2
def baseEnd_1557460 : Nat := 118477863726160246561093

theorem tailTrace_1557460 : CollatzResearch.WordTrace tailWord_1557460 prefixEnd_1557460 118477863726160246561093 := by
  unfold tailWord_1557460
  simp only [CollatzResearch.WordTrace]
  refine ⟨28402616468797943918162917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37870155291730591890883889 28402616468797943918162917)
  ·
    refine ⟨5325490587899614484655547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28402616468797943918162917 5325490587899614484655547)
    ·
      refine ⟨7988235881849421726983321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5325490587899614484655547 7988235881849421726983321)
      ·
        refine ⟨5991176911387066295237491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7988235881849421726983321 5991176911387066295237491)
        ·
          refine ⟨8986765367080599442856237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5991176911387066295237491 8986765367080599442856237)
          ·
            refine ⟨3370037012655224791071089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8986765367080599442856237 3370037012655224791071089)
            ·
              refine ⟨2527527759491418593303317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3370037012655224791071089 2527527759491418593303317)
              ·
                refine ⟨118477863726160246561093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2527527759491418593303317 118477863726160246561093)
                ·
                  rfl

theorem cell21_1557460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 6].length) (baseStart_1557460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1557460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1557460 prefixEnd_1557460 := by exact prefixLift 1557460
  have htrace : WordTrace (prefixWord ++ tailWord_1557460) baseStart_1557460 baseEnd_1557460 := by
    simpa [prefixWord, tailWord_1557460, baseEnd_1557460] using wordTrace_append hprefix tailTrace_1557460
  have hstable : (prefixWord ++ tailWord_1557460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557460).length < 2 ^ (prefixWord ++ tailWord_1557460).sum := by decide
  have hdescent : baseEnd_1557460 < baseStart_1557460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557505 : List Nat := [1, 2, 4, 1, 2, 2, 1, 4, 4]
def baseStart_1557505 : Nat := 118140960795 + 1557505 * 2 ^ 59
def prefixEnd_1557505 : Nat := 4983230072969 + 3 ^ 40 * 1557505 * 2
def baseEnd_1557505 : Nat := 355443860791570661433187

theorem tailTrace_1557505 : CollatzResearch.WordTrace tailWord_1557505 prefixEnd_1557505 355443860791570661433187 := by
  unfold tailWord_1557505
  simp only [CollatzResearch.WordTrace]
  refine ⟨56806874222432860521713969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37871249481621907014475979 56806874222432860521713969)
  ·
    refine ⟨42605155666824645391285477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56806874222432860521713969 42605155666824645391285477)
    ·
      refine ⟨7988466687529621010866027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42605155666824645391285477 7988466687529621010866027)
      ·
        refine ⟨11982700031294431516299041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7988466687529621010866027 11982700031294431516299041)
        ·
          refine ⟨8987025023470823637224281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11982700031294431516299041 8987025023470823637224281)
          ·
            refine ⟨6740268767603117727918211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8987025023470823637224281 6740268767603117727918211)
            ·
              refine ⟨10110403151404676591877317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6740268767603117727918211 10110403151404676591877317)
              ·
                refine ⟨1895700590888376860976997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10110403151404676591877317 1895700590888376860976997)
                ·
                  refine ⟨355443860791570661433187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1895700590888376860976997 355443860791570661433187)
                  ·
                    rfl

theorem cell21_1557505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4, 4].length) (baseStart_1557505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1557505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1557505 prefixEnd_1557505 := by exact prefixLift 1557505
  have htrace : WordTrace (prefixWord ++ tailWord_1557505) baseStart_1557505 baseEnd_1557505 := by
    simpa [prefixWord, tailWord_1557505, baseEnd_1557505] using wordTrace_append hprefix tailTrace_1557505
  have hstable : (prefixWord ++ tailWord_1557505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557505).length < 2 ^ (prefixWord ++ tailWord_1557505).sum := by decide
  have hdescent : baseEnd_1557505 < baseStart_1557505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557550 : List Nat := [4, 1, 3, 1, 1, 1, 1, 2, 7]
def baseStart_1557550 : Nat := 118140960795 + 1557550 * 2 ^ 59
def prefixEnd_1557550 : Nat := 4983230072969 + 3 ^ 40 * 1557550 * 2
def baseEnd_1557550 : Nat := 355454130404660583183095

theorem tailTrace_1557550 : CollatzResearch.WordTrace tailWord_1557550 prefixEnd_1557550 355454130404660583183095 := by
  unfold tailWord_1557550
  simp only [CollatzResearch.WordTrace]
  refine ⟨7101064438408729150887763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37872343671513222138068069 7101064438408729150887763)
  ·
    refine ⟨10651596657613093726331645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7101064438408729150887763 10651596657613093726331645)
    ·
      refine ⟨3994348746604910147374367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10651596657613093726331645 3994348746604910147374367)
      ·
        refine ⟨5991523119907365221061551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3994348746604910147374367 5991523119907365221061551)
        ·
          refine ⟨8987284679861047831592327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5991523119907365221061551 8987284679861047831592327)
          ·
            refine ⟨13480927019791571747388491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8987284679861047831592327 13480927019791571747388491)
            ·
              refine ⟨20221390529687357621082737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13480927019791571747388491 20221390529687357621082737)
              ·
                refine ⟨15166042897265518215812053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20221390529687357621082737 15166042897265518215812053)
                ·
                  refine ⟨355454130404660583183095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15166042897265518215812053 355454130404660583183095)
                  ·
                    rfl

theorem cell21_1557550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_1557550 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1557550 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1557550 prefixEnd_1557550 := by exact prefixLift 1557550
  have htrace : WordTrace (prefixWord ++ tailWord_1557550) baseStart_1557550 baseEnd_1557550 := by
    simpa [prefixWord, tailWord_1557550, baseEnd_1557550] using wordTrace_append hprefix tailTrace_1557550
  have hstable : (prefixWord ++ tailWord_1557550).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557550).length < 2 ^ (prefixWord ++ tailWord_1557550).sum := by decide
  have hdescent : baseEnd_1557550 < baseStart_1557550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557671 : List Nat := [1, 1, 6, 2, 1, 10]
def baseStart_1557671 : Nat := 118140960795 + 1557671 * 2 ^ 59
def prefixEnd_1557671 : Nat := 4983230072969 + 3 ^ 40 * 1557671 * 2
def baseEnd_1557671 : Nat := 13165990527895972654303

theorem tailTrace_1557671 : CollatzResearch.WordTrace tailWord_1557671 prefixEnd_1557671 13165990527895972654303 := by
  unfold tailWord_1557671
  simp only [CollatzResearch.WordTrace]
  refine ⟨56812928739831470872256867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37875285826554313914837911 56812928739831470872256867)
  ·
    refine ⟨85219393109747206308385301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56812928739831470872256867 85219393109747206308385301)
    ·
      refine ⟨3994659052019400295705561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 85219393109747206308385301 3994659052019400295705561)
      ·
        refine ⟨2995994289014550221779171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3994659052019400295705561 2995994289014550221779171)
        ·
          refine ⟨4493991433521825332668757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2995994289014550221779171 4493991433521825332668757)
          ·
            refine ⟨13165990527895972654303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4493991433521825332668757 13165990527895972654303)
            ·
              rfl

theorem cell21_1557671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 10].length) (baseStart_1557671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1557671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1557671 prefixEnd_1557671 := by exact prefixLift 1557671
  have htrace : WordTrace (prefixWord ++ tailWord_1557671) baseStart_1557671 baseEnd_1557671 := by
    simpa [prefixWord, tailWord_1557671, baseEnd_1557671] using wordTrace_append hprefix tailTrace_1557671
  have hstable : (prefixWord ++ tailWord_1557671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557671).length < 2 ^ (prefixWord ++ tailWord_1557671).sum := by decide
  have hdescent : baseEnd_1557671 < baseStart_1557671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557674 : List Nat := [3, 1, 5, 1, 1, 1, 1, 4, 4]
def baseStart_1557674 : Nat := 118140960795 + 1557674 * 2 ^ 59
def prefixEnd_1557674 : Nat := 4983230072969 + 3 ^ 40 * 1557674 * 2
def baseEnd_1557674 : Nat := 355482428894063923116175

theorem tailTrace_1557674 : CollatzResearch.WordTrace tailWord_1557674 prefixEnd_1557674 355482428894063923116175 := by
  unfold tailWord_1557674
  simp only [CollatzResearch.WordTrace]
  refine ⟨14203259539705150596154019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37875358772547068256410717 14203259539705150596154019)
  ·
    refine ⟨21304889309557725894231029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14203259539705150596154019 21304889309557725894231029)
    ·
      refine ⟨1997333372771036802584159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21304889309557725894231029 1997333372771036802584159)
      ·
        refine ⟨2996000059156555203876239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1997333372771036802584159 2996000059156555203876239)
        ·
          refine ⟨4494000088734832805814359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2996000059156555203876239 4494000088734832805814359)
          ·
            refine ⟨6741000133102249208721539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4494000088734832805814359 6741000133102249208721539)
            ·
              refine ⟨10111500199653373813082309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6741000133102249208721539 10111500199653373813082309)
              ·
                refine ⟨1895906287435007589952933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10111500199653373813082309 1895906287435007589952933)
                ·
                  refine ⟨355482428894063923116175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1895906287435007589952933 355482428894063923116175)
                  ·
                    rfl

theorem cell21_1557674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 4, 4].length) (baseStart_1557674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1557674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1557674 prefixEnd_1557674 := by exact prefixLift 1557674
  have htrace : WordTrace (prefixWord ++ tailWord_1557674) baseStart_1557674 baseEnd_1557674 := by
    simpa [prefixWord, tailWord_1557674, baseEnd_1557674] using wordTrace_append hprefix tailTrace_1557674
  have hstable : (prefixWord ++ tailWord_1557674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557674).length < 2 ^ (prefixWord ++ tailWord_1557674).sum := by decide
  have hdescent : baseEnd_1557674 < baseStart_1557674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557733 : List Nat := [1, 3, 1, 4, 3, 1, 1, 1, 6]
def baseStart_1557733 : Nat := 118140960795 + 1557733 * 2 ^ 59
def prefixEnd_1557733 : Nat := 4983230072969 + 3 ^ 40 * 1557733 * 2
def baseEnd_1557733 : Nat := 355495893497892931632721

theorem tailTrace_1557733 : CollatzResearch.WordTrace tailWord_1557733 prefixEnd_1557733 355495893497892931632721 := by
  unfold tailWord_1557733
  simp only [CollatzResearch.WordTrace]
  refine ⟨56815190065606855461013853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37876793377071236974009235 56815190065606855461013853)
  ·
    refine ⟨21305696274602570797880195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56815190065606855461013853 21305696274602570797880195)
    ·
      refine ⟨31958544411903856196820293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21305696274602570797880195 31958544411903856196820293)
      ·
        refine ⟨5992227077231973036903805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31958544411903856196820293 5992227077231973036903805)
        ·
          refine ⟨2247085153961989888838927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5992227077231973036903805 2247085153961989888838927)
          ·
            refine ⟨3370627730942984833258391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2247085153961989888838927 3370627730942984833258391)
            ·
              refine ⟨5055941596414477249887587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3370627730942984833258391 5055941596414477249887587)
              ·
                refine ⟨7583912394621715874831381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5055941596414477249887587 7583912394621715874831381)
                ·
                  refine ⟨355495893497892931632721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7583912394621715874831381 355495893497892931632721)
                  ·
                    rfl

theorem cell21_1557733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 6].length) (baseStart_1557733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1557733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1557733 prefixEnd_1557733 := by exact prefixLift 1557733
  have htrace : WordTrace (prefixWord ++ tailWord_1557733) baseStart_1557733 baseEnd_1557733 := by
    simpa [prefixWord, tailWord_1557733, baseEnd_1557733] using wordTrace_append hprefix tailTrace_1557733
  have hstable : (prefixWord ++ tailWord_1557733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557733).length < 2 ^ (prefixWord ++ tailWord_1557733).sum := by decide
  have hdescent : baseEnd_1557733 < baseStart_1557733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557764 : List Nat := [2, 3, 2, 2, 2, 1, 4, 5]
def baseStart_1557764 : Nat := 118140960795 + 1557764 * 2 ^ 59
def prefixEnd_1557764 : Nat := 4983230072969 + 3 ^ 40 * 1557764 * 2
def baseEnd_1557764 : Nat := 118500989373414588871997

theorem tailTrace_1557764 : CollatzResearch.WordTrace tailWord_1557764 prefixEnd_1557764 118500989373414588871997 := by
  unfold tailWord_1557764
  simp only [CollatzResearch.WordTrace]
  refine ⟨28408160364247273877696173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37877547152329698503594897 28408160364247273877696173)
  ·
    refine ⟨10653060136592727704136065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28408160364247273877696173 10653060136592727704136065)
    ·
      refine ⟨7989795102444545778102049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10653060136592727704136065 7989795102444545778102049)
      ·
        refine ⟨5992346326833409333576537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7989795102444545778102049 5992346326833409333576537)
        ·
          refine ⟨4494259745125057000182403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5992346326833409333576537 4494259745125057000182403)
          ·
            refine ⟨6741389617687585500273605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4494259745125057000182403 6741389617687585500273605)
            ·
              refine ⟨1264010553316422281301301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6741389617687585500273605 1264010553316422281301301)
              ·
                refine ⟨118500989373414588871997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1264010553316422281301301 118500989373414588871997)
                ·
                  rfl

theorem cell21_1557764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 5].length) (baseStart_1557764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1557764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1557764 prefixEnd_1557764 := by exact prefixLift 1557764
  have htrace : WordTrace (prefixWord ++ tailWord_1557764) baseStart_1557764 baseEnd_1557764 := by
    simpa [prefixWord, tailWord_1557764, baseEnd_1557764] using wordTrace_append hprefix tailTrace_1557764
  have hstable : (prefixWord ++ tailWord_1557764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557764).length < 2 ^ (prefixWord ++ tailWord_1557764).sum := by decide
  have hdescent : baseEnd_1557764 < baseStart_1557764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557809 : List Nat := [1, 2, 2, 3, 3, 2, 1, 3, 4]
def baseStart_1557809 : Nat := 118140960795 + 1557809 * 2 ^ 59
def prefixEnd_1557809 : Nat := 4983230072969 + 3 ^ 40 * 1557809 * 2
def baseEnd_1557809 : Nat := 355513237733333688365899

theorem tailTrace_1557809 : CollatzResearch.WordTrace tailWord_1557809 prefixEnd_1557809 355513237733333688365899 := by
  unfold tailWord_1557809
  simp only [CollatzResearch.WordTrace]
  refine ⟨56817962013331520440780481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37878641342221013627186987 56817962013331520440780481)
  ·
    refine ⟨42613471509998640330585361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56817962013331520440780481 42613471509998640330585361)
    ·
      refine ⟨31960103632498980247939021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42613471509998640330585361 31960103632498980247939021)
      ·
        refine ⟨11985038862187117592977133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31960103632498980247939021 11985038862187117592977133)
        ·
          refine ⟨4494389573320169097366425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11985038862187117592977133 4494389573320169097366425)
          ·
            refine ⟨3370792179990126823024819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4494389573320169097366425 3370792179990126823024819)
            ·
              refine ⟨5056188269985190234537229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3370792179990126823024819 5056188269985190234537229)
              ·
                refine ⟨1896070601244446337951461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5056188269985190234537229 1896070601244446337951461)
                ·
                  refine ⟨355513237733333688365899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1896070601244446337951461 355513237733333688365899)
                  ·
                    rfl

theorem cell21_1557809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3, 4].length) (baseStart_1557809 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1557809 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1557809 prefixEnd_1557809 := by exact prefixLift 1557809
  have htrace : WordTrace (prefixWord ++ tailWord_1557809) baseStart_1557809 baseEnd_1557809 := by
    simpa [prefixWord, tailWord_1557809, baseEnd_1557809] using wordTrace_append hprefix tailTrace_1557809
  have hstable : (prefixWord ++ tailWord_1557809).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557809).length < 2 ^ (prefixWord ++ tailWord_1557809).sum := by decide
  have hdescent : baseEnd_1557809 < baseStart_1557809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557913 : List Nat := [1, 2, 1, 2, 1, 5, 1, 3, 5]
def baseStart_1557913 : Nat := 118140960795 + 1557913 * 2 ^ 59
def prefixEnd_1557913 : Nat := 4983230072969 + 3 ^ 40 * 1557913 * 2
def baseEnd_1557913 : Nat := 355536971950252618632353

theorem tailTrace_1557913 : CollatzResearch.WordTrace tailWord_1557913 prefixEnd_1557913 355536971950252618632353 := by
  unfold tailWord_1557913
  simp only [CollatzResearch.WordTrace]
  refine ⟨56821755204954746202566393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37881170136636497468377595 56821755204954746202566393)
  ·
    refine ⟨42616316403716059651924795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56821755204954746202566393 42616316403716059651924795)
    ·
      refine ⟨63924474605574089477887193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42616316403716059651924795 63924474605574089477887193)
      ·
        refine ⟨47943355954180567108415395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63924474605574089477887193 47943355954180567108415395)
        ·
          refine ⟨71915033931270850662623093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47943355954180567108415395 71915033931270850662623093)
          ·
            refine ⟨6742034431056642249620915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71915033931270850662623093 6742034431056642249620915)
            ·
              refine ⟨10113051646584963374431373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6742034431056642249620915 10113051646584963374431373)
              ·
                refine ⟨3792394367469361265411765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10113051646584963374431373 3792394367469361265411765)
                ·
                  refine ⟨355536971950252618632353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3792394367469361265411765 355536971950252618632353)
                  ·
                    rfl

theorem cell21_1557913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 5].length) (baseStart_1557913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1557913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1557913 prefixEnd_1557913 := by exact prefixLift 1557913
  have htrace : WordTrace (prefixWord ++ tailWord_1557913) baseStart_1557913 baseEnd_1557913 := by
    simpa [prefixWord, tailWord_1557913, baseEnd_1557913] using wordTrace_append hprefix tailTrace_1557913
  have hstable : (prefixWord ++ tailWord_1557913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557913).length < 2 ^ (prefixWord ++ tailWord_1557913).sum := by decide
  have hdescent : baseEnd_1557913 < baseStart_1557913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557933 : List Nat := [1, 5, 2, 2, 1, 3, 2, 5]
def baseStart_1557933 : Nat := 118140960795 + 1557933 * 2 ^ 59
def prefixEnd_1557933 : Nat := 4983230072969 + 3 ^ 40 * 1557933 * 2
def baseEnd_1557933 : Nat := 118513845407579009432993

theorem tailTrace_1557933 : CollatzResearch.WordTrace tailWord_1557933 prefixEnd_1557933 118513845407579009432993 := by
  unfold tailWord_1557933
  simp only [CollatzResearch.WordTrace]
  refine ⟨56822484664882289618294453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37881656443254859745529635 56822484664882289618294453)
  ·
    refine ⟨5327107937332714651715105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56822484664882289618294453 5327107937332714651715105)
    ·
      refine ⟨3995330952999535988786329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5327107937332714651715105 3995330952999535988786329)
      ·
        refine ⟨2996498214749651991589747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3995330952999535988786329 2996498214749651991589747)
        ·
          refine ⟨4494747322124477987384621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2996498214749651991589747 4494747322124477987384621)
          ·
            refine ⟨1685530245796679245269233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4494747322124477987384621 1685530245796679245269233)
            ·
              refine ⟨1264147684347509433951925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1685530245796679245269233 1264147684347509433951925)
              ·
                refine ⟨118513845407579009432993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1264147684347509433951925 118513845407579009432993)
                ·
                  rfl

theorem cell21_1557933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 5].length) (baseStart_1557933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1557933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1557933 prefixEnd_1557933 := by exact prefixLift 1557933
  have htrace : WordTrace (prefixWord ++ tailWord_1557933) baseStart_1557933 baseEnd_1557933 := by
    simpa [prefixWord, tailWord_1557933, baseEnd_1557933] using wordTrace_append hprefix tailTrace_1557933
  have hstable : (prefixWord ++ tailWord_1557933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557933).length < 2 ^ (prefixWord ++ tailWord_1557933).sum := by decide
  have hdescent : baseEnd_1557933 < baseStart_1557933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557964 : List Nat := [2, 2, 1, 4, 2, 2, 3, 2, 3]
def baseStart_1557964 : Nat := 118140960795 + 1557964 * 2 ^ 59
def prefixEnd_1557964 : Nat := 4983230072969 + 3 ^ 40 * 1557964 * 2
def baseEnd_1557964 : Nat := 355548610845087863282249

theorem tailTrace_1557964 : CollatzResearch.WordTrace tailWord_1557964 prefixEnd_1557964 355548610845087863282249 := by
  unfold tailWord_1557964
  simp only [CollatzResearch.WordTrace]
  refine ⟨28411807663884990956336473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37882410218513321275115297 28411807663884990956336473)
  ·
    refine ⟨21308855747913743217252355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28411807663884990956336473 21308855747913743217252355)
    ·
      refine ⟨31963283621870614825878533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21308855747913743217252355 31963283621870614825878533)
      ·
        refine ⟨5993115679100740279852225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31963283621870614825878533 5993115679100740279852225)
        ·
          refine ⟨4494836759325555209889169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5993115679100740279852225 4494836759325555209889169)
          ·
            refine ⟨3371127569494166407416877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4494836759325555209889169 3371127569494166407416877)
            ·
              refine ⟨1264172838560312402781329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3371127569494166407416877 1264172838560312402781329)
              ·
                refine ⟨948129628920234302085997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1264172838560312402781329 948129628920234302085997)
                ·
                  refine ⟨355548610845087863282249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 948129628920234302085997 355548610845087863282249)
                  ·
                    rfl

theorem cell21_1557964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 2, 3].length) (baseStart_1557964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1557964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1557964 prefixEnd_1557964 := by exact prefixLift 1557964
  have htrace : WordTrace (prefixWord ++ tailWord_1557964) baseStart_1557964 baseEnd_1557964 := by
    simpa [prefixWord, tailWord_1557964, baseEnd_1557964] using wordTrace_append hprefix tailTrace_1557964
  have hstable : (prefixWord ++ tailWord_1557964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557964).length < 2 ^ (prefixWord ++ tailWord_1557964).sum := by decide
  have hdescent : baseEnd_1557964 < baseStart_1557964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557978 : List Nat := [3, 1, 1, 2, 3, 4, 2, 1, 4]
def baseStart_1557978 : Nat := 118140960795 + 1557978 * 2 ^ 59
def prefixEnd_1557978 : Nat := 4983230072969 + 3 ^ 40 * 1557978 * 2
def baseEnd_1557978 : Nat := 355551805835826950048887

theorem tailTrace_1557978 : CollatzResearch.WordTrace tailWord_1557978 prefixEnd_1557978 355551805835826950048887 := by
  unfold tailWord_1557978
  simp only [CollatzResearch.WordTrace]
  refine ⟨14206031487429815575920647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37882750633146174869121725 14206031487429815575920647)
  ·
    refine ⟨21309047231144723363880971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14206031487429815575920647 21309047231144723363880971)
    ·
      refine ⟨31963570846717085045821457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21309047231144723363880971 31963570846717085045821457)
      ·
        refine ⟨23972678135037813784366093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31963570846717085045821457 23972678135037813784366093)
        ·
          refine ⟨8989754300639180169137285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23972678135037813784366093 8989754300639180169137285)
          ·
            refine ⟨1685578931369846281713241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8989754300639180169137285 1685578931369846281713241)
            ·
              refine ⟨1264184198527384711284931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1685578931369846281713241 1264184198527384711284931)
              ·
                refine ⟨1896276297791077066927397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1264184198527384711284931 1896276297791077066927397)
                ·
                  refine ⟨355551805835826950048887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1896276297791077066927397 355551805835826950048887)
                  ·
                    rfl

theorem cell21_1557978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 1, 4].length) (baseStart_1557978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1557978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1557978 prefixEnd_1557978 := by exact prefixLift 1557978
  have htrace : WordTrace (prefixWord ++ tailWord_1557978) baseStart_1557978 baseEnd_1557978 := by
    simpa [prefixWord, tailWord_1557978, baseEnd_1557978] using wordTrace_append hprefix tailTrace_1557978
  have hstable : (prefixWord ++ tailWord_1557978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557978).length < 2 ^ (prefixWord ++ tailWord_1557978).sum := by decide
  have hdescent : baseEnd_1557978 < baseStart_1557978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558003 : List Nat := [1, 1, 1, 2, 2, 2, 2, 4, 6]
def baseStart_1558003 : Nat := 118140960795 + 1558003 * 2 ^ 59
def prefixEnd_1558003 : Nat := 4983230072969 + 3 ^ 40 * 1558003 * 2
def baseEnd_1558003 : Nat := 355557511176432462132169

theorem tailTrace_1558003 : CollatzResearch.WordTrace tailWord_1558003 prefixEnd_1558003 355557511176432462132169 := by
  unfold tailWord_1558003
  simp only [CollatzResearch.WordTrace]
  refine ⟨56825037774628691573342663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37883358516419127715561775 56825037774628691573342663)
  ·
    refine ⟨85237556661943037360013995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56825037774628691573342663 85237556661943037360013995)
    ·
      refine ⟨127856334992914556040020993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85237556661943037360013995 127856334992914556040020993)
      ·
        refine ⟨95892251244685917030015745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127856334992914556040020993 95892251244685917030015745)
        ·
          refine ⟨71919188433514437772511809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95892251244685917030015745 71919188433514437772511809)
          ·
            refine ⟨53939391325135828329383857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71919188433514437772511809 53939391325135828329383857)
            ·
              refine ⟨40454543493851871247037893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53939391325135828329383857 40454543493851871247037893)
              ·
                refine ⟨7585226905097225858819605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40454543493851871247037893 7585226905097225858819605)
                ·
                  refine ⟨355557511176432462132169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7585226905097225858819605 355557511176432462132169)
                  ·
                    rfl

theorem cell21_1558003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 6].length) (baseStart_1558003 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1558003 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1558003 prefixEnd_1558003 := by exact prefixLift 1558003
  have htrace : WordTrace (prefixWord ++ tailWord_1558003) baseStart_1558003 baseEnd_1558003 := by
    simpa [prefixWord, tailWord_1558003, baseEnd_1558003] using wordTrace_append hprefix tailTrace_1558003
  have hstable : (prefixWord ++ tailWord_1558003).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558003).length < 2 ^ (prefixWord ++ tailWord_1558003).sum := by decide
  have hdescent : baseEnd_1558003 < baseStart_1558003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558023 : List Nat := [1, 1, 4, 3, 2, 2, 1, 4, 3]
def baseStart_1558023 : Nat := 118140960795 + 1558023 * 2 ^ 59
def prefixEnd_1558023 : Nat := 4983230072969 + 3 ^ 40 * 1558023 * 2
def baseEnd_1558023 : Nat := 355562075448916871798795

theorem tailTrace_1558023 : CollatzResearch.WordTrace tailWord_1558023 prefixEnd_1558023 355562075448916871798795 := by
  unfold tailWord_1558023
  simp only [CollatzResearch.WordTrace]
  refine ⟨56825767234556234989070723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37883844823037489992713815 56825767234556234989070723)
  ·
    refine ⟨85238650851834352483606085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56825767234556234989070723 85238650851834352483606085)
    ·
      refine ⟨15982247034718941090676141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85238650851834352483606085 15982247034718941090676141)
      ·
        refine ⟨5993342638019602909003553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15982247034718941090676141 5993342638019602909003553)
        ·
          refine ⟨4495006978514702181752665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5993342638019602909003553 4495006978514702181752665)
          ·
            refine ⟨3371255233886026636314499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4495006978514702181752665 3371255233886026636314499)
            ·
              refine ⟨5056882850829039954471749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3371255233886026636314499 5056882850829039954471749)
              ·
                refine ⟨948165534530444991463453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5056882850829039954471749 948165534530444991463453)
                ·
                  refine ⟨355562075448916871798795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 948165534530444991463453 355562075448916871798795)
                  ·
                    rfl

theorem cell21_1558023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 4, 3].length) (baseStart_1558023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1558023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1558023 prefixEnd_1558023 := by exact prefixLift 1558023
  have htrace : WordTrace (prefixWord ++ tailWord_1558023) baseStart_1558023 baseEnd_1558023 := by
    simpa [prefixWord, tailWord_1558023, baseEnd_1558023] using wordTrace_append hprefix tailTrace_1558023
  have hstable : (prefixWord ++ tailWord_1558023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558023).length < 2 ^ (prefixWord ++ tailWord_1558023).sum := by decide
  have hdescent : baseEnd_1558023 < baseStart_1558023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558186 : List Nat := [3, 1, 5, 12]
def baseStart_1558186 : Nat := 118140960795 + 1558186 * 2 ^ 59
def prefixEnd_1558186 : Nat := 4983230072969 + 3 ^ 40 * 1558186 * 2
def baseEnd_1558186 : Nat := 1463371499052118562065

theorem tailTrace_1558186 : CollatzResearch.WordTrace tailWord_1558186 prefixEnd_1558186 1463371499052118562065 := by
  unfold tailWord_1558186
  simp only [CollatzResearch.WordTrace]
  refine ⟨14207928083241428456813603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37887808221977142551502941 14207928083241428456813603)
  ·
    refine ⟨21311892124862142685220405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14207928083241428456813603 21311892124862142685220405)
    ·
      refine ⟨1997989886705825876739413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21311892124862142685220405 1997989886705825876739413)
      ·
        refine ⟨1463371499052118562065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 1997989886705825876739413 1463371499052118562065)
        ·
          rfl

theorem cell21_1558186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 12].length) (baseStart_1558186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1558186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1558186 prefixEnd_1558186 := by exact prefixLift 1558186
  have htrace : WordTrace (prefixWord ++ tailWord_1558186) baseStart_1558186 baseEnd_1558186 := by
    simpa [prefixWord, tailWord_1558186, baseEnd_1558186] using wordTrace_append hprefix tailTrace_1558186
  have hstable : (prefixWord ++ tailWord_1558186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558186).length < 2 ^ (prefixWord ++ tailWord_1558186).sum := by decide
  have hdescent : baseEnd_1558186 < baseStart_1558186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558189 : List Nat := [1, 5, 2, 1, 1, 1, 4, 2, 4]
def baseStart_1558189 : Nat := 118140960795 + 1558189 * 2 ^ 59
def prefixEnd_1558189 : Nat := 4983230072969 + 3 ^ 40 * 1558189 * 2
def baseEnd_1558189 : Nat := 355599958910537472031789

theorem tailTrace_1558189 : CollatzResearch.WordTrace tailWord_1558189 prefixEnd_1558189 355599958910537472031789 := by
  unfold tailWord_1558189
  simp only [CollatzResearch.WordTrace]
  refine ⟨56831821751954845339613621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37887881167969896893075747 56831821751954845339613621)
  ·
    refine ⟨5327983289245766750588777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56831821751954845339613621 5327983289245766750588777)
    ·
      refine ⟨3995987466934325062941583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5327983289245766750588777 3995987466934325062941583)
      ·
        refine ⟨5993981200401487594412375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3995987466934325062941583 5993981200401487594412375)
        ·
          refine ⟨8990971800602231391618563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5993981200401487594412375 8990971800602231391618563)
          ·
            refine ⟨13486457700903347087427845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8990971800602231391618563 13486457700903347087427845)
            ·
              refine ⟨2528710818919377578892721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13486457700903347087427845 2528710818919377578892721)
              ·
                refine ⟨1896533114189533184169541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2528710818919377578892721 1896533114189533184169541)
                ·
                  refine ⟨355599958910537472031789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1896533114189533184169541 355599958910537472031789)
                  ·
                    rfl

theorem cell21_1558189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_1558189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1558189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1558189 prefixEnd_1558189 := by exact prefixLift 1558189
  have htrace : WordTrace (prefixWord ++ tailWord_1558189) baseStart_1558189 baseEnd_1558189 := by
    simpa [prefixWord, tailWord_1558189, baseEnd_1558189] using wordTrace_append hprefix tailTrace_1558189
  have hstable : (prefixWord ++ tailWord_1558189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558189).length < 2 ^ (prefixWord ++ tailWord_1558189).sum := by decide
  have hdescent : baseEnd_1558189 < baseStart_1558189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558200 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 9]
def baseStart_1558200 : Nat := 118140960795 + 1558200 * 2 ^ 59
def prefixEnd_1558200 : Nat := 4983230072969 + 3 ^ 40 * 1558200 * 2
def baseEnd_1558200 : Nat := 355602469260403897348433

theorem tailTrace_1558200 : CollatzResearch.WordTrace tailWord_1558200 prefixEnd_1558200 355602469260403897348433 := by
  unfold tailWord_1558200
  simp only [CollatzResearch.WordTrace]
  refine ⟨28416111477457497109132027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37888148636609996145509369 28416111477457497109132027)
  ·
    refine ⟨42624167216186245663698041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28416111477457497109132027 42624167216186245663698041)
    ·
      refine ⟨31968125412139684247773531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42624167216186245663698041 31968125412139684247773531)
      ·
        refine ⟨47952188118209526371660297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31968125412139684247773531 47952188118209526371660297)
        ·
          refine ⟨35964141088657144778745223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47952188118209526371660297 35964141088657144778745223)
          ·
            refine ⟨53946211632985717168117835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35964141088657144778745223 53946211632985717168117835)
            ·
              refine ⟨80919317449478575752176753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53946211632985717168117835 80919317449478575752176753)
              ·
                refine ⟨60689488087108931814132565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80919317449478575752176753 60689488087108931814132565)
                ·
                  refine ⟨355602469260403897348433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60689488087108931814132565 355602469260403897348433)
                  ·
                    rfl

theorem cell21_1558200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 9].length) (baseStart_1558200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1558200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1558200 prefixEnd_1558200 := by exact prefixLift 1558200
  have htrace : WordTrace (prefixWord ++ tailWord_1558200) baseStart_1558200 baseEnd_1558200 := by
    simpa [prefixWord, tailWord_1558200, baseEnd_1558200] using wordTrace_append hprefix tailTrace_1558200
  have hstable : (prefixWord ++ tailWord_1558200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558200).length < 2 ^ (prefixWord ++ tailWord_1558200).sum := by decide
  have hdescent : baseEnd_1558200 < baseStart_1558200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558220 : List Nat := [2, 2, 1, 5, 2, 1, 3, 5]
def baseStart_1558220 : Nat := 118140960795 + 1558220 * 2 ^ 59
def prefixEnd_1558220 : Nat := 4983230072969 + 3 ^ 40 * 1558220 * 2
def baseEnd_1558220 : Nat := 118535677844296102338353

theorem tailTrace_1558220 : CollatzResearch.WordTrace tailWord_1558220 prefixEnd_1558220 118535677844296102338353 := by
  unfold tailWord_1558220
  simp only [CollatzResearch.WordTrace]
  refine ⟨28416476207421268816996057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37888634943228358422661409 28416476207421268816996057)
  ·
    refine ⟨21312357155565951612747043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28416476207421268816996057 21312357155565951612747043)
    ·
      refine ⟨31968535733348927419120565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21312357155565951612747043 31968535733348927419120565)
      ·
        refine ⟨2997050225001461945542553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31968535733348927419120565 2997050225001461945542553)
        ·
          refine ⟨2247787668751096459156915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2997050225001461945542553 2247787668751096459156915)
          ·
            refine ⟨3371681503126644688735373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2247787668751096459156915 3371681503126644688735373)
            ·
              refine ⟨1264380563672491758275765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3371681503126644688735373 1264380563672491758275765)
              ·
                refine ⟨118535677844296102338353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1264380563672491758275765 118535677844296102338353)
                ·
                  rfl

theorem cell21_1558220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 5].length) (baseStart_1558220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1558220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1558220 prefixEnd_1558220 := by exact prefixLift 1558220
  have htrace : WordTrace (prefixWord ++ tailWord_1558220) baseStart_1558220 baseEnd_1558220 := by
    simpa [prefixWord, tailWord_1558220, baseEnd_1558220] using wordTrace_append hprefix tailTrace_1558220
  have hstable : (prefixWord ++ tailWord_1558220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558220).length < 2 ^ (prefixWord ++ tailWord_1558220).sum := by decide
  have hdescent : baseEnd_1558220 < baseStart_1558220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558231 : List Nat := [1, 1, 3, 2, 1, 3, 2, 2, 6]
def baseStart_1558231 : Nat := 118140960795 + 1558231 * 2 ^ 59
def prefixEnd_1558231 : Nat := 4983230072969 + 3 ^ 40 * 1558231 * 2
def baseEnd_1558231 : Nat := 355609543882754732331703

theorem tailTrace_1558231 : CollatzResearch.WordTrace tailWord_1558231 prefixEnd_1558231 355609543882754732331703 := by
  unfold tailWord_1558231
  simp only [CollatzResearch.WordTrace]
  refine ⟨56833353617802686512642547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37888902411868457675095031 56833353617802686512642547)
  ·
    refine ⟨85250030426704029768963821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56833353617802686512642547 85250030426704029768963821)
    ·
      refine ⟨31968761410014011163361433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85250030426704029768963821 31968761410014011163361433)
      ·
        refine ⟨23976571057510508372521075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31968761410014011163361433 23976571057510508372521075)
        ·
          refine ⟨35964856586265762558781613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23976571057510508372521075 35964856586265762558781613)
          ·
            refine ⟨13486821219849660959543105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35964856586265762558781613 13486821219849660959543105)
            ·
              refine ⟨10115115914887245719657329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13486821219849660959543105 10115115914887245719657329)
              ·
                refine ⟨7586336936165434289742997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10115115914887245719657329 7586336936165434289742997)
                ·
                  refine ⟨355609543882754732331703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7586336936165434289742997 355609543882754732331703)
                  ·
                    rfl

theorem cell21_1558231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 6].length) (baseStart_1558231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1558231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1558231 prefixEnd_1558231 := by exact prefixLift 1558231
  have htrace : WordTrace (prefixWord ++ tailWord_1558231) baseStart_1558231 baseEnd_1558231 := by
    simpa [prefixWord, tailWord_1558231, baseEnd_1558231] using wordTrace_append hprefix tailTrace_1558231
  have hstable : (prefixWord ++ tailWord_1558231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558231).length < 2 ^ (prefixWord ++ tailWord_1558231).sum := by decide
  have hdescent : baseEnd_1558231 < baseStart_1558231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558234 : List Nat := [3, 1, 1, 2, 2, 3, 1, 5, 3]
def baseStart_1558234 : Nat := 118140960795 + 1558234 * 2 ^ 59
def prefixEnd_1558234 : Nat := 4983230072969 + 3 ^ 40 * 1558234 * 2
def baseEnd_1558234 : Nat := 355610228523627393781697

theorem tailTrace_1558234 : CollatzResearch.WordTrace tailWord_1558234 prefixEnd_1558234 355610228523627393781697 := by
  unfold tailWord_1558234
  simp only [CollatzResearch.WordTrace]
  refine ⟨14208365759197954506250439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37888975357861212016667837 14208365759197954506250439)
  ·
    refine ⟨21312548638796931759375659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14208365759197954506250439 21312548638796931759375659)
    ·
      refine ⟨31968822958195397639063489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21312548638796931759375659 31968822958195397639063489)
      ·
        refine ⟨23976617218646548229297617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31968822958195397639063489 23976617218646548229297617)
        ·
          refine ⟨17982462913984911171973213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23976617218646548229297617 17982462913984911171973213)
          ·
            refine ⟨6743423592744341689489955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17982462913984911171973213 6743423592744341689489955)
            ·
              refine ⟨10115135389116512534234933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6743423592744341689489955 10115135389116512534234933)
              ·
                refine ⟨948293942729673050084525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10115135389116512534234933 948293942729673050084525)
                ·
                  refine ⟨355610228523627393781697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 948293942729673050084525 355610228523627393781697)
                  ·
                    rfl

theorem cell21_1558234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 5, 3].length) (baseStart_1558234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1558234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1558234 prefixEnd_1558234 := by exact prefixLift 1558234
  have htrace : WordTrace (prefixWord ++ tailWord_1558234) baseStart_1558234 baseEnd_1558234 := by
    simpa [prefixWord, tailWord_1558234, baseEnd_1558234] using wordTrace_append hprefix tailTrace_1558234
  have hstable : (prefixWord ++ tailWord_1558234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558234).length < 2 ^ (prefixWord ++ tailWord_1558234).sum := by decide
  have hdescent : baseEnd_1558234 < baseStart_1558234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558248 : List Nat := [2, 1, 4, 1, 3, 2, 1, 1, 6]
def baseStart_1558248 : Nat := 118140960795 + 1558248 * 2 ^ 59
def prefixEnd_1558248 : Nat := 4983230072969 + 3 ^ 40 * 1558248 * 2
def baseEnd_1558248 : Nat := 355613423514366480548335

theorem tailTrace_1558248 : CollatzResearch.WordTrace tailWord_1558248 prefixEnd_1558248 355613423514366480548335 := by
  unfold tailWord_1558248
  simp only [CollatzResearch.WordTrace]
  refine ⟨28416986829370549208005699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37889315772494065610674265 28416986829370549208005699)
  ·
    refine ⟨42625480244055823812008549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28416986829370549208005699 42625480244055823812008549)
    ·
      refine ⟨7992277545760466964751603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42625480244055823812008549 7992277545760466964751603)
      ·
        refine ⟨11988416318640700447127405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7992277545760466964751603 11988416318640700447127405)
        ·
          refine ⟨4495656119490262667672777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11988416318640700447127405 4495656119490262667672777)
          ·
            refine ⟨3371742089617697000754583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4495656119490262667672777 3371742089617697000754583)
            ·
              refine ⟨5057613134426545501131875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3371742089617697000754583 5057613134426545501131875)
              ·
                refine ⟨7586419701639818251697813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5057613134426545501131875 7586419701639818251697813)
                ·
                  refine ⟨355613423514366480548335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7586419701639818251697813 355613423514366480548335)
                  ·
                    rfl

theorem cell21_1558248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 6].length) (baseStart_1558248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1558248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1558248 prefixEnd_1558248 := by exact prefixLift 1558248
  have htrace : WordTrace (prefixWord ++ tailWord_1558248) baseStart_1558248 baseEnd_1558248 := by
    simpa [prefixWord, tailWord_1558248, baseEnd_1558248] using wordTrace_append hprefix tailTrace_1558248
  have hstable : (prefixWord ++ tailWord_1558248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558248).length < 2 ^ (prefixWord ++ tailWord_1558248).sum := by decide
  have hdescent : baseEnd_1558248 < baseStart_1558248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558279 : List Nat := [1, 1, 4, 4, 2, 1, 1, 7]
def baseStart_1558279 : Nat := 118140960795 + 1558279 * 2 ^ 59
def prefixEnd_1558279 : Nat := 4983230072969 + 3 ^ 40 * 1558279 * 2
def baseEnd_1558279 : Nat := 118540166045572438510535

theorem tailTrace_1558279 : CollatzResearch.WordTrace tailWord_1558279 prefixEnd_1558279 118540166045572438510535 := by
  unfold tailWord_1558279
  simp only [CollatzResearch.WordTrace]
  refine ⟨56835104321628790710389891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37890069547752527140259927 56835104321628790710389891)
  ·
    refine ⟨85252656482443186065584837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56835104321628790710389891 85252656482443186065584837)
    ·
      refine ⟨15984873090458097387297157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85252656482443186065584837 15984873090458097387297157)
      ·
        refine ⟨2997163704460893260118217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15984873090458097387297157 2997163704460893260118217)
        ·
          refine ⟨2247872778345669945088663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2997163704460893260118217 2247872778345669945088663)
          ·
            refine ⟨3371809167518504917632995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2247872778345669945088663 3371809167518504917632995)
            ·
              refine ⟨5057713751277757376449493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3371809167518504917632995 5057713751277757376449493)
              ·
                refine ⟨118540166045572438510535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5057713751277757376449493 118540166045572438510535)
                ·
                  rfl

theorem cell21_1558279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 7].length) (baseStart_1558279 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1558279 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1558279 prefixEnd_1558279 := by exact prefixLift 1558279
  have htrace : WordTrace (prefixWord ++ tailWord_1558279) baseStart_1558279 baseEnd_1558279 := by
    simpa [prefixWord, tailWord_1558279, baseEnd_1558279] using wordTrace_append hprefix tailTrace_1558279
  have hstable : (prefixWord ++ tailWord_1558279).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558279).length < 2 ^ (prefixWord ++ tailWord_1558279).sum := by decide
  have hdescent : baseEnd_1558279 < baseStart_1558279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558302 : List Nat := [4, 3, 2, 2, 1, 1, 3, 2, 3]
def baseStart_1558302 : Nat := 118140960795 + 1558302 * 2 ^ 59
def prefixEnd_1558302 : Nat := 4983230072969 + 3 ^ 40 * 1558302 * 2
def baseEnd_1558302 : Nat := 355625747050074386648225

theorem tailTrace_1558302 : CollatzResearch.WordTrace tailWord_1558302 prefixEnd_1558302 355625747050074386648225 := by
  unfold tailWord_1558302
  simp only [CollatzResearch.WordTrace]
  refine ⟨7104492900068183204809645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37890628800363643758984773 7104492900068183204809645)
  ·
    refine ⟨2664184837525568701803617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7104492900068183204809645 2664184837525568701803617)
    ·
      refine ⟨1998138628144176526352713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2664184837525568701803617 1998138628144176526352713)
      ·
        refine ⟨1498603971108132394764535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1998138628144176526352713 1498603971108132394764535)
        ·
          refine ⟨2247905956662198592146803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1498603971108132394764535 2247905956662198592146803)
          ·
            refine ⟨3371858934993297888220205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2247905956662198592146803 3371858934993297888220205)
            ·
              refine ⟨1264447100622486708082577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3371858934993297888220205 1264447100622486708082577)
              ·
                refine ⟨948335325466865031061933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1264447100622486708082577 948335325466865031061933)
                ·
                  refine ⟨355625747050074386648225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 948335325466865031061933 355625747050074386648225)
                  ·
                    rfl

theorem cell21_1558302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_1558302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1558302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1558302 prefixEnd_1558302 := by exact prefixLift 1558302
  have htrace : WordTrace (prefixWord ++ tailWord_1558302) baseStart_1558302 baseEnd_1558302 := by
    simpa [prefixWord, tailWord_1558302, baseEnd_1558302] using wordTrace_append hprefix tailTrace_1558302
  have hstable : (prefixWord ++ tailWord_1558302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558302).length < 2 ^ (prefixWord ++ tailWord_1558302).sum := by decide
  have hdescent : baseEnd_1558302 < baseStart_1558302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558307 : List Nat := [1, 1, 1, 4, 2, 1, 4, 1, 6]
def baseStart_1558307 : Nat := 118140960795 + 1558307 * 2 ^ 59
def prefixEnd_1558307 : Nat := 4983230072969 + 3 ^ 40 * 1558307 * 2
def baseEnd_1558307 : Nat := 355626888118195489064881

theorem tailTrace_1558307 : CollatzResearch.WordTrace tailWord_1558307 prefixEnd_1558307 355626888118195489064881 := by
  unfold tailWord_1558307
  simp only [CollatzResearch.WordTrace]
  refine ⟨56836125565527351492409175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37890750377018234328272783 56836125565527351492409175)
  ·
    refine ⟨85254188348291027238613763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56836125565527351492409175 85254188348291027238613763)
    ·
      refine ⟨127881282522436540857920645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85254188348291027238613763 127881282522436540857920645)
      ·
        refine ⟨23977740472956851410860121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127881282522436540857920645 23977740472956851410860121)
        ·
          refine ⟨17983305354717638558145091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23977740472956851410860121 17983305354717638558145091)
          ·
            refine ⟨26974958032076457837217637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17983305354717638558145091 26974958032076457837217637)
            ·
              refine ⟨5057804631014335844478307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26974958032076457837217637 5057804631014335844478307)
              ·
                refine ⟨7586706946521503766717461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5057804631014335844478307 7586706946521503766717461)
                ·
                  refine ⟨355626888118195489064881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7586706946521503766717461 355626888118195489064881)
                  ·
                    rfl

theorem cell21_1558307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 6].length) (baseStart_1558307 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1558307 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1558307 prefixEnd_1558307 := by exact prefixLift 1558307
  have htrace : WordTrace (prefixWord ++ tailWord_1558307) baseStart_1558307 baseEnd_1558307 := by
    simpa [prefixWord, tailWord_1558307, baseEnd_1558307] using wordTrace_append hprefix tailTrace_1558307
  have hstable : (prefixWord ++ tailWord_1558307).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558307).length < 2 ^ (prefixWord ++ tailWord_1558307).sum := by decide
  have hdescent : baseEnd_1558307 < baseStart_1558307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558372 : List Nat := [2, 3, 1, 1, 6, 1, 1, 6]
def baseStart_1558372 : Nat := 118140960795 + 1558372 * 2 ^ 59
def prefixEnd_1558372 : Nat := 4983230072969 + 3 ^ 40 * 1558372 * 2
def baseEnd_1558372 : Nat := 118547240667923273493805

theorem tailTrace_1558372 : CollatzResearch.WordTrace tailWord_1558372 prefixEnd_1558372 118547240667923273493805 := by
  unfold tailWord_1558372
  simp only [CollatzResearch.WordTrace]
  refine ⟨28419248155145933796762685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37892330873527911729016913 28419248155145933796762685)
  ·
    refine ⟨10657218058179725173786007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28419248155145933796762685 10657218058179725173786007)
    ·
      refine ⟨15985827087269587760679011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10657218058179725173786007 15985827087269587760679011)
      ·
        refine ⟨23978740630904381641018517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15985827087269587760679011 23978740630904381641018517)
        ·
          refine ⟨1124003467073642889422743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23978740630904381641018517 1124003467073642889422743)
          ·
            refine ⟨1686005200610464334134115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1124003467073642889422743 1686005200610464334134115)
            ·
              refine ⟨2529007800915696501201173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1686005200610464334134115 2529007800915696501201173)
              ·
                refine ⟨118547240667923273493805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2529007800915696501201173 118547240667923273493805)
                ·
                  rfl

theorem cell21_1558372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 6].length) (baseStart_1558372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1558372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1558372 prefixEnd_1558372 := by exact prefixLift 1558372
  have htrace : WordTrace (prefixWord ++ tailWord_1558372) baseStart_1558372 baseEnd_1558372 := by
    simpa [prefixWord, tailWord_1558372, baseEnd_1558372] using wordTrace_append hprefix tailTrace_1558372
  have hstable : (prefixWord ++ tailWord_1558372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558372).length < 2 ^ (prefixWord ++ tailWord_1558372).sum := by decide
  have hdescent : baseEnd_1558372 < baseStart_1558372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558434 : List Nat := [3, 3, 1, 2, 3, 1, 3, 1, 4]
def baseStart_1558434 : Nat := 118140960795 + 1558434 * 2 ^ 59
def prefixEnd_1558434 : Nat := 4983230072969 + 3 ^ 40 * 1558434 * 2
def baseEnd_1558434 : Nat := 355655871248471490447955

theorem tailTrace_1558434 : CollatzResearch.WordTrace tailWord_1558434 prefixEnd_1558434 355655871248471490447955 := by
  unfold tailWord_1558434
  simp only [CollatzResearch.WordTrace]
  refine ⟨14210189409016813045570589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37893838424044834788188237 14210189409016813045570589)
  ·
    refine ⟨5328821028381304892088971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14210189409016813045570589 5328821028381304892088971)
    ·
      refine ⟨7993231542571957338133457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5328821028381304892088971 7993231542571957338133457)
      ·
        refine ⟨5994923656928968003600093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7993231542571957338133457 5994923656928968003600093)
        ·
          refine ⟨2248096371348363001350035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5994923656928968003600093 2248096371348363001350035)
          ·
            refine ⟨3372144557022544502025053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2248096371348363001350035 3372144557022544502025053)
            ·
              refine ⟨1264554208883454188259395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3372144557022544502025053 1264554208883454188259395)
              ·
                refine ⟨1896831313325181282389093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1264554208883454188259395 1896831313325181282389093)
                ·
                  refine ⟨355655871248471490447955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1896831313325181282389093 355655871248471490447955)
                  ·
                    rfl

theorem cell21_1558434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_1558434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1558434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1558434 prefixEnd_1558434 := by exact prefixLift 1558434
  have htrace : WordTrace (prefixWord ++ tailWord_1558434) baseStart_1558434 baseEnd_1558434 := by
    simpa [prefixWord, tailWord_1558434, baseEnd_1558434] using wordTrace_append hprefix tailTrace_1558434
  have hstable : (prefixWord ++ tailWord_1558434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558434).length < 2 ^ (prefixWord ++ tailWord_1558434).sum := by decide
  have hdescent : baseEnd_1558434 < baseStart_1558434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558493 : List Nat := [1, 4, 3, 1, 3, 1, 1, 3, 4]
def baseStart_1558493 : Nat := 118140960795 + 1558493 * 2 ^ 59
def prefixEnd_1558493 : Nat := 4983230072969 + 3 ^ 40 * 1558493 * 2
def baseEnd_1558493 : Nat := 355669335852300498964501

theorem tailTrace_1558493 : CollatzResearch.WordTrace tailWord_1558493 prefixEnd_1558493 355669335852300498964501 := by
  unfold tailWord_1558493
  simp only [CollatzResearch.WordTrace]
  refine ⟨56842909542853505258680133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37895273028569003505786755 56842909542853505258680133)
  ·
    refine ⟨10658045539285032236002525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56842909542853505258680133 10658045539285032236002525)
    ·
      refine ⟨3996767077231887088500947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10658045539285032236002525 3996767077231887088500947)
      ·
        refine ⟨5995150615847830632751421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3996767077231887088500947 5995150615847830632751421)
        ·
          refine ⟨2248181480942936487281783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5995150615847830632751421 2248181480942936487281783)
          ·
            refine ⟨3372272221414404730922675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2248181480942936487281783 3372272221414404730922675)
            ·
              refine ⟨5058408332121607096384013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3372272221414404730922675 5058408332121607096384013)
              ·
                refine ⟨1896903124545602661144005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5058408332121607096384013 1896903124545602661144005)
                ·
                  refine ⟨355669335852300498964501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1896903124545602661144005 355669335852300498964501)
                  ·
                    rfl

theorem cell21_1558493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_1558493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1558493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1558493 prefixEnd_1558493 := by exact prefixLift 1558493
  have htrace : WordTrace (prefixWord ++ tailWord_1558493) baseStart_1558493 baseEnd_1558493 := by
    simpa [prefixWord, tailWord_1558493, baseEnd_1558493] using wordTrace_append hprefix tailTrace_1558493
  have hstable : (prefixWord ++ tailWord_1558493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558493).length < 2 ^ (prefixWord ++ tailWord_1558493).sum := by decide
  have hdescent : baseEnd_1558493 < baseStart_1558493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558504 : List Nat := [2, 1, 4, 1, 1, 1, 1, 3, 7]
def baseStart_1558504 : Nat := 118140960795 + 1558504 * 2 ^ 59
def prefixEnd_1558504 : Nat := 4983230072969 + 3 ^ 40 * 1558504 * 2
def baseEnd_1558504 : Nat := 355671846202166924281145

theorem tailTrace_1558504 : CollatzResearch.WordTrace tailWord_1558504 prefixEnd_1558504 355671846202166924281145 := by
  unfold tailWord_1558504
  simp only [CollatzResearch.WordTrace]
  refine ⟨28421655372906827068665283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37895540497209102758220377 28421655372906827068665283)
  ·
    refine ⟨42632483059360240602997925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28421655372906827068665283 42632483059360240602997925)
    ·
      refine ⟨7993590573630045113062111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42632483059360240602997925 7993590573630045113062111)
      ·
        refine ⟨11990385860445067669593167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7993590573630045113062111 11990385860445067669593167)
        ·
          refine ⟨17985578790667601504389751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11990385860445067669593167 17985578790667601504389751)
          ·
            refine ⟨26978368186001402256584627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17985578790667601504389751 26978368186001402256584627)
            ·
              refine ⟨40467552279002103384876941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26978368186001402256584627 40467552279002103384876941)
              ·
                refine ⟨15175332104625788769328853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40467552279002103384876941 15175332104625788769328853)
                ·
                  refine ⟨355671846202166924281145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15175332104625788769328853 355671846202166924281145)
                  ·
                    rfl

theorem cell21_1558504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 7].length) (baseStart_1558504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1558504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1558504 prefixEnd_1558504 := by exact prefixLift 1558504
  have htrace : WordTrace (prefixWord ++ tailWord_1558504) baseStart_1558504 baseEnd_1558504 := by
    simpa [prefixWord, tailWord_1558504, baseEnd_1558504] using wordTrace_append hprefix tailTrace_1558504
  have hstable : (prefixWord ++ tailWord_1558504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558504).length < 2 ^ (prefixWord ++ tailWord_1558504).sum := by decide
  have hdescent : baseEnd_1558504 < baseStart_1558504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558642 : List Nat := [3, 2, 1, 2, 2, 4, 7]
def baseStart_1558642 : Nat := 118140960795 + 1558642 * 2 ^ 59
def prefixEnd_1558642 : Nat := 4983230072969 + 3 ^ 40 * 1558642 * 2
def baseEnd_1558642 : Nat := 39522593298034372331207

theorem tailTrace_1558642 : CollatzResearch.WordTrace tailWord_1558642 prefixEnd_1558642 39522593298034372331207 := by
  unfold tailWord_1558642
  simp only [CollatzResearch.WordTrace]
  refine ⟨14212086004828425926463545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37898896012875802470569453 14212086004828425926463545)
  ·
    refine ⟨10659064503621319444847659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14212086004828425926463545 10659064503621319444847659)
    ·
      refine ⟨15988596755431979167271489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10659064503621319444847659 15988596755431979167271489)
      ·
        refine ⟨11991447566573984375453617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15988596755431979167271489 11991447566573984375453617)
        ·
          refine ⟨8993585674930488281590213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11991447566573984375453617 8993585674930488281590213)
          ·
            refine ⟨1686297314049466552798165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8993585674930488281590213 1686297314049466552798165)
            ·
              refine ⟨39522593298034372331207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1686297314049466552798165 39522593298034372331207)
              ·
                rfl

theorem cell21_1558642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 7].length) (baseStart_1558642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1558642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1558642 prefixEnd_1558642 := by exact prefixLift 1558642
  have htrace : WordTrace (prefixWord ++ tailWord_1558642) baseStart_1558642 baseEnd_1558642 := by
    simpa [prefixWord, tailWord_1558642, baseEnd_1558642] using wordTrace_append hprefix tailTrace_1558642
  have hstable : (prefixWord ++ tailWord_1558642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558642).length < 2 ^ (prefixWord ++ tailWord_1558642).sum := by decide
  have hdescent : baseEnd_1558642 < baseStart_1558642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558794 : List Nat := [3, 1, 2, 2, 1, 1, 6, 5]
def baseStart_1558794 : Nat := 118140960795 + 1558794 * 2 ^ 59
def prefixEnd_1558794 : Nat := 4983230072969 + 3 ^ 40 * 1558794 * 2
def baseEnd_1558794 : Nat := 118579342717730288149073

theorem tailTrace_1558794 : CollatzResearch.WordTrace tailWord_1558794 prefixEnd_1558794 118579342717730288149073 := by
  unfold tailWord_1558794
  simp only [CollatzResearch.WordTrace]
  refine ⟨14213471978690758416346859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37902591943175355776924957 14213471978690758416346859)
  ·
    refine ⟨21320207968036137624520289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14213471978690758416346859 21320207968036137624520289)
    ·
      refine ⟨15990155976027103218390217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21320207968036137624520289 15990155976027103218390217)
      ·
        refine ⟨11992616982020327413792663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15990155976027103218390217 11992616982020327413792663)
        ·
          refine ⟨17988925473030491120688995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11992616982020327413792663 17988925473030491120688995)
          ·
            refine ⟨26983388209545736681033493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17988925473030491120688995 26983388209545736681033493)
            ·
              refine ⟨1264846322322456406923445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26983388209545736681033493 1264846322322456406923445)
              ·
                refine ⟨118579342717730288149073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1264846322322456406923445 118579342717730288149073)
                ·
                  rfl

theorem cell21_1558794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 5].length) (baseStart_1558794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1558794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1558794 prefixEnd_1558794 := by exact prefixLift 1558794
  have htrace : WordTrace (prefixWord ++ tailWord_1558794) baseStart_1558794 baseEnd_1558794 := by
    simpa [prefixWord, tailWord_1558794, baseEnd_1558794] using wordTrace_append hprefix tailTrace_1558794
  have hstable : (prefixWord ++ tailWord_1558794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558794).length < 2 ^ (prefixWord ++ tailWord_1558794).sum := by decide
  have hdescent : baseEnd_1558794 < baseStart_1558794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558867 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 9]
def baseStart_1558867 : Nat := 118140960795 + 1558867 * 2 ^ 59
def prefixEnd_1558867 : Nat := 4983230072969 + 3 ^ 40 * 1558867 * 2
def baseEnd_1558867 : Nat := 355754687747758959730403

theorem tailTrace_1558867 : CollatzResearch.WordTrace tailWord_1558867 prefixEnd_1558867 355754687747758959730403 := by
  unfold tailWord_1558867
  simp only [CollatzResearch.WordTrace]
  refine ⟨56856550443498567132794855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37904366962332378088529903 56856550443498567132794855)
  ·
    refine ⟨85284825665247850699192283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56856550443498567132794855 85284825665247850699192283)
    ·
      refine ⟨127927238497871776048788425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85284825665247850699192283 127927238497871776048788425)
      ·
        refine ⟨95945428873403832036591319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127927238497871776048788425 95945428873403832036591319)
        ·
          refine ⟨143918143310105748054886979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95945428873403832036591319 143918143310105748054886979)
          ·
            refine ⟨215877214965158622082330469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143918143310105748054886979 215877214965158622082330469)
            ·
              refine ⟨40476977805967241640436963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 215877214965158622082330469 40476977805967241640436963)
              ·
                refine ⟨60715466708950862460655445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40476977805967241640436963 60715466708950862460655445)
                ·
                  refine ⟨355754687747758959730403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60715466708950862460655445 355754687747758959730403)
                  ·
                    rfl

theorem cell21_1558867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 9].length) (baseStart_1558867 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1558867 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1558867 prefixEnd_1558867 := by exact prefixLift 1558867
  have htrace : WordTrace (prefixWord ++ tailWord_1558867) baseStart_1558867 baseEnd_1558867 := by
    simpa [prefixWord, tailWord_1558867, baseEnd_1558867] using wordTrace_append hprefix tailTrace_1558867
  have hstable : (prefixWord ++ tailWord_1558867).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558867).length < 2 ^ (prefixWord ++ tailWord_1558867).sum := by decide
  have hdescent : baseEnd_1558867 < baseStart_1558867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558884 : List Nat := [2, 3, 1, 1, 3, 1, 2, 3, 5]
def baseStart_1558884 : Nat := 118140960795 + 1558884 * 2 ^ 59
def prefixEnd_1558884 : Nat := 4983230072969 + 3 ^ 40 * 1558884 * 2
def baseEnd_1558884 : Nat := 355758567379370707947035

theorem tailTrace_1558884 : CollatzResearch.WordTrace tailWord_1558884 prefixEnd_1558884 355758567379370707947035 := by
  unfold tailWord_1558884
  simp only [CollatzResearch.WordTrace]
  refine ⟨28428585242218489518081853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37904780322957986024109137 28428585242218489518081853)
  ·
    refine ⟨10660719465831933569280695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28428585242218489518081853 10660719465831933569280695)
    ·
      refine ⟨15991079198747900353921043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10660719465831933569280695 15991079198747900353921043)
      ·
        refine ⟨23986618798121850530881565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15991079198747900353921043 23986618798121850530881565)
        ·
          refine ⟨8994982049295693949080587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23986618798121850530881565 8994982049295693949080587)
          ·
            refine ⟨13492473073943540923620881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8994982049295693949080587 13492473073943540923620881)
            ·
              refine ⟨10119354805457655692715661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13492473073943540923620881 10119354805457655692715661)
              ·
                refine ⟨3794758052046620884768373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10119354805457655692715661 3794758052046620884768373)
                ·
                  refine ⟨355758567379370707947035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3794758052046620884768373 355758567379370707947035)
                  ·
                    rfl

theorem cell21_1558884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_1558884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1558884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1558884 prefixEnd_1558884 := by exact prefixLift 1558884
  have htrace : WordTrace (prefixWord ++ tailWord_1558884) baseStart_1558884 baseEnd_1558884 := by
    simpa [prefixWord, tailWord_1558884, baseEnd_1558884] using wordTrace_append hprefix tailTrace_1558884
  have hstable : (prefixWord ++ tailWord_1558884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558884).length < 2 ^ (prefixWord ++ tailWord_1558884).sum := by decide
  have hdescent : baseEnd_1558884 < baseStart_1558884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558901 : List Nat := [1, 3, 4, 1, 2, 2, 1, 2, 5]
def baseStart_1558901 : Nat := 118140960795 + 1558901 * 2 ^ 59
def prefixEnd_1558901 : Nat := 4983230072969 + 3 ^ 40 * 1558901 * 2
def baseEnd_1558901 : Nat := 355762447010982456163667

theorem tailTrace_1558901 : CollatzResearch.WordTrace tailWord_1558901 prefixEnd_1558901 355762447010982456163667 := by
  unfold tailWord_1558901
  simp only [CollatzResearch.WordTrace]
  refine ⟨56857790525375390939532557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37905193683583593959688371 56857790525375390939532557)
  ·
    refine ⟨21321671447015771602324709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56857790525375390939532557 21321671447015771602324709)
    ·
      refine ⟨3997813396315457175435883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21321671447015771602324709 3997813396315457175435883)
      ·
        refine ⟨5996720094473185763153825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3997813396315457175435883 5996720094473185763153825)
        ·
          refine ⟨4497540070854889322365369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5996720094473185763153825 4497540070854889322365369)
          ·
            refine ⟨3373155053141166991774027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4497540070854889322365369 3373155053141166991774027)
            ·
              refine ⟨5059732579711750487661041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3373155053141166991774027 5059732579711750487661041)
              ·
                refine ⟨3794799434783812865745781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5059732579711750487661041 3794799434783812865745781)
                ·
                  refine ⟨355762447010982456163667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3794799434783812865745781 355762447010982456163667)
                  ·
                    rfl

theorem cell21_1558901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 5].length) (baseStart_1558901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1558901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1558901 prefixEnd_1558901 := by exact prefixLift 1558901
  have htrace : WordTrace (prefixWord ++ tailWord_1558901) baseStart_1558901 baseEnd_1558901 := by
    simpa [prefixWord, tailWord_1558901, baseEnd_1558901] using wordTrace_append hprefix tailTrace_1558901
  have hstable : (prefixWord ++ tailWord_1558901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558901).length < 2 ^ (prefixWord ++ tailWord_1558901).sum := by decide
  have hdescent : baseEnd_1558901 < baseStart_1558901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558932 : List Nat := [2, 4, 2, 1, 3, 1, 1, 1, 6]
def baseStart_1558932 : Nat := 118140960795 + 1558932 * 2 ^ 59
def prefixEnd_1558932 : Nat := 4983230072969 + 3 ^ 40 * 1558932 * 2
def baseEnd_1558932 : Nat := 355769521633333291146937

theorem tailTrace_1558932 : CollatzResearch.WordTrace tailWord_1558932 prefixEnd_1558932 355769521633333291146937 := by
  unfold tailWord_1558932
  simp only [CollatzResearch.WordTrace]
  refine ⟨28429460594131541616955525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37905947458842055489274033 28429460594131541616955525)
  ·
    refine ⟨5330523861399664053179161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28429460594131541616955525 5330523861399664053179161)
    ·
      refine ⟨3997892896049748039884371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5330523861399664053179161 3997892896049748039884371)
      ·
        refine ⟨5996839344074622059826557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3997892896049748039884371 5996839344074622059826557)
        ·
          refine ⟨2248814754027983272434959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5996839344074622059826557 2248814754027983272434959)
          ·
            refine ⟨3373222131041974908652439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2248814754027983272434959 3373222131041974908652439)
            ·
              refine ⟨5059833196562962362978659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3373222131041974908652439 5059833196562962362978659)
              ·
                refine ⟨7589749794844443544467989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5059833196562962362978659 7589749794844443544467989)
                ·
                  refine ⟨355769521633333291146937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7589749794844443544467989 355769521633333291146937)
                  ·
                    rfl

theorem cell21_1558932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_1558932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1558932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1558932 prefixEnd_1558932 := by exact prefixLift 1558932
  have htrace : WordTrace (prefixWord ++ tailWord_1558932) baseStart_1558932 baseEnd_1558932 := by
    simpa [prefixWord, tailWord_1558932, baseEnd_1558932] using wordTrace_append hprefix tailTrace_1558932
  have hstable : (prefixWord ++ tailWord_1558932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558932).length < 2 ^ (prefixWord ++ tailWord_1558932).sum := by decide
  have hdescent : baseEnd_1558932 < baseStart_1558932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559019 : List Nat := [1, 1, 1, 1, 2, 3, 4, 1, 7]
def baseStart_1559019 : Nat := 118140960795 + 1559019 * 2 ^ 59
def prefixEnd_1559019 : Nat := 4983230072969 + 3 ^ 40 * 1559019 * 2
def baseEnd_1559019 : Nat := 355789376218640473196759

theorem tailTrace_1559019 : CollatzResearch.WordTrace tailWord_1559019 prefixEnd_1559019 355789376218640473196759 := by
  unfold tailWord_1559019
  simp only [CollatzResearch.WordTrace]
  refine ⟨56862094338947897092328111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37908062892631931394885407 56862094338947897092328111)
  ·
    refine ⟨85293141508421845638492167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56862094338947897092328111 85293141508421845638492167)
    ·
      refine ⟨127939712262632768457738251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85293141508421845638492167 127939712262632768457738251)
      ·
        refine ⟨191909568393949152686607377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127939712262632768457738251 191909568393949152686607377)
        ·
          refine ⟨143932176295461864514955533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191909568393949152686607377 143932176295461864514955533)
          ·
            refine ⟨53974566110798199193108325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143932176295461864514955533 53974566110798199193108325)
            ·
              refine ⟨10120231145774662348707811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53974566110798199193108325 10120231145774662348707811)
              ·
                refine ⟨15180346718661993523061717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10120231145774662348707811 15180346718661993523061717)
                ·
                  refine ⟨355789376218640473196759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15180346718661993523061717 355789376218640473196759)
                  ·
                    rfl

theorem cell21_1559019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 7].length) (baseStart_1559019 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1559019 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1559019 prefixEnd_1559019 := by exact prefixLift 1559019
  have htrace : WordTrace (prefixWord ++ tailWord_1559019) baseStart_1559019 baseEnd_1559019 := by
    simpa [prefixWord, tailWord_1559019, baseEnd_1559019] using wordTrace_append hprefix tailTrace_1559019
  have hstable : (prefixWord ++ tailWord_1559019).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559019).length < 2 ^ (prefixWord ++ tailWord_1559019).sum := by decide
  have hdescent : baseEnd_1559019 < baseStart_1559019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559095 : List Nat := [1, 1, 3, 1, 2, 3, 1, 2, 7]
def baseStart_1559095 : Nat := 118140960795 + 1559095 * 2 ^ 59
def prefixEnd_1559095 : Nat := 4983230072969 + 3 ^ 40 * 1559095 * 2
def baseEnd_1559095 : Nat := 355806720454081229929937

theorem tailTrace_1559095 : CollatzResearch.WordTrace tailWord_1559095 prefixEnd_1559095 355806720454081229929937 := by
  unfold tailWord_1559095
  simp only [CollatzResearch.WordTrace]
  refine ⟨56864866286672562072094739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37909910857781708048063159 56864866286672562072094739)
  ·
    refine ⟨85297299430008843108142109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56864866286672562072094739 85297299430008843108142109)
    ·
      refine ⟨31986487286253316165553291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85297299430008843108142109 31986487286253316165553291)
      ·
        refine ⟨47979730929379974248329937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31986487286253316165553291 47979730929379974248329937)
        ·
          refine ⟨35984798197034980686247453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47979730929379974248329937 35984798197034980686247453)
          ·
            refine ⟨13494299323888117757342795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35984798197034980686247453 13494299323888117757342795)
            ·
              refine ⟨20241448985832176636014193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13494299323888117757342795 20241448985832176636014193)
              ·
                refine ⟨15181086739374132477010645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20241448985832176636014193 15181086739374132477010645)
                ·
                  refine ⟨355806720454081229929937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15181086739374132477010645 355806720454081229929937)
                  ·
                    rfl

theorem cell21_1559095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 7].length) (baseStart_1559095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1559095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1559095 prefixEnd_1559095 := by exact prefixLift 1559095
  have htrace : WordTrace (prefixWord ++ tailWord_1559095) baseStart_1559095 baseEnd_1559095 := by
    simpa [prefixWord, tailWord_1559095, baseEnd_1559095] using wordTrace_append hprefix tailTrace_1559095
  have hstable : (prefixWord ++ tailWord_1559095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559095).length < 2 ^ (prefixWord ++ tailWord_1559095).sum := by decide
  have hdescent : baseEnd_1559095 < baseStart_1559095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
