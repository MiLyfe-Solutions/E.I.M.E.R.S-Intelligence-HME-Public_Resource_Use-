import V185TrunkScan22Chunk200

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1792502 : List Nat := [5, 1, 1, 1, 2, 1, 2, 4, 2, 3]
def baseStart_1792502 : Nat := 118140960795 + 1792502 * 2 ^ 59
def prefixEnd_1792502 : Nat := 4983230072969 + 3 ^ 40 * 1792502 * 2
def baseEnd_1792502 : Nat := 613610066763767374254293

theorem tailTrace_1792502 : CollatzResearch.WordTrace tailWord_1792502 prefixEnd_1792502 613610066763767374254293 := by
  unfold tailWord_1792502
  simp only [CollatzResearch.WordTrace]
  refine ⟨4086119934504928988378735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43585279301385909209373173 4086119934504928988378735)
  ·
    refine ⟨6129179901757393482568103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4086119934504928988378735 6129179901757393482568103)
    ·
      refine ⟨9193769852636090223852155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6129179901757393482568103 9193769852636090223852155)
      ·
        refine ⟨13790654778954135335778233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9193769852636090223852155 13790654778954135335778233)
        ·
          refine ⟨10342991084215601501833675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13790654778954135335778233 10342991084215601501833675)
          ·
            refine ⟨15514486626323402252750513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10342991084215601501833675 15514486626323402252750513)
            ·
              refine ⟨11635864969742551689562885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15514486626323402252750513 11635864969742551689562885)
              ·
                refine ⟨2181724681826728441793041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11635864969742551689562885 2181724681826728441793041)
                ·
                  refine ⟨1636293511370046331344781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2181724681826728441793041 1636293511370046331344781)
                  ·
                    refine ⟨613610066763767374254293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1636293511370046331344781 613610066763767374254293)
                    ·
                      rfl

theorem cell22_1792502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_1792502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1792502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1792502 prefixEnd_1792502 := by exact prefixLift 1792502
  have htrace : WordTrace (prefixWord ++ tailWord_1792502) baseStart_1792502 baseEnd_1792502 := by
    simpa [prefixWord, tailWord_1792502, baseEnd_1792502] using wordTrace_append hprefix tailTrace_1792502
  have hstable : (prefixWord ++ tailWord_1792502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792502).length < 2 ^ (prefixWord ++ tailWord_1792502).sum := by decide
  have hdescent : baseEnd_1792502 < baseStart_1792502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792590 : List Nat := [4, 1, 1, 1, 1, 2, 4, 1, 3, 4]
def baseStart_1792590 : Nat := 118140960795 + 1792590 * 2 ^ 59
def prefixEnd_1792590 : Nat := 4983230072969 + 3 ^ 40 * 1792590 * 2
def baseEnd_1792590 : Nat := 613640190962164478054023

theorem tailTrace_1792590 : CollatzResearch.WordTrace tailWord_1792590 prefixEnd_1792590 613640190962164478054023 := by
  unfold tailWord_1792590
  simp only [CollatzResearch.WordTrace]
  refine ⟨8172641071970006855407903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43587419050506703228842149 8172641071970006855407903)
  ·
    refine ⟨12258961607955010283111855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8172641071970006855407903 12258961607955010283111855)
    ·
      refine ⟨18388442411932515424667783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12258961607955010283111855 18388442411932515424667783)
      ·
        refine ⟨27582663617898773137001675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18388442411932515424667783 27582663617898773137001675)
        ·
          refine ⟨41373995426848159705502513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27582663617898773137001675 41373995426848159705502513)
          ·
            refine ⟨31030496570136119779126885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41373995426848159705502513 31030496570136119779126885)
            ·
              refine ⟨5818218106900522458586291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31030496570136119779126885 5818218106900522458586291)
              ·
                refine ⟨8727327160350783687879437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5818218106900522458586291 8727327160350783687879437)
                ·
                  refine ⟨3272747685131543882954789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8727327160350783687879437 3272747685131543882954789)
                  ·
                    refine ⟨613640190962164478054023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3272747685131543882954789 613640190962164478054023)
                    ·
                      rfl

theorem cell22_1792590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_1792590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1792590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1792590 prefixEnd_1792590 := by exact prefixLift 1792590
  have htrace : WordTrace (prefixWord ++ tailWord_1792590) baseStart_1792590 baseEnd_1792590 := by
    simpa [prefixWord, tailWord_1792590, baseEnd_1792590] using wordTrace_append hprefix tailTrace_1792590
  have hstable : (prefixWord ++ tailWord_1792590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792590).length < 2 ^ (prefixWord ++ tailWord_1792590).sum := by decide
  have hdescent : baseEnd_1792590 < baseStart_1792590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792622 : List Nat := [4, 1, 2, 2, 2, 2, 2, 1, 6]
def baseStart_1792622 : Nat := 118140960795 + 1792622 * 2 ^ 59
def prefixEnd_1792622 : Nat := 4983230072969 + 3 ^ 40 * 1792622 * 2
def baseEnd_1792622 : Nat := 204550381738709020417975

theorem tailTrace_1792622 : CollatzResearch.WordTrace tailWord_1792622 prefixEnd_1792622 204550381738709020417975 := by
  unfold tailWord_1792622
  simp only [CollatzResearch.WordTrace]
  refine ⟨8172786963955515538553515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43588197141096082872285413 8172786963955515538553515)
  ·
    refine ⟨12259180445933273307830273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8172786963955515538553515 12259180445933273307830273)
    ·
      refine ⟨9194385334449954980872705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12259180445933273307830273 9194385334449954980872705)
      ·
        refine ⟨6895789000837466235654529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9194385334449954980872705 6895789000837466235654529)
        ·
          refine ⟨5171841750628099676740897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6895789000837466235654529 5171841750628099676740897)
          ·
            refine ⟨3878881312971074757555673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5171841750628099676740897 3878881312971074757555673)
            ·
              refine ⟨2909160984728306068166755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3878881312971074757555673 2909160984728306068166755)
              ·
                refine ⟨4363741477092459102250133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2909160984728306068166755 4363741477092459102250133)
                ·
                  refine ⟨204550381738709020417975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4363741477092459102250133 204550381738709020417975)
                  ·
                    rfl

theorem cell22_1792622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_1792622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1792622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1792622 prefixEnd_1792622 := by exact prefixLift 1792622
  have htrace : WordTrace (prefixWord ++ tailWord_1792622) baseStart_1792622 baseEnd_1792622 := by
    simpa [prefixWord, tailWord_1792622, baseEnd_1792622] using wordTrace_append hprefix tailTrace_1792622
  have hstable : (prefixWord ++ tailWord_1792622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792622).length < 2 ^ (prefixWord ++ tailWord_1792622).sum := by decide
  have hdescent : baseEnd_1792622 < baseStart_1792622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792772 : List Nat := [2, 3, 2, 2, 1, 1, 1, 4, 1, 5]
def baseStart_1792772 : Nat := 118140960795 + 1792772 * 2 ^ 59
def prefixEnd_1792772 : Nat := 4983230072969 + 3 ^ 40 * 1792772 * 2
def baseEnd_1792772 : Nat := 613702493281576670003465

theorem tailTrace_1792772 : CollatzResearch.WordTrace tailWord_1792772 prefixEnd_1792772 613702493281576670003465 := by
  unfold tailWord_1792772
  simp only [CollatzResearch.WordTrace]
  refine ⟨32693883330550349963194285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43591844440733799950925713 32693883330550349963194285)
  ·
    refine ⟨12260206248956381236197857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32693883330550349963194285 12260206248956381236197857)
    ·
      refine ⟨9195154686717285927148393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12260206248956381236197857 9195154686717285927148393)
      ·
        refine ⟨6896366015037964445361295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9195154686717285927148393 6896366015037964445361295)
        ·
          refine ⟨10344549022556946668041943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6896366015037964445361295 10344549022556946668041943)
          ·
            refine ⟨15516823533835420002062915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10344549022556946668041943 15516823533835420002062915)
            ·
              refine ⟨23275235300753130003094373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15516823533835420002062915 23275235300753130003094373)
              ·
                refine ⟨4364106618891211875580195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23275235300753130003094373 4364106618891211875580195)
                ·
                  refine ⟨6546159928336817813370293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4364106618891211875580195 6546159928336817813370293)
                  ·
                    refine ⟨613702493281576670003465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6546159928336817813370293 613702493281576670003465)
                    ·
                      rfl

theorem cell22_1792772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_1792772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1792772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1792772 prefixEnd_1792772 := by exact prefixLift 1792772
  have htrace : WordTrace (prefixWord ++ tailWord_1792772) baseStart_1792772 baseEnd_1792772 := by
    simpa [prefixWord, tailWord_1792772, baseEnd_1792772] using wordTrace_append hprefix tailTrace_1792772
  have hstable : (prefixWord ++ tailWord_1792772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792772).length < 2 ^ (prefixWord ++ tailWord_1792772).sum := by decide
  have hdescent : baseEnd_1792772 < baseStart_1792772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792776 : List Nat := [2, 1, 3, 2, 2, 4, 2, 1, 1, 4]
def baseStart_1792776 : Nat := 118140960795 + 1792776 * 2 ^ 59
def prefixEnd_1792776 : Nat := 4983230072969 + 3 ^ 40 * 1792776 * 2
def baseEnd_1792776 : Nat := 613703862563321992903453

theorem tailTrace_1792776 : CollatzResearch.WordTrace tailWord_1792776 prefixEnd_1792776 613703862563321992903453 := by
  unfold tailWord_1792776
  simp only [CollatzResearch.WordTrace]
  refine ⟨32693956276543104304767091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43591941702057472406356121 32693956276543104304767091)
  ·
    refine ⟨49040934414814656457150637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32693956276543104304767091 49040934414814656457150637)
    ·
      refine ⟨18390350405555496171431489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49040934414814656457150637 18390350405555496171431489)
      ·
        refine ⟨13792762804166622128573617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18390350405555496171431489 13792762804166622128573617)
        ·
          refine ⟨10344572103124966596430213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13792762804166622128573617 10344572103124966596430213)
          ·
            refine ⟨1939607269335931236830665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10344572103124966596430213 1939607269335931236830665)
            ·
              refine ⟨1454705452001948427622999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1939607269335931236830665 1454705452001948427622999)
              ·
                refine ⟨2182058178002922641434499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1454705452001948427622999 2182058178002922641434499)
                ·
                  refine ⟨3273087267004383962151749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2182058178002922641434499 3273087267004383962151749)
                  ·
                    refine ⟨613703862563321992903453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3273087267004383962151749 613703862563321992903453)
                    ·
                      rfl

theorem cell22_1792776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 1, 1, 4].length) (baseStart_1792776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1792776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1792776 prefixEnd_1792776 := by exact prefixLift 1792776
  have htrace : WordTrace (prefixWord ++ tailWord_1792776) baseStart_1792776 baseEnd_1792776 := by
    simpa [prefixWord, tailWord_1792776, baseEnd_1792776] using wordTrace_append hprefix tailTrace_1792776
  have hstable : (prefixWord ++ tailWord_1792776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792776).length < 2 ^ (prefixWord ++ tailWord_1792776).sum := by decide
  have hdescent : baseEnd_1792776 < baseStart_1792776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792819 : List Nat := [1, 1, 1, 2, 6, 3, 2, 6]
def baseStart_1792819 : Nat := 118140960795 + 1792819 * 2 ^ 59
def prefixEnd_1792819 : Nat := 4983230072969 + 3 ^ 40 * 1792819 * 2
def baseEnd_1792819 : Nat := 68190953593564912675369

theorem tailTrace_1792819 : CollatzResearch.WordTrace tailWord_1792819 prefixEnd_1792819 68190953593564912675369 := by
  unfold tailWord_1792819
  simp only [CollatzResearch.WordTrace]
  refine ⟨65389480891930426953349511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43592987261286951302233007 65389480891930426953349511)
  ·
    refine ⟨98084221337895640430024267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65389480891930426953349511 98084221337895640430024267)
    ·
      refine ⟨147126332006843460645036401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98084221337895640430024267 147126332006843460645036401)
      ·
        refine ⟨110344749005132595483777301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147126332006843460645036401 110344749005132595483777301)
        ·
          refine ⟨5172410109615590413302061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 110344749005132595483777301 5172410109615590413302061)
          ·
            refine ⟨1939653791105846404988273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5172410109615590413302061 1939653791105846404988273)
            ·
              refine ⟨1454740343329384803741205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1939653791105846404988273 1454740343329384803741205)
              ·
                refine ⟨68190953593564912675369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1454740343329384803741205 68190953593564912675369)
                ·
                  rfl

theorem cell22_1792819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 6].length) (baseStart_1792819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1792819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1792819 prefixEnd_1792819 := by exact prefixLift 1792819
  have htrace : WordTrace (prefixWord ++ tailWord_1792819) baseStart_1792819 baseEnd_1792819 := by
    simpa [prefixWord, tailWord_1792819, baseEnd_1792819] using wordTrace_append hprefix tailTrace_1792819
  have hstable : (prefixWord ++ tailWord_1792819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792819).length < 2 ^ (prefixWord ++ tailWord_1792819).sum := by decide
  have hdescent : baseEnd_1792819 < baseStart_1792819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792836 : List Nat := [2, 3, 4, 2, 1, 2, 8]
def baseStart_1792836 : Nat := 118140960795 + 1792836 * 2 ^ 59
def prefixEnd_1792836 : Nat := 4983230072969 + 3 ^ 40 * 1792836 * 2
def baseEnd_1792836 : Nat := 22730533399611179126047

theorem tailTrace_1792836 : CollatzResearch.WordTrace tailWord_1792836 prefixEnd_1792836 22730533399611179126047 := by
  unfold tailWord_1792836
  simp only [CollatzResearch.WordTrace]
  refine ⟨32695050466434419428359181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43593400621912559237812241 32695050466434419428359181)
  ·
    refine ⟨12260643924912907285634693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32695050466434419428359181 12260643924912907285634693)
    ·
      refine ⟨2298870735921170116056505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12260643924912907285634693 2298870735921170116056505)
      ·
        refine ⟨1724153051940877587042379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2298870735921170116056505 1724153051940877587042379)
        ·
          refine ⟨2586229577911316380563569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1724153051940877587042379 2586229577911316380563569)
          ·
            refine ⟨1939672183433487285422677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2586229577911316380563569 1939672183433487285422677)
            ·
              refine ⟨22730533399611179126047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1939672183433487285422677 22730533399611179126047)
              ·
                rfl

theorem cell22_1792836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 8].length) (baseStart_1792836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1792836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1792836 prefixEnd_1792836 := by exact prefixLift 1792836
  have htrace : WordTrace (prefixWord ++ tailWord_1792836) baseStart_1792836 baseEnd_1792836 := by
    simpa [prefixWord, tailWord_1792836, baseEnd_1792836] using wordTrace_append hprefix tailTrace_1792836
  have hstable : (prefixWord ++ tailWord_1792836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792836).length < 2 ^ (prefixWord ++ tailWord_1792836).sum := by decide
  have hdescent : baseEnd_1792836 < baseStart_1792836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792838 : List Nat := [6, 1, 1, 2, 2, 1, 1, 2, 2, 4]
def baseStart_1792838 : Nat := 118140960795 + 1792838 * 2 ^ 59
def prefixEnd_1792838 : Nat := 4983230072969 + 3 ^ 40 * 1792838 * 2
def baseEnd_1792838 : Nat := 613725086430374497853263

theorem tailTrace_1792838 : CollatzResearch.WordTrace tailWord_1792838 prefixEnd_1792838 613725086430374497853263 := by
  unfold tailWord_1792838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2043442933714424787446599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43593449252574395465527445 2043442933714424787446599)
  ·
    refine ⟨3065164400571637181169899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2043442933714424787446599 3065164400571637181169899)
    ·
      refine ⟨4597746600857455771754849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3065164400571637181169899 4597746600857455771754849)
      ·
        refine ⟨3448309950643091828816137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4597746600857455771754849 3448309950643091828816137)
        ·
          refine ⟨2586232462982318871612103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3448309950643091828816137 2586232462982318871612103)
          ·
            refine ⟨3879348694473478307418155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2586232462982318871612103 3879348694473478307418155)
            ·
              refine ⟨5819023041710217461127233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3879348694473478307418155 5819023041710217461127233)
              ·
                refine ⟨4364267281282663095845425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5819023041710217461127233 4364267281282663095845425)
                ·
                  refine ⟨3273200460961997321884069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4364267281282663095845425 3273200460961997321884069)
                  ·
                    refine ⟨613725086430374497853263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3273200460961997321884069 613725086430374497853263)
                    ·
                      rfl

theorem cell22_1792838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_1792838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1792838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1792838 prefixEnd_1792838 := by exact prefixLift 1792838
  have htrace : WordTrace (prefixWord ++ tailWord_1792838) baseStart_1792838 baseEnd_1792838 := by
    simpa [prefixWord, tailWord_1792838, baseEnd_1792838] using wordTrace_append hprefix tailTrace_1792838
  have hstable : (prefixWord ++ tailWord_1792838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792838).length < 2 ^ (prefixWord ++ tailWord_1792838).sum := by decide
  have hdescent : baseEnd_1792838 < baseStart_1792838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792945 : List Nat := [1, 2, 2, 4, 4, 1, 2, 1, 1, 4]
def baseStart_1792945 : Nat := 118140960795 + 1792945 * 2 ^ 59
def prefixEnd_1792945 : Nat := 4983230072969 + 3 ^ 40 * 1792945 * 2
def baseEnd_1792945 : Nat := 613761714717061885427935

theorem tailTrace_1792945 : CollatzResearch.WordTrace tailWord_1792945 prefixEnd_1792945 613761714717061885427935 := by
  unfold tailWord_1792945
  simp only [CollatzResearch.WordTrace]
  refine ⟨65394076489473950472436289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43596050992982633648290859 65394076489473950472436289)
  ·
    refine ⟨49045557367105462854327217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65394076489473950472436289 49045557367105462854327217)
    ·
      refine ⟨36784168025329097140745413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49045557367105462854327217 36784168025329097140745413)
      ·
        refine ⟨6897031504749205713889765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36784168025329097140745413 6897031504749205713889765)
        ·
          refine ⟨1293193407140476071354331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6897031504749205713889765 1293193407140476071354331)
          ·
            refine ⟨1939790110710714107031497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1293193407140476071354331 1939790110710714107031497)
            ·
              refine ⟨1454842583033035580273623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1939790110710714107031497 1454842583033035580273623)
              ·
                refine ⟨2182263874549553370410435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1454842583033035580273623 2182263874549553370410435)
                ·
                  refine ⟨3273395811824330055615653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2182263874549553370410435 3273395811824330055615653)
                  ·
                    refine ⟨613761714717061885427935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3273395811824330055615653 613761714717061885427935)
                    ·
                      rfl

theorem cell22_1792945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 1, 1, 4].length) (baseStart_1792945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1792945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1792945 prefixEnd_1792945 := by exact prefixLift 1792945
  have htrace : WordTrace (prefixWord ++ tailWord_1792945) baseStart_1792945 baseEnd_1792945 := by
    simpa [prefixWord, tailWord_1792945, baseEnd_1792945] using wordTrace_append hprefix tailTrace_1792945
  have hstable : (prefixWord ++ tailWord_1792945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792945).length < 2 ^ (prefixWord ++ tailWord_1792945).sum := by decide
  have hdescent : baseEnd_1792945 < baseStart_1792945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792967 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 1, 8]
def baseStart_1792967 : Nat := 118140960795 + 1792967 * 2 ^ 59
def prefixEnd_1792967 : Nat := 4983230072969 + 3 ^ 40 * 1792967 * 2
def baseEnd_1792967 : Nat := 613769245766661161377867

theorem tailTrace_1792967 : CollatzResearch.WordTrace tailWord_1792967 prefixEnd_1792967 613769245766661161377867 := by
  unfold tailWord_1792967
  simp only [CollatzResearch.WordTrace]
  refine ⟨65394878895394248229737155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43596585930262832153158103 65394878895394248229737155)
  ·
    refine ⟨98092318343091372344605733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65394878895394248229737155 98092318343091372344605733)
    ·
      refine ⟨18392309689329632314613575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98092318343091372344605733 18392309689329632314613575)
      ·
        refine ⟨27588464533994448471920363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18392309689329632314613575 27588464533994448471920363)
        ·
          refine ⟨41382696800991672707880545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27588464533994448471920363 41382696800991672707880545)
          ·
            refine ⟨31037022600743754530910409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41382696800991672707880545 31037022600743754530910409)
            ·
              refine ⟨23277766950557815898182807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31037022600743754530910409 23277766950557815898182807)
              ·
                refine ⟨34916650425836723847274211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23277766950557815898182807 34916650425836723847274211)
                ·
                  refine ⟨52374975638755085770911317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34916650425836723847274211 52374975638755085770911317)
                  ·
                    refine ⟨613769245766661161377867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 52374975638755085770911317 613769245766661161377867)
                    ·
                      rfl

theorem cell22_1792967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_1792967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1792967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1792967 prefixEnd_1792967 := by exact prefixLift 1792967
  have htrace : WordTrace (prefixWord ++ tailWord_1792967) baseStart_1792967 baseEnd_1792967 := by
    simpa [prefixWord, tailWord_1792967, baseEnd_1792967] using wordTrace_append hprefix tailTrace_1792967
  have hstable : (prefixWord ++ tailWord_1792967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792967).length < 2 ^ (prefixWord ++ tailWord_1792967).sum := by decide
  have hdescent : baseEnd_1792967 < baseStart_1792967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792986 : List Nat := [3, 1, 1, 2, 4, 1, 2, 2, 3, 3]
def baseStart_1792986 : Nat := 118140960795 + 1792986 * 2 ^ 59
def prefixEnd_1792986 : Nat := 4983230072969 + 3 ^ 40 * 1792986 * 2
def baseEnd_1792986 : Nat := 613775749854951445152809

theorem tailTrace_1792986 : CollatzResearch.WordTrace tailWord_1792986 prefixEnd_1792986 613775749854951445152809 := by
  unfold tailWord_1792986
  simp only [CollatzResearch.WordTrace]
  refine ⟨16348892970581353618669703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43597047921550276316452541 16348892970581353618669703)
  ·
    refine ⟨24523339455872030428004555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16348892970581353618669703 24523339455872030428004555)
    ·
      refine ⟨36785009183808045642006833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24523339455872030428004555 36785009183808045642006833)
      ·
        refine ⟨27588756887856034231505125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36785009183808045642006833 27588756887856034231505125)
        ·
          refine ⟨5172891916473006418407211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27588756887856034231505125 5172891916473006418407211)
          ·
            refine ⟨7759337874709509627610817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5172891916473006418407211 7759337874709509627610817)
            ·
              refine ⟨5819503406032132220708113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7759337874709509627610817 5819503406032132220708113)
              ·
                refine ⟨4364627554524099165531085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5819503406032132220708113 4364627554524099165531085)
                ·
                  refine ⟨1636735332946537187074157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4364627554524099165531085 1636735332946537187074157)
                  ·
                    refine ⟨613775749854951445152809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1636735332946537187074157 613775749854951445152809)
                    ·
                      rfl

theorem cell22_1792986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 3, 3].length) (baseStart_1792986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1792986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1792986 prefixEnd_1792986 := by exact prefixLift 1792986
  have htrace : WordTrace (prefixWord ++ tailWord_1792986) baseStart_1792986 baseEnd_1792986 := by
    simpa [prefixWord, tailWord_1792986, baseEnd_1792986] using wordTrace_append hprefix tailTrace_1792986
  have hstable : (prefixWord ++ tailWord_1792986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792986).length < 2 ^ (prefixWord ++ tailWord_1792986).sum := by decide
  have hdescent : baseEnd_1792986 < baseStart_1792986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792999 : List Nat := [1, 1, 5, 2, 2, 1, 1, 2, 7]
def baseStart_1792999 : Nat := 118140960795 + 1792999 * 2 ^ 59
def prefixEnd_1792999 : Nat := 4983230072969 + 3 ^ 40 * 1792999 * 2
def baseEnd_1792999 : Nat := 204593400006874581525923

theorem tailTrace_1792999 : CollatzResearch.WordTrace tailWord_1792999 prefixEnd_1792999 204593400006874581525923 := by
  unfold tailWord_1792999
  simp only [CollatzResearch.WordTrace]
  refine ⟨65396046031278317694902051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43597364020852211796601367 65396046031278317694902051)
  ·
    refine ⟨98094069046917476542353077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65396046031278317694902051 98094069046917476542353077)
    ·
      refine ⟨9196318973148513425845601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98094069046917476542353077 9196318973148513425845601)
      ·
        refine ⟨6897239229861385069384201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9196318973148513425845601 6897239229861385069384201)
        ·
          refine ⟨5172929422396038802038151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6897239229861385069384201 5172929422396038802038151)
          ·
            refine ⟨7759394133594058203057227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5172929422396038802038151 7759394133594058203057227)
            ·
              refine ⟨11639091200391087304585841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7759394133594058203057227 11639091200391087304585841)
              ·
                refine ⟨8729318400293315478439381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11639091200391087304585841 8729318400293315478439381)
                ·
                  refine ⟨204593400006874581525923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8729318400293315478439381 204593400006874581525923)
                  ·
                    rfl

theorem cell22_1792999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 7].length) (baseStart_1792999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1792999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1792999 prefixEnd_1792999 := by exact prefixLift 1792999
  have htrace : WordTrace (prefixWord ++ tailWord_1792999) baseStart_1792999 baseEnd_1792999 := by
    simpa [prefixWord, tailWord_1792999, baseEnd_1792999] using wordTrace_append hprefix tailTrace_1792999
  have hstable : (prefixWord ++ tailWord_1792999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792999).length < 2 ^ (prefixWord ++ tailWord_1792999).sum := by decide
  have hdescent : baseEnd_1792999 < baseStart_1792999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793020 : List Nat := [2, 2, 2, 1, 2, 4, 3, 2, 1, 3]
def baseStart_1793020 : Nat := 118140960795 + 1793020 * 2 ^ 59
def prefixEnd_1793020 : Nat := 4983230072969 + 3 ^ 40 * 1793020 * 2
def baseEnd_1793020 : Nat := 613787388749786689802705

theorem tailTrace_1793020 : CollatzResearch.WordTrace tailWord_1793020 prefixEnd_1793020 613787388749786689802705 := by
  unfold tailWord_1793020
  simp only [CollatzResearch.WordTrace]
  refine ⟨32698405982101119140708257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43597874642801492187611009 32698405982101119140708257)
  ·
    refine ⟨24523804486575839355531193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32698405982101119140708257 24523804486575839355531193)
    ·
      refine ⟨18392853364931879516648395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24523804486575839355531193 18392853364931879516648395)
      ·
        refine ⟨27589280047397819274972593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18392853364931879516648395 27589280047397819274972593)
        ·
          refine ⟨20691960035548364456229445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27589280047397819274972593 20691960035548364456229445)
          ·
            refine ⟨3879742506665318335543021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20691960035548364456229445 3879742506665318335543021)
            ·
              refine ⟨1454903439999494375828633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3879742506665318335543021 1454903439999494375828633)
              ·
                refine ⟨1091177579999620781871475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1454903439999494375828633 1091177579999620781871475)
                ·
                  refine ⟨1636766369999431172807213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1091177579999620781871475 1636766369999431172807213)
                  ·
                    refine ⟨613787388749786689802705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1636766369999431172807213 613787388749786689802705)
                    ·
                      rfl

theorem cell22_1793020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 2, 1, 3].length) (baseStart_1793020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1793020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1793020 prefixEnd_1793020 := by exact prefixLift 1793020
  have htrace : WordTrace (prefixWord ++ tailWord_1793020) baseStart_1793020 baseEnd_1793020 := by
    simpa [prefixWord, tailWord_1793020, baseEnd_1793020] using wordTrace_append hprefix tailTrace_1793020
  have hstable : (prefixWord ++ tailWord_1793020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793020).length < 2 ^ (prefixWord ++ tailWord_1793020).sum := by decide
  have hdescent : baseEnd_1793020 < baseStart_1793020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793029 : List Nat := [1, 3, 1, 1, 2, 3, 2, 2, 3, 4]
def baseStart_1793029 : Nat := 118140960795 + 1793029 * 2 ^ 59
def prefixEnd_1793029 : Nat := 4983230072969 + 3 ^ 40 * 1793029 * 2
def baseEnd_1793029 : Nat := 613790469633713666327677

theorem tailTrace_1793029 : CollatzResearch.WordTrace tailWord_1793029 prefixEnd_1793029 613790469633713666327677 := by
  unfold tailWord_1793029
  simp only [CollatzResearch.WordTrace]
  refine ⟨65397140221169632818494141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43598093480779755212329427 65397140221169632818494141)
  ·
    refine ⟨24523927582938612306935303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65397140221169632818494141 24523927582938612306935303)
    ·
      refine ⟨36785891374407918460402955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24523927582938612306935303 36785891374407918460402955)
      ·
        refine ⟨55178837061611877690604433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36785891374407918460402955 55178837061611877690604433)
        ·
          refine ⟨41384127796208908267953325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55178837061611877690604433 41384127796208908267953325)
          ·
            refine ⟨15519047923578340600482497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41384127796208908267953325 15519047923578340600482497)
            ·
              refine ⟨11639285942683755450361873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15519047923578340600482497 11639285942683755450361873)
              ·
                refine ⟨8729464457012816587771405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11639285942683755450361873 8729464457012816587771405)
                ·
                  refine ⟨3273549171379806220414277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8729464457012816587771405 3273549171379806220414277)
                  ·
                    refine ⟨613790469633713666327677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3273549171379806220414277 613790469633713666327677)
                    ·
                      rfl

theorem cell22_1793029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3, 4].length) (baseStart_1793029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1793029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1793029 prefixEnd_1793029 := by exact prefixLift 1793029
  have htrace : WordTrace (prefixWord ++ tailWord_1793029) baseStart_1793029 baseEnd_1793029 := by
    simpa [prefixWord, tailWord_1793029, baseEnd_1793029] using wordTrace_append hprefix tailTrace_1793029
  have hstable : (prefixWord ++ tailWord_1793029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793029).length < 2 ^ (prefixWord ++ tailWord_1793029).sum := by decide
  have hdescent : baseEnd_1793029 < baseStart_1793029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793059 : List Nat := [1, 1, 1, 4, 3, 2, 1, 1, 3, 5]
def baseStart_1793059 : Nat := 118140960795 + 1793059 * 2 ^ 59
def prefixEnd_1793059 : Nat := 4983230072969 + 3 ^ 40 * 1793059 * 2
def baseEnd_1793059 : Nat := 613800739246803588077585

theorem tailTrace_1793059 : CollatzResearch.WordTrace tailWord_1793059 prefixEnd_1793059 613800739246803588077585 := by
  unfold tailWord_1793059
  simp only [CollatzResearch.WordTrace]
  refine ⟨65398234411060947942086231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43598822940707298628057487 65398234411060947942086231)
  ·
    refine ⟨98097351616591421913129347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65398234411060947942086231 98097351616591421913129347)
    ·
      refine ⟨147146027424887132869694021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98097351616591421913129347 147146027424887132869694021)
      ·
        refine ⟨27589880142166337413067629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147146027424887132869694021 27589880142166337413067629)
        ·
          refine ⟨10346205053312376529900361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27589880142166337413067629 10346205053312376529900361)
          ·
            refine ⟨7759653789984282397425271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10346205053312376529900361 7759653789984282397425271)
            ·
              refine ⟨11639480684976423596137907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7759653789984282397425271 11639480684976423596137907)
              ·
                refine ⟨17459221027464635394206861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11639480684976423596137907 17459221027464635394206861)
                ·
                  refine ⟨6547207885299238272827573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17459221027464635394206861 6547207885299238272827573)
                  ·
                    refine ⟨613800739246803588077585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6547207885299238272827573 613800739246803588077585)
                    ·
                      rfl

theorem cell22_1793059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 5].length) (baseStart_1793059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1793059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1793059 prefixEnd_1793059 := by exact prefixLift 1793059
  have htrace : WordTrace (prefixWord ++ tailWord_1793059) baseStart_1793059 baseEnd_1793059 := by
    simpa [prefixWord, tailWord_1793059, baseEnd_1793059] using wordTrace_append hprefix tailTrace_1793059
  have hstable : (prefixWord ++ tailWord_1793059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793059).length < 2 ^ (prefixWord ++ tailWord_1793059).sum := by decide
  have hdescent : baseEnd_1793059 < baseStart_1793059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793061 : List Nat := [1, 3, 1, 2, 2, 2, 2, 5, 4]
def baseStart_1793061 : Nat := 118140960795 + 1793061 * 2 ^ 59
def prefixEnd_1793061 : Nat := 4983230072969 + 3 ^ 40 * 1793061 * 2
def baseEnd_1793061 : Nat := 204600474629225416509193

theorem tailTrace_1793061 : CollatzResearch.WordTrace tailWord_1793061 prefixEnd_1793061 204600474629225416509193 := by
  unfold tailWord_1793061
  simp only [CollatzResearch.WordTrace]
  refine ⟨65398307357053702283659037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43598871571369134855772691 65398307357053702283659037)
  ·
    refine ⟨24524365258895138356372139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65398307357053702283659037 24524365258895138356372139)
    ·
      refine ⟨36786547888342707534558209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24524365258895138356372139 36786547888342707534558209)
      ·
        refine ⟨27589910916257030650918657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36786547888342707534558209 27589910916257030650918657)
        ·
          refine ⟨20692433187192772988188993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27589910916257030650918657 20692433187192772988188993)
          ·
            refine ⟨15519324890394579741141745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20692433187192772988188993 15519324890394579741141745)
            ·
              refine ⟨11639493667795934805856309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15519324890394579741141745 11639493667795934805856309)
              ·
                refine ⟨1091202531355868888049029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11639493667795934805856309 1091202531355868888049029)
                ·
                  refine ⟨204600474629225416509193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1091202531355868888049029 204600474629225416509193)
                  ·
                    rfl

theorem cell22_1793061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 5, 4].length) (baseStart_1793061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1793061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1793061 prefixEnd_1793061 := by exact prefixLift 1793061
  have htrace : WordTrace (prefixWord ++ tailWord_1793061) baseStart_1793061 baseEnd_1793061 := by
    simpa [prefixWord, tailWord_1793061, baseEnd_1793061] using wordTrace_append hprefix tailTrace_1793061
  have hstable : (prefixWord ++ tailWord_1793061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793061).length < 2 ^ (prefixWord ++ tailWord_1793061).sum := by decide
  have hdescent : baseEnd_1793061 < baseStart_1793061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793138 : List Nat := [3, 2, 1, 2, 2, 1, 4, 1, 3, 3]
def baseStart_1793138 : Nat := 118140960795 + 1793138 * 2 ^ 59
def prefixEnd_1793138 : Nat := 4983230072969 + 3 ^ 40 * 1793138 * 2
def baseEnd_1793138 : Nat := 613827782561273715352343

theorem tailTrace_1793138 : CollatzResearch.WordTrace tailWord_1793138 prefixEnd_1793138 613827782561273715352343 := by
  unfold tailWord_1793138
  simp only [CollatzResearch.WordTrace]
  refine ⟨16350278944443686108553017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43600743851849829622808045 16350278944443686108553017)
  ·
    refine ⟨12262709208332764581414763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16350278944443686108553017 12262709208332764581414763)
    ·
      refine ⟨18394063812499146872122145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12262709208332764581414763 18394063812499146872122145)
      ·
        refine ⟨13795547859374360154091609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18394063812499146872122145 13795547859374360154091609)
        ·
          refine ⟨10346660894530770115568707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13795547859374360154091609 10346660894530770115568707)
          ·
            refine ⟨15519991341796155173353061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10346660894530770115568707 15519991341796155173353061)
            ·
              refine ⟨2909998376586779095003699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15519991341796155173353061 2909998376586779095003699)
              ·
                refine ⟨4364997564880168642505549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2909998376586779095003699 4364997564880168642505549)
                ·
                  refine ⟨1636874086830063240939581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4364997564880168642505549 1636874086830063240939581)
                  ·
                    refine ⟨613827782561273715352343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1636874086830063240939581 613827782561273715352343)
                    ·
                      rfl

theorem cell22_1793138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 3, 3].length) (baseStart_1793138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1793138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1793138 prefixEnd_1793138 := by exact prefixLift 1793138
  have htrace : WordTrace (prefixWord ++ tailWord_1793138) baseStart_1793138 baseEnd_1793138 := by
    simpa [prefixWord, tailWord_1793138, baseEnd_1793138] using wordTrace_append hprefix tailTrace_1793138
  have hstable : (prefixWord ++ tailWord_1793138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793138).length < 2 ^ (prefixWord ++ tailWord_1793138).sum := by decide
  have hdescent : baseEnd_1793138 < baseStart_1793138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793164 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 2, 8]
def baseStart_1793164 : Nat := 118140960795 + 1793164 * 2 ^ 59
def prefixEnd_1793164 : Nat := 4983230072969 + 3 ^ 40 * 1793164 * 2
def baseEnd_1793164 : Nat := 613836682892618314202263

theorem tailTrace_1793164 : CollatzResearch.WordTrace tailWord_1793164 prefixEnd_1793164 613836682892618314202263 := by
  unfold tailWord_1793164
  simp only [CollatzResearch.WordTrace]
  refine ⟨32701032037840275437329273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43601376050453700583105697 32701032037840275437329273)
  ·
    refine ⟨24525774028380206577996955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32701032037840275437329273 24525774028380206577996955)
    ·
      refine ⟨36788661042570309866995433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24525774028380206577996955 36788661042570309866995433)
      ·
        refine ⟨27591495781927732400246575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36788661042570309866995433 27591495781927732400246575)
        ·
          refine ⟨41387243672891598600369863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27591495781927732400246575 41387243672891598600369863)
          ·
            refine ⟨62080865509337397900554795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41387243672891598600369863 62080865509337397900554795)
            ·
              refine ⟨93121298264006096850832193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62080865509337397900554795 93121298264006096850832193)
              ·
                refine ⟨69840973698004572638124145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93121298264006096850832193 69840973698004572638124145)
                ·
                  refine ⟨52380730273503429478593109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69840973698004572638124145 52380730273503429478593109)
                  ·
                    refine ⟨613836682892618314202263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 52380730273503429478593109 613836682892618314202263)
                    ·
                      rfl

theorem cell22_1793164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_1793164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1793164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1793164 prefixEnd_1793164 := by exact prefixLift 1793164
  have htrace : WordTrace (prefixWord ++ tailWord_1793164) baseStart_1793164 baseEnd_1793164 := by
    simpa [prefixWord, tailWord_1793164, baseEnd_1793164] using wordTrace_append hprefix tailTrace_1793164
  have hstable : (prefixWord ++ tailWord_1793164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793164).length < 2 ^ (prefixWord ++ tailWord_1793164).sum := by decide
  have hdescent : baseEnd_1793164 < baseStart_1793164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793211 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 6, 3]
def baseStart_1793211 : Nat := 118140960795 + 1793211 * 2 ^ 59
def prefixEnd_1793211 : Nat := 4983230072969 + 3 ^ 40 * 1793211 * 2
def baseEnd_1793211 : Nat := 613852771953125858277119

theorem tailTrace_1793211 : CollatzResearch.WordTrace tailWord_1793211 prefixEnd_1793211 613852771953125858277119 := by
  unfold tailWord_1793211
  simp only [CollatzResearch.WordTrace]
  refine ⟨65403778306510277901619487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43602518871006851934412991 65403778306510277901619487)
  ·
    refine ⟨98105667459765416852429231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65403778306510277901619487 98105667459765416852429231)
    ·
      refine ⟨147158501189648125278643847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98105667459765416852429231 147158501189648125278643847)
      ·
        refine ⟨220737751784472187917965771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147158501189648125278643847 220737751784472187917965771)
        ·
          refine ⟨331106627676708281876948657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220737751784472187917965771 331106627676708281876948657)
          ·
            refine ⟨248329970757531211407711493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331106627676708281876948657 248329970757531211407711493)
            ·
              refine ⟨46561869517037102138945905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 248329970757531211407711493 46561869517037102138945905)
              ·
                refine ⟨34921402137777826604209429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46561869517037102138945905 34921402137777826604209429)
                ·
                  refine ⟨1636940725208335622072317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 34921402137777826604209429 1636940725208335622072317)
                  ·
                    refine ⟨613852771953125858277119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1636940725208335622072317 613852771953125858277119)
                    ·
                      rfl

theorem cell22_1793211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 6, 3].length) (baseStart_1793211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1793211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1793211 prefixEnd_1793211 := by exact prefixLift 1793211
  have htrace : WordTrace (prefixWord ++ tailWord_1793211) baseStart_1793211 baseEnd_1793211 := by
    simpa [prefixWord, tailWord_1793211, baseEnd_1793211] using wordTrace_append hprefix tailTrace_1793211
  have hstable : (prefixWord ++ tailWord_1793211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793211).length < 2 ^ (prefixWord ++ tailWord_1793211).sum := by decide
  have hdescent : baseEnd_1793211 < baseStart_1793211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793258 : List Nat := [3, 1, 3, 1, 1, 5, 1, 7]
def baseStart_1793258 : Nat := 118140960795 + 1793258 * 2 ^ 59
def prefixEnd_1793258 : Nat := 4983230072969 + 3 ^ 40 * 1793258 * 2
def baseEnd_1793258 : Nat := 68207651223737044705775

theorem tailTrace_1793258 : CollatzResearch.WordTrace tailWord_1793258 prefixEnd_1793258 68207651223737044705775 := by
  unfold tailWord_1793258
  simp only [CollatzResearch.WordTrace]
  refine ⟨16351373134335001232145107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43603661691560003285720285 16351373134335001232145107)
  ·
    refine ⟨24527059701502501848217661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16351373134335001232145107 24527059701502501848217661)
    ·
      refine ⟨9197647388063438193081623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24527059701502501848217661 9197647388063438193081623)
      ·
        refine ⟨13796471082095157289622435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9197647388063438193081623 13796471082095157289622435)
        ·
          refine ⟨20694706623142735934433653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13796471082095157289622435 20694706623142735934433653)
          ·
            refine ⟨1940128745919631493853155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20694706623142735934433653 1940128745919631493853155)
            ·
              refine ⟨2910193118879447240779733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1940128745919631493853155 2910193118879447240779733)
              ·
                refine ⟨68207651223737044705775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2910193118879447240779733 68207651223737044705775)
                ·
                  rfl

theorem cell22_1793258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 7].length) (baseStart_1793258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1793258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1793258 prefixEnd_1793258 := by exact prefixLift 1793258
  have htrace : WordTrace (prefixWord ++ tailWord_1793258) baseStart_1793258 baseEnd_1793258 := by
    simpa [prefixWord, tailWord_1793258, baseEnd_1793258] using wordTrace_append hprefix tailTrace_1793258
  have hstable : (prefixWord ++ tailWord_1793258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793258).length < 2 ^ (prefixWord ++ tailWord_1793258).sum := by decide
  have hdescent : baseEnd_1793258 < baseStart_1793258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793273 : List Nat := [1, 2, 1, 3, 1, 1, 5, 2, 3, 3]
def baseStart_1793273 : Nat := 118140960795 + 1793273 * 2 ^ 59
def prefixEnd_1793273 : Nat := 4983230072969 + 3 ^ 40 * 1793273 * 2
def baseEnd_1793273 : Nat := 613873995820178363226929

theorem tailTrace_1793273 : CollatzResearch.WordTrace tailWord_1793273 prefixEnd_1793273 613873995820178363226929 := by
  unfold tailWord_1793273
  simp only [CollatzResearch.WordTrace]
  refine ⟨65406039632285662490376473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43604026421523774993584315 65406039632285662490376473)
  ·
    refine ⟨49054529724214246867782355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65406039632285662490376473 49054529724214246867782355)
    ·
      refine ⟨73581794586321370301673533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49054529724214246867782355 73581794586321370301673533)
      ·
        refine ⟨27593172969870513863127575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73581794586321370301673533 27593172969870513863127575)
        ·
          refine ⟨41389759454805770794691363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27593172969870513863127575 41389759454805770794691363)
          ·
            refine ⟨62084639182208656192037045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41389759454805770794691363 62084639182208656192037045)
            ·
              refine ⟨5820434923332061518003473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62084639182208656192037045 5820434923332061518003473)
              ·
                refine ⟨4365326192499046138502605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5820434923332061518003473 4365326192499046138502605)
                ·
                  refine ⟨1636997322187142301938477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4365326192499046138502605 1636997322187142301938477)
                  ·
                    refine ⟨613873995820178363226929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1636997322187142301938477 613873995820178363226929)
                    ·
                      rfl

theorem cell22_1793273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 3, 3].length) (baseStart_1793273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1793273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1793273 prefixEnd_1793273 := by exact prefixLift 1793273
  have htrace : WordTrace (prefixWord ++ tailWord_1793273) baseStart_1793273 baseEnd_1793273 := by
    simpa [prefixWord, tailWord_1793273, baseEnd_1793273] using wordTrace_append hprefix tailTrace_1793273
  have hstable : (prefixWord ++ tailWord_1793273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793273).length < 2 ^ (prefixWord ++ tailWord_1793273).sum := by decide
  have hdescent : baseEnd_1793273 < baseStart_1793273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793341 : List Nat := [1, 4, 1, 5, 1, 2, 1, 3, 1, 3]
def baseStart_1793341 : Nat := 118140960795 + 1793341 * 2 ^ 59
def prefixEnd_1793341 : Nat := 4983230072969 + 3 ^ 40 * 1793341 * 2
def baseEnd_1793341 : Nat := 613897273609848852526721

theorem tailTrace_1793341 : CollatzResearch.WordTrace tailWord_1793341 prefixEnd_1793341 613897273609848852526721 := by
  unfold tailWord_1793341
  simp only [CollatzResearch.WordTrace]
  refine ⟨65408519796039310103851877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43605679864026206735901251 65408519796039310103851877)
  ·
    refine ⟨12264097461757370644472227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65408519796039310103851877 12264097461757370644472227)
    ·
      refine ⟨18396146192636055966708341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12264097461757370644472227 18396146192636055966708341)
      ·
        refine ⟨1724638705559630246878907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18396146192636055966708341 1724638705559630246878907)
        ·
          refine ⟨2586958058339445370318361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1724638705559630246878907 2586958058339445370318361)
          ·
            refine ⟨1940218543754584027738771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2586958058339445370318361 1940218543754584027738771)
            ·
              refine ⟨2910327815631876041608157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1940218543754584027738771 2910327815631876041608157)
              ·
                refine ⟨1091372930861953515603059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2910327815631876041608157 1091372930861953515603059)
                ·
                  refine ⟨1637059396292930273404589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1091372930861953515603059 1637059396292930273404589)
                  ·
                    refine ⟨613897273609848852526721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1637059396292930273404589 613897273609848852526721)
                    ·
                      rfl

theorem cell22_1793341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 3, 1, 3].length) (baseStart_1793341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1793341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1793341 prefixEnd_1793341 := by exact prefixLift 1793341
  have htrace : WordTrace (prefixWord ++ tailWord_1793341) baseStart_1793341 baseEnd_1793341 := by
    simpa [prefixWord, tailWord_1793341, baseEnd_1793341] using wordTrace_append hprefix tailTrace_1793341
  have hstable : (prefixWord ++ tailWord_1793341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793341).length < 2 ^ (prefixWord ++ tailWord_1793341).sum := by decide
  have hdescent : baseEnd_1793341 < baseStart_1793341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793363 : List Nat := [1, 1, 1, 2, 1, 1, 5, 3, 4, 3]
def baseStart_1793363 : Nat := 118140960795 + 1793363 * 2 ^ 59
def prefixEnd_1793363 : Nat := 4983230072969 + 3 ^ 40 * 1793363 * 2
def baseEnd_1793363 : Nat := 613904804659448128476653

theorem tailTrace_1793363 : CollatzResearch.WordTrace tailWord_1793363 prefixEnd_1793363 613904804659448128476653 := by
  unfold tailWord_1793363
  simp only [CollatzResearch.WordTrace]
  refine ⟨65409322201959607861152743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43606214801306405240768495 65409322201959607861152743)
  ·
    refine ⟨98113983302939411791729115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65409322201959607861152743 98113983302939411791729115)
    ·
      refine ⟨147170974954409117687593673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98113983302939411791729115 147170974954409117687593673)
      ·
        refine ⟨110378231215806838265695255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147170974954409117687593673 110378231215806838265695255)
        ·
          refine ⟨165567346823710257398542883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110378231215806838265695255 165567346823710257398542883)
          ·
            refine ⟨248351020235565386097814325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165567346823710257398542883 248351020235565386097814325)
            ·
              refine ⟨23282908147084254946670093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 248351020235565386097814325 23282908147084254946670093)
              ·
                refine ⟨8731090555156595605001285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23282908147084254946670093 8731090555156595605001285)
                ·
                  refine ⟨1637079479091861675937741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8731090555156595605001285 1637079479091861675937741)
                  ·
                    refine ⟨613904804659448128476653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1637079479091861675937741 613904804659448128476653)
                    ·
                      rfl

theorem cell22_1793363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 4, 3].length) (baseStart_1793363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1793363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1793363 prefixEnd_1793363 := by exact prefixLift 1793363
  have htrace : WordTrace (prefixWord ++ tailWord_1793363) baseStart_1793363 baseEnd_1793363 := by
    simpa [prefixWord, tailWord_1793363, baseEnd_1793363] using wordTrace_append hprefix tailTrace_1793363
  have hstable : (prefixWord ++ tailWord_1793363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793363).length < 2 ^ (prefixWord ++ tailWord_1793363).sum := by decide
  have hdescent : baseEnd_1793363 < baseStart_1793363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793365 : List Nat := [1, 3, 2, 2, 3, 3, 1, 1, 6]
def baseStart_1793365 : Nat := 118140960795 + 1793365 * 2 ^ 59
def prefixEnd_1793365 : Nat := 4983230072969 + 3 ^ 40 * 1793365 * 2
def baseEnd_1793365 : Nat := 204635163100106929975549

theorem tailTrace_1793365 : CollatzResearch.WordTrace tailWord_1793365 prefixEnd_1793365 204635163100106929975549 := by
  unfold tailWord_1793365
  simp only [CollatzResearch.WordTrace]
  refine ⟨65409395147952362202725549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43606263431968241468483699 65409395147952362202725549)
  ·
    refine ⟨24528523180482135826022081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65409395147952362202725549 24528523180482135826022081)
    ·
      refine ⟨18396392385361601869516561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24528523180482135826022081 18396392385361601869516561)
      ·
        refine ⟨13797294289021201402137421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18396392385361601869516561 13797294289021201402137421)
        ·
          refine ⟨5173985358382950525801533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13797294289021201402137421 5173985358382950525801533)
          ·
            refine ⟨1940244509393606447175575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5173985358382950525801533 1940244509393606447175575)
            ·
              refine ⟨2910366764090409670763363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1940244509393606447175575 2910366764090409670763363)
              ·
                refine ⟨4365550146135614506145045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2910366764090409670763363 4365550146135614506145045)
                ·
                  refine ⟨204635163100106929975549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4365550146135614506145045 204635163100106929975549)
                  ·
                    rfl

theorem cell22_1793365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 6].length) (baseStart_1793365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1793365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1793365 prefixEnd_1793365 := by exact prefixLift 1793365
  have htrace : WordTrace (prefixWord ++ tailWord_1793365) baseStart_1793365 baseEnd_1793365 := by
    simpa [prefixWord, tailWord_1793365, baseEnd_1793365] using wordTrace_append hprefix tailTrace_1793365
  have hstable : (prefixWord ++ tailWord_1793365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793365).length < 2 ^ (prefixWord ++ tailWord_1793365).sum := by decide
  have hdescent : baseEnd_1793365 < baseStart_1793365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793384 : List Nat := [2, 1, 4, 2, 4, 1, 1, 2, 1, 4]
def baseStart_1793384 : Nat := 118140960795 + 1793384 * 2 ^ 59
def prefixEnd_1793384 : Nat := 4983230072969 + 3 ^ 40 * 1793384 * 2
def baseEnd_1793384 : Nat := 613911993388611073701589

theorem tailTrace_1793384 : CollatzResearch.WordTrace tailWord_1793384 prefixEnd_1793384 613911993388611073701589 := by
  unfold tailWord_1793384
  simp only [CollatzResearch.WordTrace]
  refine ⟨32705044067441764223833603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43606725423255685631778137 32705044067441764223833603)
  ·
    refine ⟨49057566101162646335750405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32705044067441764223833603 49057566101162646335750405)
    ·
      refine ⟨9198293643967996187953201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49057566101162646335750405 9198293643967996187953201)
      ·
        refine ⟨6898720232975997140964901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9198293643967996187953201 6898720232975997140964901)
        ·
          refine ⟨1293510043682999463930919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6898720232975997140964901 1293510043682999463930919)
          ·
            refine ⟨1940265065524499195896379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1293510043682999463930919 1940265065524499195896379)
            ·
              refine ⟨2910397598286748793844569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1940265065524499195896379 2910397598286748793844569)
              ·
                refine ⟨2182798198715061595383427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2910397598286748793844569 2182798198715061595383427)
                ·
                  refine ⟨3274197298072592393075141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2182798198715061595383427 3274197298072592393075141)
                  ·
                    refine ⟨613911993388611073701589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3274197298072592393075141 613911993388611073701589)
                    ·
                      rfl

theorem cell22_1793384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_1793384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1793384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1793384 prefixEnd_1793384 := by exact prefixLift 1793384
  have htrace : WordTrace (prefixWord ++ tailWord_1793384) baseStart_1793384 baseEnd_1793384 := by
    simpa [prefixWord, tailWord_1793384, baseEnd_1793384] using wordTrace_append hprefix tailTrace_1793384
  have hstable : (prefixWord ++ tailWord_1793384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793384).length < 2 ^ (prefixWord ++ tailWord_1793384).sum := by decide
  have hdescent : baseEnd_1793384 < baseStart_1793384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793410 : List Nat := [3, 4, 2, 1, 1, 11]
def baseStart_1793410 : Nat := 118140960795 + 1793410 * 2 ^ 59
def prefixEnd_1793410 : Nat := 4983230072969 + 3 ^ 40 * 1793410 * 2
def baseEnd_1793410 : Nat := 7579270292838958920389

theorem tailTrace_1793410 : CollatzResearch.WordTrace tailWord_1793410 prefixEnd_1793410 7579270292838958920389 := by
  unfold tailWord_1793410
  simp only [CollatzResearch.WordTrace]
  refine ⟨16352759108197333722028421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43607357621859556592075789 16352759108197333722028421)
  ·
    refine ⟨3066142332787000072880329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16352759108197333722028421 3066142332787000072880329)
    ·
      refine ⟨2299606749590250054660247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3066142332787000072880329 2299606749590250054660247)
      ·
        refine ⟨3449410124385375081990371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2299606749590250054660247 3449410124385375081990371)
        ·
          refine ⟨5174115186578062622985557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3449410124385375081990371 5174115186578062622985557)
          ·
            refine ⟨7579270292838958920389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5174115186578062622985557 7579270292838958920389)
            ·
              rfl

theorem cell22_1793410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 11].length) (baseStart_1793410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1793410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1793410 prefixEnd_1793410 := by exact prefixLift 1793410
  have htrace : WordTrace (prefixWord ++ tailWord_1793410) baseStart_1793410 baseEnd_1793410 := by
    simpa [prefixWord, tailWord_1793410, baseEnd_1793410] using wordTrace_append hprefix tailTrace_1793410
  have hstable : (prefixWord ++ tailWord_1793410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793410).length < 2 ^ (prefixWord ++ tailWord_1793410).sum := by decide
  have hdescent : baseEnd_1793410 < baseStart_1793410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793442 : List Nat := [3, 3, 1, 2, 1, 3, 1, 2, 3, 3]
def baseStart_1793442 : Nat := 118140960795 + 1793442 * 2 ^ 59
def prefixEnd_1793442 : Nat := 4983230072969 + 3 ^ 40 * 1793442 * 2
def baseEnd_1793442 : Nat := 613931847973918255751411

theorem tailTrace_1793442 : CollatzResearch.WordTrace tailWord_1793442 prefixEnd_1793442 613931847973918255751411 := by
  unfold tailWord_1793442
  simp only [CollatzResearch.WordTrace]
  refine ⟨16353050892168351088319645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43608135712448936235519053 16353050892168351088319645)
  ·
    refine ⟨6132394084563131658119867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16353050892168351088319645 6132394084563131658119867)
    ·
      refine ⟨9198591126844697487179801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6132394084563131658119867 9198591126844697487179801)
      ·
        refine ⟨6898943345133523115384851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9198591126844697487179801 6898943345133523115384851)
        ·
          refine ⟨10348415017700284673077277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6898943345133523115384851 10348415017700284673077277)
          ·
            refine ⟨3880655631637606752403979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10348415017700284673077277 3880655631637606752403979)
            ·
              refine ⟨5820983447456410128605969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3880655631637606752403979 5820983447456410128605969)
              ·
                refine ⟨4365737585592307596454477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5820983447456410128605969 4365737585592307596454477)
                ·
                  refine ⟨1637151594597115348670429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4365737585592307596454477 1637151594597115348670429)
                  ·
                    refine ⟨613931847973918255751411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1637151594597115348670429 613931847973918255751411)
                    ·
                      rfl

theorem cell22_1793442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_1793442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1793442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1793442 prefixEnd_1793442 := by exact prefixLift 1793442
  have htrace : WordTrace (prefixWord ++ tailWord_1793442) baseStart_1793442 baseEnd_1793442 := by
    simpa [prefixWord, tailWord_1793442, baseEnd_1793442] using wordTrace_append hprefix tailTrace_1793442
  have hstable : (prefixWord ++ tailWord_1793442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793442).length < 2 ^ (prefixWord ++ tailWord_1793442).sum := by decide
  have hdescent : baseEnd_1793442 < baseStart_1793442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793483 : List Nat := [1, 1, 1, 1, 3, 3, 3, 3, 6]
def baseStart_1793483 : Nat := 118140960795 + 1793483 * 2 ^ 59
def prefixEnd_1793483 : Nat := 4983230072969 + 3 ^ 40 * 1793483 * 2
def baseEnd_1793483 : Nat := 204648627703935938492095

theorem tailTrace_1793483 : CollatzResearch.WordTrace tailWord_1793483 prefixEnd_1793483 204648627703935938492095 := by
  unfold tailWord_1793483
  simp only [CollatzResearch.WordTrace]
  refine ⟨65413698961524868355521103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43609132641016578903680735 65413698961524868355521103)
  ·
    refine ⟨98120548442287302533281655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65413698961524868355521103 98120548442287302533281655)
    ·
      refine ⟨147180822663430953799922483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98120548442287302533281655 147180822663430953799922483)
      ·
        refine ⟨220771233995146430699883725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147180822663430953799922483 220771233995146430699883725)
        ·
          refine ⟨82789212748179911512456397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220771233995146430699883725 82789212748179911512456397)
          ·
            refine ⟨31045954780567466817171149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82789212748179911512456397 31045954780567466817171149)
            ·
              refine ⟨11642233042712800056439181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31045954780567466817171149 11642233042712800056439181)
              ·
                refine ⟨4365837391017300021164693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11642233042712800056439181 4365837391017300021164693)
                ·
                  refine ⟨204648627703935938492095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4365837391017300021164693 204648627703935938492095)
                  ·
                    rfl

theorem cell22_1793483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 6].length) (baseStart_1793483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1793483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1793483 prefixEnd_1793483 := by exact prefixLift 1793483
  have htrace : WordTrace (prefixWord ++ tailWord_1793483) baseStart_1793483 baseEnd_1793483 := by
    simpa [prefixWord, tailWord_1793483, baseEnd_1793483] using wordTrace_append hprefix tailTrace_1793483
  have hstable : (prefixWord ++ tailWord_1793483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793483).length < 2 ^ (prefixWord ++ tailWord_1793483).sum := by decide
  have hdescent : baseEnd_1793483 < baseStart_1793483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793528 : List Nat := [2, 1, 2, 1, 1, 5, 10]
def baseStart_1793528 : Nat := 118140960795 + 1793528 * 2 ^ 59
def prefixEnd_1793528 : Nat := 4983230072969 + 3 ^ 40 * 1793528 * 2
def baseEnd_1793528 : Nat := 22739306945608988818561

theorem tailTrace_1793528 : CollatzResearch.WordTrace tailWord_1793528 prefixEnd_1793528 22739306945608988818561 := by
  unfold tailWord_1793528
  simp only [CollatzResearch.WordTrace]
  refine ⟨32707670123180920520454619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43610226830907894027272825 32707670123180920520454619)
  ·
    refine ⟨49061505184771380780681929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32707670123180920520454619 49061505184771380780681929)
    ·
      refine ⟨36796128888578535585511447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49061505184771380780681929 36796128888578535585511447)
      ·
        refine ⟨55194193332867803378267171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36796128888578535585511447 55194193332867803378267171)
        ·
          refine ⟨82791289999301705067400757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55194193332867803378267171 82791289999301705067400757)
          ·
            refine ⟨7761683437434534850068821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82791289999301705067400757 7761683437434534850068821)
            ·
              refine ⟨22739306945608988818561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7761683437434534850068821 22739306945608988818561)
              ·
                rfl

theorem cell22_1793528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 10].length) (baseStart_1793528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1793528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1793528 prefixEnd_1793528 := by exact prefixLift 1793528
  have htrace : WordTrace (prefixWord ++ tailWord_1793528) baseStart_1793528 baseEnd_1793528 := by
    simpa [prefixWord, tailWord_1793528, baseEnd_1793528] using wordTrace_append hprefix tailTrace_1793528
  have hstable : (prefixWord ++ tailWord_1793528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793528).length < 2 ^ (prefixWord ++ tailWord_1793528).sum := by decide
  have hdescent : baseEnd_1793528 < baseStart_1793528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793530 : List Nat := [3, 1, 1, 1, 1, 2, 5, 2, 2, 4]
def baseStart_1793530 : Nat := 118140960795 + 1793530 * 2 ^ 59
def prefixEnd_1793530 : Nat := 4983230072969 + 3 ^ 40 * 1793530 * 2
def baseEnd_1793530 : Nat := 613961972172315359551141

theorem tailTrace_1793530 : CollatzResearch.WordTrace tailWord_1793530 prefixEnd_1793530 613961972172315359551141 := by
  unfold tailWord_1793530
  simp only [CollatzResearch.WordTrace]
  refine ⟨16353853298088648845620511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43610275461569730254988029 16353853298088648845620511)
  ·
    refine ⟨24530779947132973268430767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16353853298088648845620511 24530779947132973268430767)
    ·
      refine ⟨36796169920699459902646151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24530779947132973268430767 36796169920699459902646151)
      ·
        refine ⟨55194254881049189853969227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36796169920699459902646151 55194254881049189853969227)
        ·
          refine ⟨82791382321573784780953841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55194254881049189853969227 82791382321573784780953841)
          ·
            refine ⟨62093536741180338585715381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82791382321573784780953841 62093536741180338585715381)
            ·
              refine ⟨5821269069485656742410817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62093536741180338585715381 5821269069485656742410817)
              ·
                refine ⟨4365951802114242556808113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5821269069485656742410817 4365951802114242556808113)
                ·
                  refine ⟨3274463851585681917606085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4365951802114242556808113 3274463851585681917606085)
                  ·
                    refine ⟨613961972172315359551141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3274463851585681917606085 613961972172315359551141)
                    ·
                      rfl

theorem cell22_1793530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 2, 4].length) (baseStart_1793530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1793530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1793530 prefixEnd_1793530 := by exact prefixLift 1793530
  have htrace : WordTrace (prefixWord ++ tailWord_1793530) baseStart_1793530 baseEnd_1793530 := by
    simpa [prefixWord, tailWord_1793530, baseEnd_1793530] using wordTrace_append hprefix tailTrace_1793530
  have hstable : (prefixWord ++ tailWord_1793530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793530).length < 2 ^ (prefixWord ++ tailWord_1793530).sum := by decide
  have hdescent : baseEnd_1793530 < baseStart_1793530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793594 : List Nat := [3, 1, 1, 1, 3, 2, 3, 4, 1, 3]
def baseStart_1793594 : Nat := 118140960795 + 1793594 * 2 ^ 59
def prefixEnd_1793594 : Nat := 4983230072969 + 3 ^ 40 * 1793594 * 2
def baseEnd_1793594 : Nat := 613983880680240525950945

theorem tailTrace_1793594 : CollatzResearch.WordTrace tailWord_1793594 prefixEnd_1793594 613983880680240525950945 := by
  unfold tailWord_1793594
  simp only [CollatzResearch.WordTrace]
  refine ⟨16354436866030683578202959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43611831642748489541874557 16354436866030683578202959)
  ·
    refine ⟨24531655299046025367304439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16354436866030683578202959 24531655299046025367304439)
    ·
      refine ⟨36797482948569038050956659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24531655299046025367304439 36797482948569038050956659)
      ·
        refine ⟨55196224422853557076434989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36797482948569038050956659 55196224422853557076434989)
        ·
          refine ⟨20698584158570083903663121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55196224422853557076434989 20698584158570083903663121)
          ·
            refine ⟨15523938118927562927747341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20698584158570083903663121 15523938118927562927747341)
            ·
              refine ⟨5821476794597836097905253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15523938118927562927747341 5821476794597836097905253)
              ·
                refine ⟨1091526898987094268357235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5821476794597836097905253 1091526898987094268357235)
                ·
                  refine ⟨1637290348480641402535853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1091526898987094268357235 1637290348480641402535853)
                  ·
                    refine ⟨613983880680240525950945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1637290348480641402535853 613983880680240525950945)
                    ·
                      rfl

theorem cell22_1793594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 4, 1, 3].length) (baseStart_1793594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1793594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1793594 prefixEnd_1793594 := by exact prefixLift 1793594
  have htrace : WordTrace (prefixWord ++ tailWord_1793594) baseStart_1793594 baseEnd_1793594 := by
    simpa [prefixWord, tailWord_1793594, baseEnd_1793594] using wordTrace_append hprefix tailTrace_1793594
  have hstable : (prefixWord ++ tailWord_1793594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793594).length < 2 ^ (prefixWord ++ tailWord_1793594).sum := by decide
  have hdescent : baseEnd_1793594 < baseStart_1793594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793605 : List Nat := [1, 3, 1, 1, 1, 4, 3, 1, 2, 5]
def baseStart_1793605 : Nat := 118140960795 + 1793605 * 2 ^ 59
def prefixEnd_1793605 : Nat := 4983230072969 + 3 ^ 40 * 1793605 * 2
def baseEnd_1793605 : Nat := 613987646205040163925911

theorem tailTrace_1793605 : CollatzResearch.WordTrace tailWord_1793605 prefixEnd_1793605 613987646205040163925911 := by
  unfold tailWord_1793605
  simp only [CollatzResearch.WordTrace]
  refine ⟨65418148667082883191462269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43612099111388588794308179 65418148667082883191462269)
  ·
    refine ⟨24531805750156081196798351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65418148667082883191462269 24531805750156081196798351)
    ·
      refine ⟨36797708625234121795197527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24531805750156081196798351 36797708625234121795197527)
      ·
        refine ⟨55196562937851182692796291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36797708625234121795197527 55196562937851182692796291)
        ·
          refine ⟨82794844406776774039194437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55196562937851182692796291 82794844406776774039194437)
          ·
            refine ⟨15524033326270645132348957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82794844406776774039194437 15524033326270645132348957)
            ·
              refine ⟨5821512497351491924630859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15524033326270645132348957 5821512497351491924630859)
              ·
                refine ⟨8732268746027237886946289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5821512497351491924630859 8732268746027237886946289)
                ·
                  refine ⟨6549201559520428415209717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8732268746027237886946289 6549201559520428415209717)
                  ·
                    refine ⟨613987646205040163925911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6549201559520428415209717 613987646205040163925911)
                    ·
                      rfl

theorem cell22_1793605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 5].length) (baseStart_1793605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1793605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1793605 prefixEnd_1793605 := by exact prefixLift 1793605
  have htrace : WordTrace (prefixWord ++ tailWord_1793605) baseStart_1793605 baseEnd_1793605 := by
    simpa [prefixWord, tailWord_1793605, baseEnd_1793605] using wordTrace_append hprefix tailTrace_1793605
  have hstable : (prefixWord ++ tailWord_1793605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793605).length < 2 ^ (prefixWord ++ tailWord_1793605).sum := by decide
  have hdescent : baseEnd_1793605 < baseStart_1793605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793697 : List Nat := [1, 2, 3, 3, 2, 3, 8]
def baseStart_1793697 : Nat := 118140960795 + 1793697 * 2 ^ 59
def prefixEnd_1793697 : Nat := 4983230072969 + 3 ^ 40 * 1793697 * 2
def baseEnd_1793697 : Nat := 22741449617969725578727

theorem tailTrace_1793697 : CollatzResearch.WordTrace tailWord_1793697 prefixEnd_1793697 22741449617969725578727 := by
  unfold tailWord_1793697
  simp only [CollatzResearch.WordTrace]
  refine ⟨65421504182749582903811345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43614336121833055269207563 65421504182749582903811345)
  ·
    refine ⟨49066128137062187177858509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65421504182749582903811345 49066128137062187177858509)
    ·
      refine ⟨18399798051398320191696941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49066128137062187177858509 18399798051398320191696941)
      ·
        refine ⟨6899924269274370071886353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18399798051398320191696941 6899924269274370071886353)
        ·
          refine ⟨5174943201955777553914765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6899924269274370071886353 5174943201955777553914765)
          ·
            refine ⟨1940603700733416582718037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5174943201955777553914765 1940603700733416582718037)
            ·
              refine ⟨22741449617969725578727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1940603700733416582718037 22741449617969725578727)
              ·
                rfl

theorem cell22_1793697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 8].length) (baseStart_1793697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1793697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1793697 prefixEnd_1793697 := by exact prefixLift 1793697
  have htrace : WordTrace (prefixWord ++ tailWord_1793697) baseStart_1793697 baseEnd_1793697 := by
    simpa [prefixWord, tailWord_1793697, baseEnd_1793697] using wordTrace_append hprefix tailTrace_1793697
  have hstable : (prefixWord ++ tailWord_1793697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793697).length < 2 ^ (prefixWord ++ tailWord_1793697).sum := by decide
  have hdescent : baseEnd_1793697 < baseStart_1793697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793718 : List Nat := [5, 1, 3, 1, 1, 2, 1, 3, 2, 3]
def baseStart_1793718 : Nat := 118140960795 + 1793718 * 2 ^ 59
def prefixEnd_1793718 : Nat := 4983230072969 + 3 ^ 40 * 1793718 * 2
def baseEnd_1793718 : Nat := 614026328414345535850565

theorem tailTrace_1793718 : CollatzResearch.WordTrace tailWord_1793718 prefixEnd_1793718 614026328414345535850565 := by
  unfold tailWord_1793718
  simp only [CollatzResearch.WordTrace]
  refine ⟨4088891882229593968145363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43614846743782335660217205 4088891882229593968145363)
  ·
    refine ⟨6133337823344390952218045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4088891882229593968145363 6133337823344390952218045)
    ·
      refine ⟨2300001683754146607081767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6133337823344390952218045 2300001683754146607081767)
      ·
        refine ⟨3450002525631219910622651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2300001683754146607081767 3450002525631219910622651)
        ·
          refine ⟨5175003788446829865933977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3450002525631219910622651 5175003788446829865933977)
          ·
            refine ⟨3881252841335122399450483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5175003788446829865933977 3881252841335122399450483)
            ·
              refine ⟨5821879262002683599175725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3881252841335122399450483 5821879262002683599175725)
              ·
                refine ⟨2183204723251006349690897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5821879262002683599175725 2183204723251006349690897)
                ·
                  refine ⟨1637403542438254762268173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2183204723251006349690897 1637403542438254762268173)
                  ·
                    refine ⟨614026328414345535850565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1637403542438254762268173 614026328414345535850565)
                    ·
                      rfl

theorem cell22_1793718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_1793718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1793718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1793718 prefixEnd_1793718 := by exact prefixLift 1793718
  have htrace : WordTrace (prefixWord ++ tailWord_1793718) baseStart_1793718 baseEnd_1793718 := by
    simpa [prefixWord, tailWord_1793718, baseEnd_1793718] using wordTrace_append hprefix tailTrace_1793718
  have hstable : (prefixWord ++ tailWord_1793718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793718).length < 2 ^ (prefixWord ++ tailWord_1793718).sum := by decide
  have hdescent : baseEnd_1793718 < baseStart_1793718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793763 : List Nat := [1, 1, 1, 7, 2, 1, 1, 4, 1, 3]
def baseStart_1793763 : Nat := 118140960795 + 1793763 * 2 ^ 59
def prefixEnd_1793763 : Nat := 4983230072969 + 3 ^ 40 * 1793763 * 2
def baseEnd_1793763 : Nat := 614041732833980418475427

theorem tailTrace_1793763 : CollatzResearch.WordTrace tailWord_1793763 prefixEnd_1793763 614041732833980418475427 := by
  unfold tailWord_1793763
  simp only [CollatzResearch.WordTrace]
  refine ⟨65423911400510476175713943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43615940933673650783809295 65423911400510476175713943)
  ·
    refine ⟨98135867100765714263570915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65423911400510476175713943 98135867100765714263570915)
    ·
      refine ⟨147203800651148571395356373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98135867100765714263570915 147203800651148571395356373)
      ·
        refine ⟨3450089077761294642078665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 147203800651148571395356373 3450089077761294642078665)
        ·
          refine ⟨2587566808320970981558999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3450089077761294642078665 2587566808320970981558999)
          ·
            refine ⟨3881350212481456472338499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2587566808320970981558999 3881350212481456472338499)
            ·
              refine ⟨5822025318722184708507749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3881350212481456472338499 5822025318722184708507749)
              ·
                refine ⟨1091629747260409632845203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5822025318722184708507749 1091629747260409632845203)
                ·
                  refine ⟨1637444620890614449267805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1091629747260409632845203 1637444620890614449267805)
                  ·
                    refine ⟨614041732833980418475427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1637444620890614449267805 614041732833980418475427)
                    ·
                      rfl

theorem cell22_1793763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 4, 1, 3].length) (baseStart_1793763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1793763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1793763 prefixEnd_1793763 := by exact prefixLift 1793763
  have htrace : WordTrace (prefixWord ++ tailWord_1793763) baseStart_1793763 baseEnd_1793763 := by
    simpa [prefixWord, tailWord_1793763, baseEnd_1793763] using wordTrace_append hprefix tailTrace_1793763
  have hstable : (prefixWord ++ tailWord_1793763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793763).length < 2 ^ (prefixWord ++ tailWord_1793763).sum := by decide
  have hdescent : baseEnd_1793763 < baseStart_1793763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793772 : List Nat := [2, 2, 1, 1, 2, 2, 3, 2, 3, 4]
def baseStart_1793772 : Nat := 118140960795 + 1793772 * 2 ^ 59
def prefixEnd_1793772 : Nat := 4983230072969 + 3 ^ 40 * 1793772 * 2
def baseEnd_1793772 : Nat := 614044813717907395000399

theorem tailTrace_1793772 : CollatzResearch.WordTrace tailWord_1793772 prefixEnd_1793772 614044813717907395000399 := by
  unfold tailWord_1793772
  simp only [CollatzResearch.WordTrace]
  refine ⟨32712119828738935356395785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43616159771651913808527713 32712119828738935356395785)
  ·
    refine ⟨24534089871554201517296839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32712119828738935356395785 24534089871554201517296839)
    ·
      refine ⟨36801134807331302275945259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24534089871554201517296839 36801134807331302275945259)
      ·
        refine ⟨55201702210996953413917889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36801134807331302275945259 55201702210996953413917889)
        ·
          refine ⟨41401276658247715060438417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55201702210996953413917889 41401276658247715060438417)
          ·
            refine ⟨31050957493685786295328813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41401276658247715060438417 31050957493685786295328813)
            ·
              refine ⟨11644109060132169860748305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31050957493685786295328813 11644109060132169860748305)
              ·
                refine ⟨8733081795099127395561229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11644109060132169860748305 8733081795099127395561229)
                ·
                  refine ⟨3274905673162172773335461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8733081795099127395561229 3274905673162172773335461)
                  ·
                    refine ⟨614044813717907395000399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3274905673162172773335461 614044813717907395000399)
                    ·
                      rfl

theorem cell22_1793772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 4].length) (baseStart_1793772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1793772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1793772 prefixEnd_1793772 := by exact prefixLift 1793772
  have htrace : WordTrace (prefixWord ++ tailWord_1793772) baseStart_1793772 baseEnd_1793772 := by
    simpa [prefixWord, tailWord_1793772, baseEnd_1793772] using wordTrace_append hprefix tailTrace_1793772
  have hstable : (prefixWord ++ tailWord_1793772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793772).length < 2 ^ (prefixWord ++ tailWord_1793772).sum := by decide
  have hdescent : baseEnd_1793772 < baseStart_1793772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793804 : List Nat := [2, 2, 1, 2, 2, 1, 3, 5, 4]
def baseStart_1793804 : Nat := 118140960795 + 1793804 * 2 ^ 59
def prefixEnd_1793804 : Nat := 4983230072969 + 3 ^ 40 * 1793804 * 2
def baseEnd_1793804 : Nat := 204685255990623326066767

theorem tailTrace_1793804 : CollatzResearch.WordTrace tailWord_1793804 prefixEnd_1793804 204685255990623326066767 := by
  unfold tailWord_1793804
  simp only [CollatzResearch.WordTrace]
  refine ⟨32712703396680970088978233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43616937862241293451970977 32712703396680970088978233)
  ·
    refine ⟨24534527547510727566733675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32712703396680970088978233 24534527547510727566733675)
    ·
      refine ⟨36801791321266091350100513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24534527547510727566733675 36801791321266091350100513)
      ·
        refine ⟨27601343490949568512575385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36801791321266091350100513 27601343490949568512575385)
        ·
          refine ⟨20701007618212176384431539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27601343490949568512575385 20701007618212176384431539)
          ·
            refine ⟨31051511427318264576647309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20701007618212176384431539 31051511427318264576647309)
            ·
              refine ⟨11644316785244349216242741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31051511427318264576647309 11644316785244349216242741)
              ·
                refine ⟨1091654698616657739022757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11644316785244349216242741 1091654698616657739022757)
                ·
                  refine ⟨204685255990623326066767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1091654698616657739022757 204685255990623326066767)
                  ·
                    rfl

theorem cell22_1793804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 5, 4].length) (baseStart_1793804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1793804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1793804 prefixEnd_1793804 := by exact prefixLift 1793804
  have htrace : WordTrace (prefixWord ++ tailWord_1793804) baseStart_1793804 baseEnd_1793804 := by
    simpa [prefixWord, tailWord_1793804, baseEnd_1793804] using wordTrace_append hprefix tailTrace_1793804
  have hstable : (prefixWord ++ tailWord_1793804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793804).length < 2 ^ (prefixWord ++ tailWord_1793804).sum := by decide
  have hdescent : baseEnd_1793804 < baseStart_1793804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793806 : List Nat := [4, 1, 1, 2, 1, 1, 6, 1, 1, 4]
def baseStart_1793806 : Nat := 118140960795 + 1793806 * 2 ^ 59
def prefixEnd_1793806 : Nat := 4983230072969 + 3 ^ 40 * 1793806 * 2
def baseEnd_1793806 : Nat := 614056452612742639650295

theorem tailTrace_1793806 : CollatzResearch.WordTrace tailWord_1793806 prefixEnd_1793806 614056452612742639650295 := by
  unfold tailWord_1793806
  simp only [CollatzResearch.WordTrace]
  refine ⟨8178184967419336814941159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43616986492903129679686181 8178184967419336814941159)
  ·
    refine ⟨12267277451129005222411739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8178184967419336814941159 12267277451129005222411739)
    ·
      refine ⟨18400916176693507833617609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12267277451129005222411739 18400916176693507833617609)
      ·
        refine ⟨13800687132520130875213207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18400916176693507833617609 13800687132520130875213207)
        ·
          refine ⟨20701030698780196312819811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13800687132520130875213207 20701030698780196312819811)
          ·
            refine ⟨31051546048170294469229717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20701030698780196312819811 31051546048170294469229717)
            ·
              refine ⟨1455541221007982553245143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31051546048170294469229717 1455541221007982553245143)
              ·
                refine ⟨2183311831511973829867715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1455541221007982553245143 2183311831511973829867715)
                ·
                  refine ⟨3274967747267960744801573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2183311831511973829867715 3274967747267960744801573)
                  ·
                    refine ⟨614056452612742639650295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3274967747267960744801573 614056452612742639650295)
                    ·
                      rfl

theorem cell22_1793806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 1, 1, 4].length) (baseStart_1793806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1793806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1793806 prefixEnd_1793806 := by exact prefixLift 1793806
  have htrace : WordTrace (prefixWord ++ tailWord_1793806) baseStart_1793806 baseEnd_1793806 := by
    simpa [prefixWord, tailWord_1793806, baseEnd_1793806] using wordTrace_append hprefix tailTrace_1793806
  have hstable : (prefixWord ++ tailWord_1793806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793806).length < 2 ^ (prefixWord ++ tailWord_1793806).sum := by decide
  have hdescent : baseEnd_1793806 < baseStart_1793806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793973 : List Nat := [1, 3, 3, 2, 1, 3, 2, 3, 4]
def baseStart_1793973 : Nat := 118140960795 + 1793973 * 2 ^ 59
def prefixEnd_1793973 : Nat := 4983230072969 + 3 ^ 40 * 1793973 * 2
def baseEnd_1793973 : Nat := 204704540041869956908261

theorem tailTrace_1793973 : CollatzResearch.WordTrace tailWord_1793973 prefixEnd_1793973 204704540041869956908261 := by
  unfold tailWord_1793973
  simp only [CollatzResearch.WordTrace]
  refine ⟨65431570729749682040858573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43621047153166454693905715 65431570729749682040858573)
  ·
    refine ⟨24536839023656130765321965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65431570729749682040858573 24536839023656130765321965)
    ·
      refine ⟨9201314633871049036995737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24536839023656130765321965 9201314633871049036995737)
      ·
        refine ⟨6900985975403286777746803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9201314633871049036995737 6900985975403286777746803)
        ·
          refine ⟨10351478963104930166620205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6900985975403286777746803 10351478963104930166620205)
          ·
            refine ⟨3881804611164348812482577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10351478963104930166620205 3881804611164348812482577)
            ·
              refine ⟨2911353458373261609361933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3881804611164348812482577 2911353458373261609361933)
              ·
                refine ⟨1091757546889973103510725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2911353458373261609361933 1091757546889973103510725)
                ·
                  refine ⟨204704540041869956908261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1091757546889973103510725 204704540041869956908261)
                  ·
                    rfl

theorem cell22_1793973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 3, 4].length) (baseStart_1793973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1793973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1793973 prefixEnd_1793973 := by exact prefixLift 1793973
  have htrace : WordTrace (prefixWord ++ tailWord_1793973) baseStart_1793973 baseEnd_1793973 := by
    simpa [prefixWord, tailWord_1793973, baseEnd_1793973] using wordTrace_append hprefix tailTrace_1793973
  have hstable : (prefixWord ++ tailWord_1793973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793973).length < 2 ^ (prefixWord ++ tailWord_1793973).sum := by decide
  have hdescent : baseEnd_1793973 < baseStart_1793973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794005 : List Nat := [1, 3, 2, 3, 2, 2, 3, 1, 2, 3]
def baseStart_1794005 : Nat := 118140960795 + 1794005 * 2 ^ 59
def prefixEnd_1794005 : Nat := 4983230072969 + 3 ^ 40 * 1794005 * 2
def baseEnd_1794005 : Nat := 614124574379572453924685

theorem tailTrace_1794005 : CollatzResearch.WordTrace tailWord_1794005 prefixEnd_1794005 614124574379572453924685 := by
  unfold tailWord_1794005
  simp only [CollatzResearch.WordTrace]
  refine ⟨65432737865633751506023469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43621825243755834337348979 65432737865633751506023469)
  ·
    refine ⟨24537276699612656814758801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65432737865633751506023469 24537276699612656814758801)
    ·
      refine ⟨18402957524709492611069101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24537276699612656814758801 18402957524709492611069101)
      ·
        refine ⟨6901109071766059729150913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18402957524709492611069101 6901109071766059729150913)
        ·
          refine ⟨5175831803824544796863185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6901109071766059729150913 5175831803824544796863185)
          ·
            refine ⟨3881873852868408597647389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5175831803824544796863185 3881873852868408597647389)
            ·
              refine ⟨1455702694825653224117771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3881873852868408597647389 1455702694825653224117771)
              ·
                refine ⟨2183554042238479836176657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1455702694825653224117771 2183554042238479836176657)
                ·
                  refine ⟨1637665531678859877132493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2183554042238479836176657 1637665531678859877132493)
                  ·
                    refine ⟨614124574379572453924685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1637665531678859877132493 614124574379572453924685)
                    ·
                      rfl

theorem cell22_1794005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 2, 3].length) (baseStart_1794005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1794005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1794005 prefixEnd_1794005 := by exact prefixLift 1794005
  have htrace : WordTrace (prefixWord ++ tailWord_1794005) baseStart_1794005 baseEnd_1794005 := by
    simpa [prefixWord, tailWord_1794005, baseEnd_1794005] using wordTrace_append hprefix tailTrace_1794005
  have hstable : (prefixWord ++ tailWord_1794005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794005).length < 2 ^ (prefixWord ++ tailWord_1794005).sum := by decide
  have hdescent : baseEnd_1794005 < baseStart_1794005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794018 : List Nat := [3, 3, 3, 1, 2, 1, 1, 8]
def baseStart_1794018 : Nat := 118140960795 + 1794018 * 2 ^ 59
def prefixEnd_1794018 : Nat := 4983230072969 + 3 ^ 40 * 1794018 * 2
def baseEnd_1794018 : Nat := 68236558282804972594405

theorem tailTrace_1794018 : CollatzResearch.WordTrace tailWord_1794018 prefixEnd_1794018 68236558282804972594405 := by
  unfold tailWord_1794018
  simp only [CollatzResearch.WordTrace]
  refine ⟨16358303003646663681561677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43622141343057769817497805 16358303003646663681561677)
  ·
    refine ⟨6134363626367498880585629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16358303003646663681561677 6134363626367498880585629)
    ·
      refine ⟨2300386359887812080219611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6134363626367498880585629 2300386359887812080219611)
      ·
        refine ⟨3450579539831718120329417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2300386359887812080219611 3450579539831718120329417)
        ·
          refine ⟨2587934654873788590247063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3450579539831718120329417 2587934654873788590247063)
          ·
            refine ⟨3881901982310682885370595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2587934654873788590247063 3881901982310682885370595)
            ·
              refine ⟨5822852973466024328055893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3881901982310682885370595 5822852973466024328055893)
              ·
                refine ⟨68236558282804972594405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5822852973466024328055893 68236558282804972594405)
                ·
                  rfl

theorem cell22_1794018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 8].length) (baseStart_1794018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1794018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1794018 prefixEnd_1794018 := by exact prefixLift 1794018
  have htrace : WordTrace (prefixWord ++ tailWord_1794018) baseStart_1794018 baseEnd_1794018 := by
    simpa [prefixWord, tailWord_1794018, baseEnd_1794018] using wordTrace_append hprefix tailTrace_1794018
  have hstable : (prefixWord ++ tailWord_1794018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794018).length < 2 ^ (prefixWord ++ tailWord_1794018).sum := by decide
  have hdescent : baseEnd_1794018 < baseStart_1794018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794108 : List Nat := [2, 2, 2, 2, 2, 1, 3, 4, 4]
def baseStart_1794108 : Nat := 118140960795 + 1794108 * 2 ^ 59
def prefixEnd_1794108 : Nat := 4983230072969 + 3 ^ 40 * 1794108 * 2
def baseEnd_1794108 : Nat := 204719944461504839533123

theorem tailTrace_1794108 : CollatzResearch.WordTrace tailWord_1794108 prefixEnd_1794108 204719944461504839533123 := by
  unfold tailWord_1794108
  simp only [CollatzResearch.WordTrace]
  refine ⟨32718247292130300048511489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43624329722840400064681985 32718247292130300048511489)
  ·
    refine ⟨24538685469097725036383617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32718247292130300048511489 24538685469097725036383617)
    ·
      refine ⟨18404014101823293777287713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24538685469097725036383617 18404014101823293777287713)
      ·
        refine ⟨13803010576367470332965785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18404014101823293777287713 13803010576367470332965785)
        ·
          refine ⟨10352257932275602749724339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13803010576367470332965785 10352257932275602749724339)
          ·
            refine ⟨15528386898413404124586509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10352257932275602749724339 15528386898413404124586509)
            ·
              refine ⟨5823145086905026546719941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15528386898413404124586509 5823145086905026546719941)
              ·
                refine ⟨1091839703794692477509989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5823145086905026546719941 1091839703794692477509989)
                ·
                  refine ⟨204719944461504839533123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1091839703794692477509989 204719944461504839533123)
                  ·
                    rfl

theorem cell22_1794108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 4, 4].length) (baseStart_1794108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1794108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1794108 prefixEnd_1794108 := by exact prefixLift 1794108
  have htrace : WordTrace (prefixWord ++ tailWord_1794108) baseStart_1794108 baseEnd_1794108 := by
    simpa [prefixWord, tailWord_1794108, baseEnd_1794108] using wordTrace_append hprefix tailTrace_1794108
  have hstable : (prefixWord ++ tailWord_1794108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794108).length < 2 ^ (prefixWord ++ tailWord_1794108).sum := by decide
  have hdescent : baseEnd_1794108 < baseStart_1794108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794211 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 7, 4]
def baseStart_1794211 : Nat := 118140960795 + 1794211 * 2 ^ 59
def prefixEnd_1794211 : Nat := 4983230072969 + 3 ^ 40 * 1794211 * 2
def baseEnd_1794211 : Nat := 614195092389456583274053

theorem tailTrace_1794211 : CollatzResearch.WordTrace tailWord_1794211 prefixEnd_1794211 614195092389456583274053 := by
  unfold tailWord_1794211
  simp only [CollatzResearch.WordTrace]
  refine ⟨65440251302887448688022487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43626834201924965792014991 65440251302887448688022487)
  ·
    refine ⟨98160376954331173032033731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65440251302887448688022487 98160376954331173032033731)
    ·
      refine ⟨147240565431496759548050597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98160376954331173032033731 147240565431496759548050597)
      ·
        refine ⟨27607606018405642415259487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147240565431496759548050597 27607606018405642415259487)
        ·
          refine ⟨41411409027608463622889231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27607606018405642415259487 41411409027608463622889231)
          ·
            refine ⟨62117113541412695434333847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41411409027608463622889231 62117113541412695434333847)
            ·
              refine ⟨93175670312119043151500771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62117113541412695434333847 93175670312119043151500771)
              ·
                refine ⟨139763505468178564727251157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93175670312119043151500771 139763505468178564727251157)
                ·
                  refine ⟨3275707159410435110794949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 139763505468178564727251157 3275707159410435110794949)
                  ·
                    refine ⟨614195092389456583274053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3275707159410435110794949 614195092389456583274053)
                    ·
                      rfl

theorem cell22_1794211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7, 4].length) (baseStart_1794211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1794211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1794211 prefixEnd_1794211 := by exact prefixLift 1794211
  have htrace : WordTrace (prefixWord ++ tailWord_1794211) baseStart_1794211 baseEnd_1794211 := by
    simpa [prefixWord, tailWord_1794211, baseEnd_1794211] using wordTrace_append hprefix tailTrace_1794211
  have hstable : (prefixWord ++ tailWord_1794211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794211).length < 2 ^ (prefixWord ++ tailWord_1794211).sum := by decide
  have hdescent : baseEnd_1794211 < baseStart_1794211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794258 : List Nat := [3, 2, 2, 2, 1, 2, 1, 1, 3, 5]
def baseStart_1794258 : Nat := 118140960795 + 1794258 * 2 ^ 59
def prefixEnd_1794258 : Nat := 4983230072969 + 3 ^ 40 * 1794258 * 2
def baseEnd_1794258 : Nat := 614211181449964127348909

theorem tailTrace_1794258 : CollatzResearch.WordTrace tailWord_1794258 prefixEnd_1794258 614211181449964127348909 := by
  unfold tailWord_1794258
  simp only [CollatzResearch.WordTrace]
  refine ⟨16360491383429293928745857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43627977022478117143322285 16360491383429293928745857)
  ·
    refine ⟨12270368537571970446559393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16360491383429293928745857 12270368537571970446559393)
    ·
      refine ⟨9202776403178977834919545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12270368537571970446559393 9202776403178977834919545)
      ·
        refine ⟨6902082302384233376189659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9202776403178977834919545 6902082302384233376189659)
        ·
          refine ⟨10353123453576350064284489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6902082302384233376189659 10353123453576350064284489)
          ·
            refine ⟨7764842590182262548213367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10353123453576350064284489 7764842590182262548213367)
            ·
              refine ⟨11647263885273393822320051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7764842590182262548213367 11647263885273393822320051)
              ·
                refine ⟨17470895827910090733480077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11647263885273393822320051 17470895827910090733480077)
                ·
                  refine ⟨6551585935466284025055029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17470895827910090733480077 6551585935466284025055029)
                  ·
                    refine ⟨614211181449964127348909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6551585935466284025055029 614211181449964127348909)
                    ·
                      rfl

theorem cell22_1794258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_1794258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1794258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1794258 prefixEnd_1794258 := by exact prefixLift 1794258
  have htrace : WordTrace (prefixWord ++ tailWord_1794258) baseStart_1794258 baseEnd_1794258 := by
    simpa [prefixWord, tailWord_1794258, baseEnd_1794258] using wordTrace_append hprefix tailTrace_1794258
  have hstable : (prefixWord ++ tailWord_1794258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794258).length < 2 ^ (prefixWord ++ tailWord_1794258).sum := by decide
  have hdescent : baseEnd_1794258 < baseStart_1794258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794273 : List Nat := [1, 2, 3, 1, 3, 1, 1, 4, 2, 4]
def baseStart_1794273 : Nat := 118140960795 + 1794273 * 2 ^ 59
def prefixEnd_1794273 : Nat := 4983230072969 + 3 ^ 40 * 1794273 * 2
def baseEnd_1794273 : Nat := 614216316256509088223863

theorem tailTrace_1794273 : CollatzResearch.WordTrace tailWord_1794273 prefixEnd_1794273 614216316256509088223863 := by
  unfold tailWord_1794273
  simp only [CollatzResearch.WordTrace]
  refine ⟨65442512628662833276779473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43628341752441888851186315 65442512628662833276779473)
  ·
    refine ⟨49081884471497124957584605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65442512628662833276779473 49081884471497124957584605)
    ·
      refine ⟨18405706676811421859094227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49081884471497124957584605 18405706676811421859094227)
      ·
        refine ⟨27608560015217132788641341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18405706676811421859094227 27608560015217132788641341)
        ·
          refine ⟨10353210005706424795740503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27608560015217132788641341 10353210005706424795740503)
          ·
            refine ⟨15529815008559637193610755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10353210005706424795740503 15529815008559637193610755)
            ·
              refine ⟨23294722512839455790416133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15529815008559637193610755 23294722512839455790416133)
              ·
                refine ⟨4367760471157397960703025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23294722512839455790416133 4367760471157397960703025)
                ·
                  refine ⟨3275820353368048470527269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4367760471157397960703025 3275820353368048470527269)
                  ·
                    refine ⟨614216316256509088223863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3275820353368048470527269 614216316256509088223863)
                    ·
                      rfl

theorem cell22_1794273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_1794273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1794273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1794273 prefixEnd_1794273 := by exact prefixLift 1794273
  have htrace : WordTrace (prefixWord ++ tailWord_1794273) baseStart_1794273 baseEnd_1794273 := by
    simpa [prefixWord, tailWord_1794273, baseEnd_1794273] using wordTrace_append hprefix tailTrace_1794273
  have hstable : (prefixWord ++ tailWord_1794273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794273).length < 2 ^ (prefixWord ++ tailWord_1794273).sum := by decide
  have hdescent : baseEnd_1794273 < baseStart_1794273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794277 : List Nat := [1, 3, 1, 4, 2, 1, 4, 2, 4]
def baseStart_1794277 : Nat := 118140960795 + 1794277 * 2 ^ 59
def prefixEnd_1794277 : Nat := 4983230072969 + 3 ^ 40 * 1794277 * 2
def baseEnd_1794277 : Nat := 204739228512751470374617

theorem tailTrace_1794277 : CollatzResearch.WordTrace tailWord_1794277 prefixEnd_1794277 204739228512751470374617 := by
  unfold tailWord_1794277
  simp only [CollatzResearch.WordTrace]
  refine ⟨65442658520648341959925085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43628439013765561306616723 65442658520648341959925085)
  ·
    refine ⟨24540996945243128234971907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65442658520648341959925085 24540996945243128234971907)
    ·
      refine ⟨36811495417864692352457861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24540996945243128234971907 36811495417864692352457861)
      ·
        refine ⟨6902155390849629816085849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36811495417864692352457861 6902155390849629816085849)
        ·
          refine ⟨5176616543137222362064387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6902155390849629816085849 5176616543137222362064387)
          ·
            refine ⟨7764924814705833543096581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5176616543137222362064387 7764924814705833543096581)
            ·
              refine ⟨1455923402757343789330609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7764924814705833543096581 1455923402757343789330609)
              ·
                refine ⟨1091942552068007841997957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1455923402757343789330609 1091942552068007841997957)
                ·
                  refine ⟨204739228512751470374617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1091942552068007841997957 204739228512751470374617)
                  ·
                    rfl

theorem cell22_1794277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 2, 4].length) (baseStart_1794277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1794277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1794277 prefixEnd_1794277 := by exact prefixLift 1794277
  have htrace : WordTrace (prefixWord ++ tailWord_1794277) baseStart_1794277 baseEnd_1794277 := by
    simpa [prefixWord, tailWord_1794277, baseEnd_1794277] using wordTrace_append hprefix tailTrace_1794277
  have hstable : (prefixWord ++ tailWord_1794277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794277).length < 2 ^ (prefixWord ++ tailWord_1794277).sum := by decide
  have hdescent : baseEnd_1794277 < baseStart_1794277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794337 : List Nat := [1, 2, 3, 2, 1, 1, 4, 4, 1, 3]
def baseStart_1794337 : Nat := 118140960795 + 1794337 * 2 ^ 59
def prefixEnd_1794337 : Nat := 4983230072969 + 3 ^ 40 * 1794337 * 2
def baseEnd_1794337 : Nat := 614238224764434254623667

theorem tailTrace_1794337 : CollatzResearch.WordTrace tailWord_1794337 prefixEnd_1794337 614238224764434254623667 := by
  unfold tailWord_1794337
  simp only [CollatzResearch.WordTrace]
  refine ⟨65444846900430972207109265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43629897933620648138072843 65444846900430972207109265)
  ·
    refine ⟨49083635175323229155331949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65444846900430972207109265 49083635175323229155331949)
    ·
      refine ⟨18406363190746210933249481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49083635175323229155331949 18406363190746210933249481)
      ·
        refine ⟨13804772393059658199937111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18406363190746210933249481 13804772393059658199937111)
        ·
          refine ⟨20707158589589487299905667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13804772393059658199937111 20707158589589487299905667)
          ·
            refine ⟨31060737884384230949858501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20707158589589487299905667 31060737884384230949858501)
            ·
              refine ⟨5823888353322043303098469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31060737884384230949858501 5823888353322043303098469)
              ·
                refine ⟨1091979066247883119330963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5823888353322043303098469 1091979066247883119330963)
                ·
                  refine ⟨1637968599371824678996445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1091979066247883119330963 1637968599371824678996445)
                  ·
                    refine ⟨614238224764434254623667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1637968599371824678996445 614238224764434254623667)
                    ·
                      rfl

theorem cell22_1794337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 4, 1, 3].length) (baseStart_1794337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1794337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1794337 prefixEnd_1794337 := by exact prefixLift 1794337
  have htrace : WordTrace (prefixWord ++ tailWord_1794337) baseStart_1794337 baseEnd_1794337 := by
    simpa [prefixWord, tailWord_1794337, baseEnd_1794337] using wordTrace_append hprefix tailTrace_1794337
  have hstable : (prefixWord ++ tailWord_1794337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794337).length < 2 ^ (prefixWord ++ tailWord_1794337).sum := by decide
  have hdescent : baseEnd_1794337 < baseStart_1794337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794343 : List Nat := [1, 1, 8, 1, 1, 1, 3, 1, 2, 3]
def baseStart_1794343 : Nat := 118140960795 + 1794343 * 2 ^ 59
def prefixEnd_1794343 : Nat := 4983230072969 + 3 ^ 40 * 1794343 * 2
def baseEnd_1794343 : Nat := 614240278687052238973649

theorem tailTrace_1794343 : CollatzResearch.WordTrace tailWord_1794343 prefixEnd_1794343 614240278687052238973649 := by
  unfold tailWord_1794343
  simp only [CollatzResearch.WordTrace]
  refine ⟨65445065738409235231827683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43630043825606156821218455 65445065738409235231827683)
  ·
    refine ⟨98167598607613852847741525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65445065738409235231827683 98167598607613852847741525)
    ·
      refine ⟨1150401546182974838059471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 98167598607613852847741525 1150401546182974838059471)
      ·
        refine ⟨1725602319274462257089207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1150401546182974838059471 1725602319274462257089207)
        ·
          refine ⟨2588403478911693385633811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1725602319274462257089207 2588403478911693385633811)
          ·
            refine ⟨3882605218367540078450717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2588403478911693385633811 3882605218367540078450717)
            ·
              refine ⟨1455976956887827529419019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3882605218367540078450717 1455976956887827529419019)
              ·
                refine ⟨2183965435331741294128529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1455976956887827529419019 2183965435331741294128529)
                ·
                  refine ⟨1637974076498805970596397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2183965435331741294128529 1637974076498805970596397)
                  ·
                    refine ⟨614240278687052238973649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1637974076498805970596397 614240278687052238973649)
                    ·
                      rfl

theorem cell22_1794343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_1794343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1794343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1794343 prefixEnd_1794343 := by exact prefixLift 1794343
  have htrace : WordTrace (prefixWord ++ tailWord_1794343) baseStart_1794343 baseEnd_1794343 := by
    simpa [prefixWord, tailWord_1794343, baseEnd_1794343] using wordTrace_append hprefix tailTrace_1794343
  have hstable : (prefixWord ++ tailWord_1794343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794343).length < 2 ^ (prefixWord ++ tailWord_1794343).sum := by decide
  have hdescent : baseEnd_1794343 < baseStart_1794343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794348 : List Nat := [2, 2, 1, 1, 1, 3, 4, 1, 2, 5]
def baseStart_1794348 : Nat := 118140960795 + 1794348 * 2 ^ 59
def prefixEnd_1794348 : Nat := 4983230072969 + 3 ^ 40 * 1794348 * 2
def baseEnd_1794348 : Nat := 614241990289233892598633

theorem tailTrace_1794348 : CollatzResearch.WordTrace tailWord_1794348 prefixEnd_1794348 614241990289233892598633 := by
  unfold tailWord_1794348
  simp only [CollatzResearch.WordTrace]
  refine ⟨32722624051695560542879849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43630165402260747390506465 32722624051695560542879849)
  ·
    refine ⟨24541968038771670407159887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32722624051695560542879849 24541968038771670407159887)
    ·
      refine ⟨36812952058157505610739831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24541968038771670407159887 36812952058157505610739831)
      ·
        refine ⟨55219428087236258416109747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36812952058157505610739831 55219428087236258416109747)
        ·
          refine ⟨82829142130854387624164621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55219428087236258416109747 82829142130854387624164621)
          ·
            refine ⟨31060928299070395359061733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82829142130854387624164621 31060928299070395359061733)
            ·
              refine ⟨5823924056075699129824075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31060928299070395359061733 5823924056075699129824075)
              ·
                refine ⟨8735886084113548694736113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5823924056075699129824075 8735886084113548694736113)
                ·
                  refine ⟨6551914563085161521052085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8735886084113548694736113 6551914563085161521052085)
                  ·
                    refine ⟨614241990289233892598633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6551914563085161521052085 614241990289233892598633)
                    ·
                      rfl

theorem cell22_1794348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 5].length) (baseStart_1794348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1794348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1794348 prefixEnd_1794348 := by exact prefixLift 1794348
  have htrace : WordTrace (prefixWord ++ tailWord_1794348) baseStart_1794348 baseEnd_1794348 := by
    simpa [prefixWord, tailWord_1794348, baseEnd_1794348] using wordTrace_append hprefix tailTrace_1794348
  have hstable : (prefixWord ++ tailWord_1794348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794348).length < 2 ^ (prefixWord ++ tailWord_1794348).sum := by decide
  have hdescent : baseEnd_1794348 < baseStart_1794348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794380 : List Nat := [2, 2, 1, 3, 2, 1, 1, 5, 1, 4]
def baseStart_1794380 : Nat := 118140960795 + 1794380 * 2 ^ 59
def prefixEnd_1794380 : Nat := 4983230072969 + 3 ^ 40 * 1794380 * 2
def baseEnd_1794380 : Nat := 614252944543196475798535

theorem tailTrace_1794380 : CollatzResearch.WordTrace tailWord_1794380 prefixEnd_1794380 614252944543196475798535 := by
  unfold tailWord_1794380
  simp only [CollatzResearch.WordTrace]
  refine ⟨32723207619637595275462297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43630943492850127033949729 32723207619637595275462297)
  ·
    refine ⟨24542405714728196456596723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32723207619637595275462297 24542405714728196456596723)
    ·
      refine ⟨36813608572092294684895085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24542405714728196456596723 36813608572092294684895085)
      ·
        refine ⟨13805103214534610506835657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36813608572092294684895085 13805103214534610506835657)
        ·
          refine ⟨10353827410900957880126743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13805103214534610506835657 10353827410900957880126743)
          ·
            refine ⟨15530741116351436820190115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10353827410900957880126743 15530741116351436820190115)
            ·
              refine ⟨23296111674527155230285173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15530741116351436820190115 23296111674527155230285173)
              ·
                refine ⟨2184010469486920802839235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23296111674527155230285173 2184010469486920802839235)
                ·
                  refine ⟨3276015704230381204258853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2184010469486920802839235 3276015704230381204258853)
                  ·
                    refine ⟨614252944543196475798535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3276015704230381204258853 614252944543196475798535)
                    ·
                      rfl

theorem cell22_1794380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5, 1, 4].length) (baseStart_1794380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1794380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1794380 prefixEnd_1794380 := by exact prefixLift 1794380
  have htrace : WordTrace (prefixWord ++ tailWord_1794380) baseStart_1794380 baseEnd_1794380 := by
    simpa [prefixWord, tailWord_1794380, baseEnd_1794380] using wordTrace_append hprefix tailTrace_1794380
  have hstable : (prefixWord ++ tailWord_1794380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794380).length < 2 ^ (prefixWord ++ tailWord_1794380).sum := by decide
  have hdescent : baseEnd_1794380 < baseStart_1794380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794446 : List Nat := [4, 1, 1, 4, 1, 3, 2, 2, 4]
def baseStart_1794446 : Nat := 118140960795 + 1794446 * 2 ^ 59
def prefixEnd_1794446 : Nat := 4983230072969 + 3 ^ 40 * 1794446 * 2
def baseEnd_1794446 : Nat := 204758512563998101216111

theorem tailTrace_1794446 : CollatzResearch.WordTrace tailWord_1794446 prefixEnd_1794446 204758512563998101216111 := by
  unfold tailWord_1794446
  simp only [CollatzResearch.WordTrace]
  refine ⟨8181102807129510477853399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43632548304690722548551461 8181102807129510477853399)
  ·
    refine ⟨12271654210694265716780099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8181102807129510477853399 12271654210694265716780099)
    ·
      refine ⟨18407481316041398575170149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12271654210694265716780099 18407481316041398575170149)
      ·
        refine ⟨3451402746757762232844403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18407481316041398575170149 3451402746757762232844403)
        ·
          refine ⟨5177104120136643349266605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3451402746757762232844403 5177104120136643349266605)
          ·
            refine ⟨1941414045051241255974977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5177104120136643349266605 1941414045051241255974977)
            ·
              refine ⟨1456060533788430941981233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1941414045051241255974977 1456060533788430941981233)
              ·
                refine ⟨1092045400341323206485925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1456060533788430941981233 1092045400341323206485925)
                ·
                  refine ⟨204758512563998101216111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1092045400341323206485925 204758512563998101216111)
                  ·
                    rfl

theorem cell22_1794446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 2, 4].length) (baseStart_1794446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1794446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1794446 prefixEnd_1794446 := by exact prefixLift 1794446
  have htrace : WordTrace (prefixWord ++ tailWord_1794446) baseStart_1794446 baseEnd_1794446 := by
    simpa [prefixWord, tailWord_1794446, baseEnd_1794446] using wordTrace_append hprefix tailTrace_1794446
  have hstable : (prefixWord ++ tailWord_1794446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794446).length < 2 ^ (prefixWord ++ tailWord_1794446).sum := by decide
  have hdescent : baseEnd_1794446 < baseStart_1794446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794489 : List Nat := [1, 2, 1, 4, 3, 1, 1, 5, 1, 3]
def baseStart_1794489 : Nat := 118140960795 + 1794489 * 2 ^ 59
def prefixEnd_1794489 : Nat := 4983230072969 + 3 ^ 40 * 1794489 * 2
def baseEnd_1794489 : Nat := 614290257470756524823201

theorem tailTrace_1794489 : CollatzResearch.WordTrace tailWord_1794489 prefixEnd_1794489 614290257470756524823201 := by
  unfold tailWord_1794489
  simp only [CollatzResearch.WordTrace]
  refine ⟨65450390795880302166642521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43633593863920201444428347 65450390795880302166642521)
  ·
    refine ⟨49087793096910226624981891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65450390795880302166642521 49087793096910226624981891)
    ·
      refine ⟨73631689645365339937472837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49087793096910226624981891 73631689645365339937472837)
      ·
        refine ⟨13805941808506001238276157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73631689645365339937472837 13805941808506001238276157)
        ·
          refine ⟨5177228178189750464353559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13805941808506001238276157 5177228178189750464353559)
          ·
            refine ⟨7765842267284625696530339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5177228178189750464353559 7765842267284625696530339)
            ·
              refine ⟨11648763400926938544795509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7765842267284625696530339 11648763400926938544795509)
              ·
                refine ⟨1092071568836900488574579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11648763400926938544795509 1092071568836900488574579)
                ·
                  refine ⟨1638107353255350732861869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1092071568836900488574579 1638107353255350732861869)
                  ·
                    refine ⟨614290257470756524823201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1638107353255350732861869 614290257470756524823201)
                    ·
                      rfl

theorem cell22_1794489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 5, 1, 3].length) (baseStart_1794489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1794489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1794489 prefixEnd_1794489 := by exact prefixLift 1794489
  have htrace : WordTrace (prefixWord ++ tailWord_1794489) baseStart_1794489 baseEnd_1794489 := by
    simpa [prefixWord, tailWord_1794489, baseEnd_1794489] using wordTrace_append hprefix tailTrace_1794489
  have hstable : (prefixWord ++ tailWord_1794489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794489).length < 2 ^ (prefixWord ++ tailWord_1794489).sum := by decide
  have hdescent : baseEnd_1794489 < baseStart_1794489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794545 : List Nat := [1, 2, 2, 2, 3, 1, 2, 1, 3, 5]
def baseStart_1794545 : Nat := 118140960795 + 1794545 * 2 ^ 59
def prefixEnd_1794545 : Nat := 4983230072969 + 3 ^ 40 * 1794545 * 2
def baseEnd_1794545 : Nat := 614309427415191045423029

theorem tailTrace_1794545 : CollatzResearch.WordTrace tailWord_1794545 prefixEnd_1794545 614309427415191045423029 := by
  unfold tailWord_1794545
  simp only [CollatzResearch.WordTrace]
  refine ⟨65452433283677423730681089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43634955522451615820454059 65452433283677423730681089)
  ·
    refine ⟨49089324962758067798010817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65452433283677423730681089 49089324962758067798010817)
    ·
      refine ⟨36816993722068550848508113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49089324962758067798010817 36816993722068550848508113)
      ·
        refine ⟨27612745291551413136381085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36816993722068550848508113 27612745291551413136381085)
        ·
          refine ⟨10354779484331779926142907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27612745291551413136381085 10354779484331779926142907)
          ·
            refine ⟨15532169226497669889214361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10354779484331779926142907 15532169226497669889214361)
            ·
              refine ⟨11649126919873252416910771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15532169226497669889214361 11649126919873252416910771)
              ·
                refine ⟨17473690379809878625366157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11649126919873252416910771 17473690379809878625366157)
                ·
                  refine ⟨6552633892428704484512309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17473690379809878625366157 6552633892428704484512309)
                  ·
                    refine ⟨614309427415191045423029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6552633892428704484512309 614309427415191045423029)
                    ·
                      rfl

theorem cell22_1794545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_1794545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1794545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1794545 prefixEnd_1794545 := by exact prefixLift 1794545
  have htrace : WordTrace (prefixWord ++ tailWord_1794545) baseStart_1794545 baseEnd_1794545 := by
    simpa [prefixWord, tailWord_1794545, baseEnd_1794545] using wordTrace_append hprefix tailTrace_1794545
  have hstable : (prefixWord ++ tailWord_1794545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794545).length < 2 ^ (prefixWord ++ tailWord_1794545).sum := by decide
  have hdescent : baseEnd_1794545 < baseStart_1794545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794564 : List Nat := [2, 3, 2, 3, 1, 3, 1, 1, 6]
def baseStart_1794564 : Nat := 118140960795 + 1794564 * 2 ^ 59
def prefixEnd_1794564 : Nat := 4983230072969 + 3 ^ 40 * 1794564 * 2
def baseEnd_1794564 : Nat := 204771977167827109732657

theorem tailTrace_1794564 : CollatzResearch.WordTrace tailWord_1794564 prefixEnd_1794564 204771977167827109732657 := by
  unfold tailWord_1794564
  simp only [CollatzResearch.WordTrace]
  refine ⟨32726563135304294987811373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43635417513739059983748497 32726563135304294987811373)
  ·
    refine ⟨12272461175739110620429265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32726563135304294987811373 12272461175739110620429265)
    ·
      refine ⟨9204345881804332965321949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12272461175739110620429265 9204345881804332965321949)
      ·
        refine ⟨3451629705676624861995731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9204345881804332965321949 3451629705676624861995731)
        ·
          refine ⟨5177444558514937292993597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3451629705676624861995731 5177444558514937292993597)
          ·
            refine ⟨1941541709443101484872599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5177444558514937292993597 1941541709443101484872599)
            ·
              refine ⟨2912312564164652227308899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1941541709443101484872599 2912312564164652227308899)
              ·
                refine ⟨4368468846246978340963349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2912312564164652227308899 4368468846246978340963349)
                ·
                  refine ⟨204771977167827109732657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4368468846246978340963349 204771977167827109732657)
                  ·
                    rfl

theorem cell22_1794564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 6].length) (baseStart_1794564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1794564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1794564 prefixEnd_1794564 := by exact prefixLift 1794564
  have htrace : WordTrace (prefixWord ++ tailWord_1794564) baseStart_1794564 baseEnd_1794564 := by
    simpa [prefixWord, tailWord_1794564, baseEnd_1794564] using wordTrace_append hprefix tailTrace_1794564
  have hstable : (prefixWord ++ tailWord_1794564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794564).length < 2 ^ (prefixWord ++ tailWord_1794564).sum := by decide
  have hdescent : baseEnd_1794564 < baseStart_1794564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794583 : List Nat := [1, 1, 3, 6, 2, 1, 1, 2, 1, 4]
def baseStart_1794583 : Nat := 118140960795 + 1794583 * 2 ^ 59
def prefixEnd_1794583 : Nat := 4983230072969 + 3 ^ 40 * 1794583 * 2
def baseEnd_1794583 : Nat := 614322435591771612972913

theorem tailTrace_1794583 : CollatzResearch.WordTrace tailWord_1794583 prefixEnd_1794583 614322435591771612972913 := by
  unfold tailWord_1794583
  simp only [CollatzResearch.WordTrace]
  refine ⟨65453819257539756220564403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43635879505026504147042935 65453819257539756220564403)
  ·
    refine ⟨98180728886309634330846605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65453819257539756220564403 98180728886309634330846605)
    ·
      refine ⟨36817773332366112874067477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98180728886309634330846605 36817773332366112874067477)
      ·
        refine ⟨1725833124954661540971913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 36817773332366112874067477 1725833124954661540971913)
        ·
          refine ⟨1294374843715996155728935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1725833124954661540971913 1294374843715996155728935)
          ·
            refine ⟨1941562265573994233593403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1294374843715996155728935 1941562265573994233593403)
            ·
              refine ⟨2912343398360991350390105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1941562265573994233593403 2912343398360991350390105)
              ·
                refine ⟨2184257548770743512792579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2912343398360991350390105 2184257548770743512792579)
                ·
                  refine ⟨3276386323156115269188869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2184257548770743512792579 3276386323156115269188869)
                  ·
                    refine ⟨614322435591771612972913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3276386323156115269188869 614322435591771612972913)
                    ·
                      rfl

theorem cell22_1794583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 2, 1, 4].length) (baseStart_1794583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1794583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1794583 prefixEnd_1794583 := by exact prefixLift 1794583
  have htrace : WordTrace (prefixWord ++ tailWord_1794583) baseStart_1794583 baseEnd_1794583 := by
    simpa [prefixWord, tailWord_1794583, baseEnd_1794583] using wordTrace_append hprefix tailTrace_1794583
  have hstable : (prefixWord ++ tailWord_1794583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794583).length < 2 ^ (prefixWord ++ tailWord_1794583).sum := by decide
  have hdescent : baseEnd_1794583 < baseStart_1794583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794635 : List Nat := [1, 1, 1, 1, 3, 1, 5, 1, 1, 7]
def baseStart_1794635 : Nat := 118140960795 + 1794635 * 2 ^ 59
def prefixEnd_1794635 : Nat := 4983230072969 + 3 ^ 40 * 1794635 * 2
def baseEnd_1794635 : Nat := 614340236254460810672753

theorem tailTrace_1794635 : CollatzResearch.WordTrace tailWord_1794635 prefixEnd_1794635 614340236254460810672753 := by
  unfold tailWord_1794635
  simp only [CollatzResearch.WordTrace]
  refine ⟨65455715853351369101457359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43637143902234246067638239 65455715853351369101457359)
  ·
    refine ⟨98183573780027053652186039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65455715853351369101457359 98183573780027053652186039)
    ·
      refine ⟨147275360670040580478279059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98183573780027053652186039 147275360670040580478279059)
      ·
        refine ⟨220913041005060870717418589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147275360670040580478279059 220913041005060870717418589)
        ·
          refine ⟨82842390376897826519031971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220913041005060870717418589 82842390376897826519031971)
          ·
            refine ⟨124263585565346739778547957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82842390376897826519031971 124263585565346739778547957)
            ·
              refine ⟨11649711146751256854238871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 124263585565346739778547957 11649711146751256854238871)
              ·
                refine ⟨17474566720126885281358307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11649711146751256854238871 17474566720126885281358307)
                ·
                  refine ⟨26211850080190327922037461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17474566720126885281358307 26211850080190327922037461)
                  ·
                    refine ⟨614340236254460810672753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26211850080190327922037461 614340236254460810672753)
                    ·
                      rfl

theorem cell22_1794635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 7].length) (baseStart_1794635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1794635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1794635 prefixEnd_1794635 := by exact prefixLift 1794635
  have htrace : WordTrace (prefixWord ++ tailWord_1794635) baseStart_1794635 baseEnd_1794635 := by
    simpa [prefixWord, tailWord_1794635, baseEnd_1794635] using wordTrace_append hprefix tailTrace_1794635
  have hstable : (prefixWord ++ tailWord_1794635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794635).length < 2 ^ (prefixWord ++ tailWord_1794635).sum := by decide
  have hdescent : baseEnd_1794635 < baseStart_1794635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794665 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 10]
def baseStart_1794665 : Nat := 118140960795 + 1794665 * 2 ^ 59
def prefixEnd_1794665 : Nat := 4983230072969 + 3 ^ 40 * 1794665 * 2
def baseEnd_1794665 : Nat := 204783501955850244140887

theorem tailTrace_1794665 : CollatzResearch.WordTrace tailWord_1794665 prefixEnd_1794665 204783501955850244140887 := by
  unfold tailWord_1794665
  simp only [CollatzResearch.WordTrace]
  refine ⟨65456810043242684225049449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43637873362161789483366299 65456810043242684225049449)
  ·
    refine ⟨49092607532432013168787087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65456810043242684225049449 49092607532432013168787087)
    ·
      refine ⟨73638911298648019753180631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49092607532432013168787087 73638911298648019753180631)
      ·
        refine ⟨110458366947972029629770947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73638911298648019753180631 110458366947972029629770947)
        ·
          refine ⟨165687550421958044444656421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110458366947972029629770947 165687550421958044444656421)
          ·
            refine ⟨31066415704117133333373079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165687550421958044444656421 31066415704117133333373079)
            ·
              refine ⟨46599623556175700000059619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31066415704117133333373079 46599623556175700000059619)
              ·
                refine ⟨69899435334263550000089429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46599623556175700000059619 69899435334263550000089429)
                ·
                  refine ⟨204783501955850244140887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 69899435334263550000089429 204783501955850244140887)
                  ·
                    rfl

theorem cell22_1794665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 10].length) (baseStart_1794665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1794665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1794665 prefixEnd_1794665 := by exact prefixLift 1794665
  have htrace : WordTrace (prefixWord ++ tailWord_1794665) baseStart_1794665 baseEnd_1794665 := by
    simpa [prefixWord, tailWord_1794665, baseEnd_1794665] using wordTrace_append hprefix tailTrace_1794665
  have hstable : (prefixWord ++ tailWord_1794665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794665).length < 2 ^ (prefixWord ++ tailWord_1794665).sum := by decide
  have hdescent : baseEnd_1794665 < baseStart_1794665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794712 : List Nat := [2, 1, 2, 4, 1, 1, 1, 3, 1, 6]
def baseStart_1794712 : Nat := 118140960795 + 1794712 * 2 ^ 59
def prefixEnd_1794712 : Nat := 4983230072969 + 3 ^ 40 * 1794712 * 2
def baseEnd_1794712 : Nat := 614366594928058276497517

theorem tailTrace_1794712 : CollatzResearch.WordTrace tailWord_1794712 prefixEnd_1794712 614366594928058276497517 := by
  unfold tailWord_1794712
  simp only [CollatzResearch.WordTrace]
  refine ⟨32729262137036205626005195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43639016182714940834673593 32729262137036205626005195)
  ·
    refine ⟨49093893205554308439007793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32729262137036205626005195 49093893205554308439007793)
    ·
      refine ⟨36820419904165731329255845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49093893205554308439007793 36820419904165731329255845)
      ·
        refine ⟨6903828732031074624235471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36820419904165731329255845 6903828732031074624235471)
        ·
          refine ⟨10355743098046611936353207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6903828732031074624235471 10355743098046611936353207)
          ·
            refine ⟨15533614647069917904529811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10355743098046611936353207 15533614647069917904529811)
            ·
              refine ⟨23300421970604876856794717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15533614647069917904529811 23300421970604876856794717)
              ·
                refine ⟨8737658238976828821298019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23300421970604876856794717 8737658238976828821298019)
                ·
                  refine ⟨13106487358465243231947029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8737658238976828821298019 13106487358465243231947029)
                  ·
                    refine ⟨614366594928058276497517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13106487358465243231947029 614366594928058276497517)
                    ·
                      rfl

theorem cell22_1794712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_1794712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1794712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1794712 prefixEnd_1794712 := by exact prefixLift 1794712
  have htrace : WordTrace (prefixWord ++ tailWord_1794712) baseStart_1794712 baseEnd_1794712 := by
    simpa [prefixWord, tailWord_1794712, baseEnd_1794712] using wordTrace_append hprefix tailTrace_1794712
  have hstable : (prefixWord ++ tailWord_1794712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794712).length < 2 ^ (prefixWord ++ tailWord_1794712).sum := by decide
  have hdescent : baseEnd_1794712 < baseStart_1794712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794716 : List Nat := [2, 2, 3, 2, 2, 1, 3, 3, 4]
def baseStart_1794716 : Nat := 118140960795 + 1794716 * 2 ^ 59
def prefixEnd_1794716 : Nat := 4983230072969 + 3 ^ 40 * 1794716 * 2
def baseEnd_1794716 : Nat := 204789321403267866465835

theorem tailTrace_1794716 : CollatzResearch.WordTrace tailWord_1794716 prefixEnd_1794716 204789321403267866465835 := by
  unfold tailWord_1794716
  simp only [CollatzResearch.WordTrace]
  refine ⟨32729335083028959967578001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43639113444038613290104001 32729335083028959967578001)
  ·
    refine ⟨24547001312271719975683501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32729335083028959967578001 24547001312271719975683501)
    ·
      refine ⟨9205125492101894990881313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24547001312271719975683501 9205125492101894990881313)
      ·
        refine ⟨6903844119076421243160985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9205125492101894990881313 6903844119076421243160985)
        ·
          refine ⟨5177883089307315932370739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6903844119076421243160985 5177883089307315932370739)
          ·
            refine ⟨7766824633960973898556109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5177883089307315932370739 7766824633960973898556109)
            ·
              refine ⟨2912559237735365211958541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7766824633960973898556109 2912559237735365211958541)
              ·
                refine ⟨1092209714150761954484453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2912559237735365211958541 1092209714150761954484453)
                ·
                  refine ⟨204789321403267866465835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1092209714150761954484453 204789321403267866465835)
                  ·
                    rfl

theorem cell22_1794716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 3, 4].length) (baseStart_1794716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1794716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1794716 prefixEnd_1794716 := by exact prefixLift 1794716
  have htrace : WordTrace (prefixWord ++ tailWord_1794716) baseStart_1794716 baseEnd_1794716 := by
    simpa [prefixWord, tailWord_1794716, baseEnd_1794716] using wordTrace_append hprefix tailTrace_1794716
  have hstable : (prefixWord ++ tailWord_1794716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794716).length < 2 ^ (prefixWord ++ tailWord_1794716).sum := by decide
  have hdescent : baseEnd_1794716 < baseStart_1794716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794733 : List Nat := [1, 5, 2, 1, 1, 3, 3, 2, 4]
def baseStart_1794733 : Nat := 118140960795 + 1794733 * 2 ^ 59
def prefixEnd_1794733 : Nat := 4983230072969 + 3 ^ 40 * 1794733 * 2
def baseEnd_1794733 : Nat := 204791261219073740574151

theorem tailTrace_1794733 : CollatzResearch.WordTrace tailWord_1794733 prefixEnd_1794733 204791261219073740574151 := by
  unfold tailWord_1794733
  simp only [CollatzResearch.WordTrace]
  refine ⟨65459290206996331838524853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43639526804664221225683235 65459290206996331838524853)
  ·
    refine ⟨6136808456905906109861705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65459290206996331838524853 6136808456905906109861705)
    ·
      refine ⟨4602606342679429582396279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6136808456905906109861705 4602606342679429582396279)
      ·
        refine ⟨6903909514019144373594419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4602606342679429582396279 6903909514019144373594419)
        ·
          refine ⟨10355864271028716560391629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6903909514019144373594419 10355864271028716560391629)
          ·
            refine ⟨3883449101635768710146861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10355864271028716560391629 3883449101635768710146861)
            ·
              refine ⟨1456293413113413266305073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3883449101635768710146861 1456293413113413266305073)
              ·
                refine ⟨1092220059835059949728805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1456293413113413266305073 1092220059835059949728805)
                ·
                  refine ⟨204791261219073740574151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1092220059835059949728805 204791261219073740574151)
                  ·
                    rfl

theorem cell22_1794733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_1794733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1794733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1794733 prefixEnd_1794733 := by exact prefixLift 1794733
  have htrace : WordTrace (prefixWord ++ tailWord_1794733) baseStart_1794733 baseEnd_1794733 := by
    simpa [prefixWord, tailWord_1794733, baseEnd_1794733] using wordTrace_append hprefix tailTrace_1794733
  have hstable : (prefixWord ++ tailWord_1794733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794733).length < 2 ^ (prefixWord ++ tailWord_1794733).sum := by decide
  have hdescent : baseEnd_1794733 < baseStart_1794733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794789 : List Nat := [1, 3, 1, 4, 1, 2, 1, 4, 5]
def baseStart_1794789 : Nat := 118140960795 + 1794789 * 2 ^ 59
def prefixEnd_1794789 : Nat := 4983230072969 + 3 ^ 40 * 1794789 * 2
def baseEnd_1794789 : Nat := 204797651200551914107427

theorem tailTrace_1794789 : CollatzResearch.WordTrace tailWord_1794789 prefixEnd_1794789 204797651200551914107427 := by
  unfold tailWord_1794789
  simp only [CollatzResearch.WordTrace]
  refine ⟨65461332694793453402563421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43640888463195635601708947 65461332694793453402563421)
  ·
    refine ⟨24547999760547545025961283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65461332694793453402563421 24547999760547545025961283)
    ·
      refine ⟨36821999640821317538941925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24547999760547545025961283 36821999640821317538941925)
      ·
        refine ⟨6904124932653997038551611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36821999640821317538941925 6904124932653997038551611)
        ·
          refine ⟨10356187398980995557827417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6904124932653997038551611 10356187398980995557827417)
          ·
            refine ⟨7767140549235746668370563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10356187398980995557827417 7767140549235746668370563)
            ·
              refine ⟨11650710823853620002555845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7767140549235746668370563 11650710823853620002555845)
              ·
                refine ⟨2184508279472553750479221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11650710823853620002555845 2184508279472553750479221)
                ·
                  refine ⟨204797651200551914107427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2184508279472553750479221 204797651200551914107427)
                  ·
                    rfl

theorem cell22_1794789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4, 5].length) (baseStart_1794789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1794789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1794789 prefixEnd_1794789 := by exact prefixLift 1794789
  have htrace : WordTrace (prefixWord ++ tailWord_1794789) baseStart_1794789 baseEnd_1794789 := by
    simpa [prefixWord, tailWord_1794789, baseEnd_1794789] using wordTrace_append hprefix tailTrace_1794789
  have hstable : (prefixWord ++ tailWord_1794789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794789).length < 2 ^ (prefixWord ++ tailWord_1794789).sum := by decide
  have hdescent : baseEnd_1794789 < baseStart_1794789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794793 : List Nat := [1, 2, 1, 1, 1, 2, 8, 2, 1, 3]
def baseStart_1794793 : Nat := 118140960795 + 1794793 * 2 ^ 59
def prefixEnd_1794793 : Nat := 4983230072969 + 3 ^ 40 * 1794793 * 2
def baseEnd_1794793 : Nat := 614394322883401065222269

theorem tailTrace_1794793 : CollatzResearch.WordTrace tailWord_1794793 prefixEnd_1794793 614394322883401065222269 := by
  unfold tailWord_1794793
  simp only [CollatzResearch.WordTrace]
  refine ⟨65461478586778962085709033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43640985724519308057139355 65461478586778962085709033)
  ·
    refine ⟨49096108940084221564281775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65461478586778962085709033 49096108940084221564281775)
    ·
      refine ⟨73644163410126332346422663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49096108940084221564281775 73644163410126332346422663)
      ·
        refine ⟨110466245115189498519633995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73644163410126332346422663 110466245115189498519633995)
        ·
          refine ⟨165699367672784247779450993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110466245115189498519633995 165699367672784247779450993)
          ·
            refine ⟨124274525754588185834588245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165699367672784247779450993 124274525754588185834588245)
            ·
              refine ⟨1456342098686580302749081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 124274525754588185834588245 1456342098686580302749081)
              ·
                refine ⟨1092256574014935227061811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1456342098686580302749081 1092256574014935227061811)
                ·
                  refine ⟨1638384861022402840592717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1092256574014935227061811 1638384861022402840592717)
                  ·
                    refine ⟨614394322883401065222269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1638384861022402840592717 614394322883401065222269)
                    ·
                      rfl

theorem cell22_1794793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 2, 1, 3].length) (baseStart_1794793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1794793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1794793 prefixEnd_1794793 := by exact prefixLift 1794793
  have htrace : WordTrace (prefixWord ++ tailWord_1794793) baseStart_1794793 baseEnd_1794793 := by
    simpa [prefixWord, tailWord_1794793, baseEnd_1794793] using wordTrace_append hprefix tailTrace_1794793
  have hstable : (prefixWord ++ tailWord_1794793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794793).length < 2 ^ (prefixWord ++ tailWord_1794793).sum := by decide
  have hdescent : baseEnd_1794793 < baseStart_1794793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794819 : List Nat := [1, 1, 1, 3, 2, 2, 1, 6, 1, 4]
def baseStart_1794819 : Nat := 118140960795 + 1794819 * 2 ^ 59
def prefixEnd_1794819 : Nat := 4983230072969 + 3 ^ 40 * 1794819 * 2
def baseEnd_1794819 : Nat := 614403223214745664072189

theorem tailTrace_1794819 : CollatzResearch.WordTrace tailWord_1794819 prefixEnd_1794819 614403223214745664072189 := by
  unfold tailWord_1794819
  simp only [CollatzResearch.WordTrace]
  refine ⟨65462426884684768526155511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43641617923123179017437007 65462426884684768526155511)
  ·
    refine ⟨98193640327027152789233267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65462426884684768526155511 98193640327027152789233267)
    ·
      refine ⟨147290460490540729183849901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98193640327027152789233267 147290460490540729183849901)
      ·
        refine ⟨55233922683952773443943713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147290460490540729183849901 55233922683952773443943713)
        ·
          refine ⟨41425442012964580082957785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55233922683952773443943713 41425442012964580082957785)
          ·
            refine ⟨31069081509723435062218339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41425442012964580082957785 31069081509723435062218339)
            ·
              refine ⟨46603622264585152593327509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31069081509723435062218339 46603622264585152593327509)
              ·
                refine ⟨2184544793652429027812227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46603622264585152593327509 2184544793652429027812227)
                ·
                  refine ⟨3276817190478643541718341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2184544793652429027812227 3276817190478643541718341)
                  ·
                    refine ⟨614403223214745664072189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3276817190478643541718341 614403223214745664072189)
                    ·
                      rfl

theorem cell22_1794819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6, 1, 4].length) (baseStart_1794819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1794819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1794819 prefixEnd_1794819 := by exact prefixLift 1794819
  have htrace : WordTrace (prefixWord ++ tailWord_1794819) baseStart_1794819 baseEnd_1794819 := by
    simpa [prefixWord, tailWord_1794819, baseEnd_1794819] using wordTrace_append hprefix tailTrace_1794819
  have hstable : (prefixWord ++ tailWord_1794819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794819).length < 2 ^ (prefixWord ++ tailWord_1794819).sum := by decide
  have hdescent : baseEnd_1794819 < baseStart_1794819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794870 : List Nat := [5, 1, 2, 2, 2, 1, 2, 2, 1, 4]
def baseStart_1794870 : Nat := 118140960795 + 1794870 * 2 ^ 59
def prefixEnd_1794870 : Nat := 4983230072969 + 3 ^ 40 * 1794870 * 2
def baseEnd_1794870 : Nat := 614420681556998531047033

theorem tailTrace_1794870 : CollatzResearch.WordTrace tailWord_1794870 prefixEnd_1794870 614420681556998531047033 := by
  unfold tailWord_1794870
  simp only [CollatzResearch.WordTrace]
  refine ⟨4091517937968750264766379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43642858005000002824174709 4091517937968750264766379)
  ·
    refine ⟨6137276906953125397149569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4091517937968750264766379 6137276906953125397149569)
    ·
      refine ⟨4602957680214844047862177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6137276906953125397149569 4602957680214844047862177)
      ·
        refine ⟨3452218260161133035896633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4602957680214844047862177 3452218260161133035896633)
        ·
          refine ⟨2589163695120849776922475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3452218260161133035896633 2589163695120849776922475)
          ·
            refine ⟨3883745542681274665383713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2589163695120849776922475 3883745542681274665383713)
            ·
              refine ⟨2912809157010955999037785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3883745542681274665383713 2912809157010955999037785)
              ·
                refine ⟨2184606867758216999278339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2912809157010955999037785 2184606867758216999278339)
                ·
                  refine ⟨3276910301637325498917509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2184606867758216999278339 3276910301637325498917509)
                  ·
                    refine ⟨614420681556998531047033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3276910301637325498917509 614420681556998531047033)
                    ·
                      rfl

theorem cell22_1794870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_1794870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1794870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1794870 prefixEnd_1794870 := by exact prefixLift 1794870
  have htrace : WordTrace (prefixWord ++ tailWord_1794870) baseStart_1794870 baseEnd_1794870 := by
    simpa [prefixWord, tailWord_1794870, baseEnd_1794870] using wordTrace_append hprefix tailTrace_1794870
  have hstable : (prefixWord ++ tailWord_1794870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794870).length < 2 ^ (prefixWord ++ tailWord_1794870).sum := by decide
  have hdescent : baseEnd_1794870 < baseStart_1794870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794879 : List Nat := [1, 1, 2, 2, 5, 2, 1, 8]
def baseStart_1794879 : Nat := 118140960795 + 1794879 * 2 ^ 59
def prefixEnd_1794879 : Nat := 4983230072969 + 3 ^ 40 * 1794879 * 2
def baseEnd_1794879 : Nat := 68269306937880611952445

theorem tailTrace_1794879 : CollatzResearch.WordTrace tailWord_1794879 prefixEnd_1794879 68269306937880611952445 := by
  unfold tailWord_1794879
  simp only [CollatzResearch.WordTrace]
  refine ⟨65464615264467398773339691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43643076842978265848893127 65464615264467398773339691)
  ·
    refine ⟨98196922896701098160009537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65464615264467398773339691 98196922896701098160009537)
    ·
      refine ⟨73647692172525823620007153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98196922896701098160009537 73647692172525823620007153)
      ·
        refine ⟨55235769129394367715005365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73647692172525823620007153 55235769129394367715005365)
        ·
          refine ⟨5178353355880721973281753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55235769129394367715005365 5178353355880721973281753)
          ·
            refine ⟨3883765016910541479961315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5178353355880721973281753 3883765016910541479961315)
            ·
              refine ⟨5825647525365812219941973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3883765016910541479961315 5825647525365812219941973)
              ·
                refine ⟨68269306937880611952445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5825647525365812219941973 68269306937880611952445)
                ·
                  rfl

theorem cell22_1794879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 8].length) (baseStart_1794879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1794879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1794879 prefixEnd_1794879 := by exact prefixLift 1794879
  have htrace : WordTrace (prefixWord ++ tailWord_1794879) baseStart_1794879 baseEnd_1794879 := by
    simpa [prefixWord, tailWord_1794879, baseEnd_1794879] using wordTrace_append hprefix tailTrace_1794879
  have hstable : (prefixWord ++ tailWord_1794879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794879).length < 2 ^ (prefixWord ++ tailWord_1794879).sum := by decide
  have hdescent : baseEnd_1794879 < baseStart_1794879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794962 : List Nat := [3, 2, 3, 2, 2, 1, 1, 4, 1, 3]
def baseStart_1794962 : Nat := 118140960795 + 1794962 * 2 ^ 59
def prefixEnd_1794962 : Nat := 4983230072969 + 3 ^ 40 * 1794962 * 2
def baseEnd_1794962 : Nat := 614452175037140957746751

theorem tailTrace_1794962 : CollatzResearch.WordTrace tailWord_1794962 prefixEnd_1794962 614452175037140957746751 := by
  unfold tailWord_1794962
  simp only [CollatzResearch.WordTrace]
  refine ⟨16366910630791675987152785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43645095015444469299074093 16366910630791675987152785)
  ·
    refine ⟨12275182973093756990364589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16366910630791675987152785 12275182973093756990364589)
    ·
      refine ⟨4603193614910158871386721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12275182973093756990364589 4603193614910158871386721)
      ·
        refine ⟨3452395211182619153540041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4603193614910158871386721 3452395211182619153540041)
        ·
          refine ⟨2589296408386964365155031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3452395211182619153540041 2589296408386964365155031)
          ·
            refine ⟨3883944612580446547732547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2589296408386964365155031 3883944612580446547732547)
            ·
              refine ⟨5825916918870669821598821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3883944612580446547732547 5825916918870669821598821)
              ·
                refine ⟨1092359422288250591549779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5825916918870669821598821 1092359422288250591549779)
                ·
                  refine ⟨1638539133432375887324669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1092359422288250591549779 1638539133432375887324669)
                  ·
                    refine ⟨614452175037140957746751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1638539133432375887324669 614452175037140957746751)
                    ·
                      rfl

theorem cell22_1794962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_1794962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1794962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1794962 prefixEnd_1794962 := by exact prefixLift 1794962
  have htrace : WordTrace (prefixWord ++ tailWord_1794962) baseStart_1794962 baseEnd_1794962 := by
    simpa [prefixWord, tailWord_1794962, baseEnd_1794962] using wordTrace_append hprefix tailTrace_1794962
  have hstable : (prefixWord ++ tailWord_1794962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794962).length < 2 ^ (prefixWord ++ tailWord_1794962).sum := by decide
  have hdescent : baseEnd_1794962 < baseStart_1794962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794969 : List Nat := [1, 2, 1, 2, 1, 3, 1, 5, 6]
def baseStart_1794969 : Nat := 118140960795 + 1794969 * 2 ^ 59
def prefixEnd_1794969 : Nat := 4983230072969 + 3 ^ 40 * 1794969 * 2
def baseEnd_1794969 : Nat := 204818190426731757607243

theorem tailTrace_1794969 : CollatzResearch.WordTrace tailWord_1794969 prefixEnd_1794969 204818190426731757607243 := by
  unfold tailWord_1794969
  simp only [CollatzResearch.WordTrace]
  refine ⟨65467897834141344144115961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43645265222760896096077307 65467897834141344144115961)
  ·
    refine ⟨49100923375606008108086971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65467897834141344144115961 49100923375606008108086971)
    ·
      refine ⟨73651385063409012162130457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49100923375606008108086971 73651385063409012162130457)
      ·
        refine ⟨55238538797556759121597843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73651385063409012162130457 55238538797556759121597843)
        ·
          refine ⟨82857808196335138682396765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55238538797556759121597843 82857808196335138682396765)
          ·
            refine ⟨31071678073625677005898787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82857808196335138682396765 31071678073625677005898787)
            ·
              refine ⟨46607517110438515508848181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31071678073625677005898787 46607517110438515508848181)
              ·
                refine ⟨4369454729103610828954517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46607517110438515508848181 4369454729103610828954517)
                ·
                  refine ⟨204818190426731757607243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4369454729103610828954517 204818190426731757607243)
                  ·
                    rfl

theorem cell22_1794969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 6].length) (baseStart_1794969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1794969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1794969 prefixEnd_1794969 := by exact prefixLift 1794969
  have htrace : WordTrace (prefixWord ++ tailWord_1794969) baseStart_1794969 baseEnd_1794969 := by
    simpa [prefixWord, tailWord_1794969, baseEnd_1794969] using wordTrace_append hprefix tailTrace_1794969
  have hstable : (prefixWord ++ tailWord_1794969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794969).length < 2 ^ (prefixWord ++ tailWord_1794969).sum := by decide
  have hdescent : baseEnd_1794969 < baseStart_1794969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795001 : List Nat := [1, 2, 1, 4, 2, 2, 2, 2, 1, 5]
def baseStart_1795001 : Nat := 118140960795 + 1795001 * 2 ^ 59
def prefixEnd_1795001 : Nat := 4983230072969 + 3 ^ 40 * 1795001 * 2
def baseEnd_1795001 : Nat := 614465525534157856021631

theorem tailTrace_1795001 : CollatzResearch.WordTrace tailWord_1795001 prefixEnd_1795001 614465525534157856021631 := by
  unfold tailWord_1795001
  simp only [CollatzResearch.WordTrace]
  refine ⟨65469064970025413609280857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43646043313350275739520571 65469064970025413609280857)
  ·
    refine ⟨49101798727519060206960643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65469064970025413609280857 49101798727519060206960643)
    ·
      refine ⟨73652698091278590310440965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49101798727519060206960643 73652698091278590310440965)
      ·
        refine ⟨13809880892114735683207681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73652698091278590310440965 13809880892114735683207681)
        ·
          refine ⟨10357410669086051762405761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13809880892114735683207681 10357410669086051762405761)
          ·
            refine ⟨7768058001814538821804321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10357410669086051762405761 7768058001814538821804321)
            ·
              refine ⟨5826043501360904116353241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7768058001814538821804321 5826043501360904116353241)
              ·
                refine ⟨4369532626020678087264931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5826043501360904116353241 4369532626020678087264931)
                ·
                  refine ⟨6554298939031017130897397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4369532626020678087264931 6554298939031017130897397)
                  ·
                    refine ⟨614465525534157856021631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6554298939031017130897397 614465525534157856021631)
                    ·
                      rfl

theorem cell22_1795001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 5].length) (baseStart_1795001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1795001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1795001 prefixEnd_1795001 := by exact prefixLift 1795001
  have htrace : WordTrace (prefixWord ++ tailWord_1795001) baseStart_1795001 baseEnd_1795001 := by
    simpa [prefixWord, tailWord_1795001, baseEnd_1795001] using wordTrace_append hprefix tailTrace_1795001
  have hstable : (prefixWord ++ tailWord_1795001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795001).length < 2 ^ (prefixWord ++ tailWord_1795001).sum := by decide
  have hdescent : baseEnd_1795001 < baseStart_1795001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795080 : List Nat := [2, 1, 3, 2, 1, 5, 1, 1, 3, 3]
def baseStart_1795080 : Nat := 118140960795 + 1795080 * 2 ^ 59
def prefixEnd_1795080 : Nat := 4983230072969 + 3 ^ 40 * 1795080 * 2
def baseEnd_1795080 : Nat := 614492568848627983296389

theorem tailTrace_1795080 : CollatzResearch.WordTrace tailWord_1795080 prefixEnd_1795080 614492568848627983296389 := by
  unfold tailWord_1795080
  simp only [CollatzResearch.WordTrace]
  refine ⟨32735973168369605050703347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43647964224492806734271129 32735973168369605050703347)
  ·
    refine ⟨49103959752554407576055021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32735973168369605050703347 49103959752554407576055021)
    ·
      refine ⟨18413984907207902841020633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49103959752554407576055021 18413984907207902841020633)
      ·
        refine ⟨13810488680405927130765475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18413984907207902841020633 13810488680405927130765475)
        ·
          refine ⟨20715733020608890696148213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13810488680405927130765475 20715733020608890696148213)
          ·
            refine ⟨1942099970682083502763895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20715733020608890696148213 1942099970682083502763895)
            ·
              refine ⟨2913149956023125254145843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1942099970682083502763895 2913149956023125254145843)
              ·
                refine ⟨4369724934034687881218765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2913149956023125254145843 4369724934034687881218765)
                ·
                  refine ⟨1638646850263007955457037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4369724934034687881218765 1638646850263007955457037)
                  ·
                    refine ⟨614492568848627983296389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1638646850263007955457037 614492568848627983296389)
                    ·
                      rfl

theorem cell22_1795080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 3, 3].length) (baseStart_1795080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1795080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1795080 prefixEnd_1795080 := by exact prefixLift 1795080
  have htrace : WordTrace (prefixWord ++ tailWord_1795080) baseStart_1795080 baseEnd_1795080 := by
    simpa [prefixWord, tailWord_1795080, baseEnd_1795080] using wordTrace_append hprefix tailTrace_1795080
  have hstable : (prefixWord ++ tailWord_1795080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795080).length < 2 ^ (prefixWord ++ tailWord_1795080).sum := by decide
  have hdescent : baseEnd_1795080 < baseStart_1795080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795093 : List Nat := [1, 3, 2, 1, 4, 2, 1, 3, 5]
def baseStart_1795093 : Nat := 118140960795 + 1795093 * 2 ^ 59
def prefixEnd_1795093 : Nat := 4983230072969 + 3 ^ 40 * 1795093 * 2
def baseEnd_1795093 : Nat := 204832339671433427573783

theorem tailTrace_1795093 : CollatzResearch.WordTrace tailWord_1795093 prefixEnd_1795093 204832339671433427573783 := by
  unfold tailWord_1795093
  simp only [CollatzResearch.WordTrace]
  refine ⟨65472420485692113321629933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43648280323794742214419955 65472420485692113321629933)
  ·
    refine ⟨24552157682134542495611225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65472420485692113321629933 24552157682134542495611225)
    ·
      refine ⟨18414118261600906871708419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24552157682134542495611225 18414118261600906871708419)
      ·
        refine ⟨27621177392401360307562629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18414118261600906871708419 27621177392401360307562629)
        ·
          refine ⟨5178970761075255057667993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27621177392401360307562629 5178970761075255057667993)
          ·
            refine ⟨3884228070806441293250995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5178970761075255057667993 3884228070806441293250995)
            ·
              refine ⟨5826342106209661939876493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3884228070806441293250995 5826342106209661939876493)
              ·
                refine ⟨2184878289828623227453685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5826342106209661939876493 2184878289828623227453685)
                ·
                  refine ⟨204832339671433427573783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2184878289828623227453685 204832339671433427573783)
                  ·
                    rfl

theorem cell22_1795093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3, 5].length) (baseStart_1795093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1795093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1795093 prefixEnd_1795093 := by exact prefixLift 1795093
  have htrace : WordTrace (prefixWord ++ tailWord_1795093) baseStart_1795093 baseEnd_1795093 := by
    simpa [prefixWord, tailWord_1795093, baseEnd_1795093] using wordTrace_append hprefix tailTrace_1795093
  have hstable : (prefixWord ++ tailWord_1795093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795093).length < 2 ^ (prefixWord ++ tailWord_1795093).sum := by decide
  have hdescent : baseEnd_1795093 < baseStart_1795093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795136 : List Nat := [2, 1, 1, 2, 2, 3, 1, 2, 3, 5]
def baseStart_1795136 : Nat := 118140960795 + 1795136 * 2 ^ 59
def prefixEnd_1795136 : Nat := 4983230072969 + 3 ^ 40 * 1795136 * 2
def baseEnd_1795136 : Nat := 614511738793062503896217

theorem tailTrace_1795136 : CollatzResearch.WordTrace tailWord_1795136 prefixEnd_1795136 614511738793062503896217 := by
  unfold tailWord_1795136
  simp only [CollatzResearch.WordTrace]
  refine ⟨32736994412268165832722631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43649325883024221110296841 32736994412268165832722631)
  ·
    refine ⟨49105491618402248749083947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32736994412268165832722631 49105491618402248749083947)
    ·
      refine ⟨73658237427603373123625921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49105491618402248749083947 73658237427603373123625921)
      ·
        refine ⟨55243678070702529842719441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73658237427603373123625921 55243678070702529842719441)
        ·
          refine ⟨41432758553026897382039581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55243678070702529842719441 41432758553026897382039581)
          ·
            refine ⟨15537284457385086518264843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41432758553026897382039581 15537284457385086518264843)
            ·
              refine ⟨23305926686077629777397265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15537284457385086518264843 23305926686077629777397265)
              ·
                refine ⟨17479445014558222333047949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23305926686077629777397265 17479445014558222333047949)
                ·
                  refine ⟨6554791880459333374892981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17479445014558222333047949 6554791880459333374892981)
                  ·
                    refine ⟨614511738793062503896217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6554791880459333374892981 614511738793062503896217)
                    ·
                      rfl

theorem cell22_1795136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 3, 5].length) (baseStart_1795136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1795136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1795136 prefixEnd_1795136 := by exact prefixLift 1795136
  have htrace : WordTrace (prefixWord ++ tailWord_1795136) baseStart_1795136 baseEnd_1795136 := by
    simpa [prefixWord, tailWord_1795136, baseEnd_1795136] using wordTrace_append hprefix tailTrace_1795136
  have hstable : (prefixWord ++ tailWord_1795136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795136).length < 2 ^ (prefixWord ++ tailWord_1795136).sum := by decide
  have hdescent : baseEnd_1795136 < baseStart_1795136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795170 : List Nat := [3, 3, 2, 2, 1, 1, 2, 2, 1, 5]
def baseStart_1795170 : Nat := 118140960795 + 1795170 * 2 ^ 59
def prefixEnd_1795170 : Nat := 4983230072969 + 3 ^ 40 * 1795170 * 2
def baseEnd_1795170 : Nat := 614523377687897748546113

theorem tailTrace_1795170 : CollatzResearch.WordTrace tailWord_1795170 prefixEnd_1795170 614523377687897748546113 := by
  unfold tailWord_1795170
  simp only [CollatzResearch.WordTrace]
  refine ⟨16368807226603288868045741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43650152604275436981455309 16368807226603288868045741)
  ·
    refine ⟨6138302709976233325517153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16368807226603288868045741 6138302709976233325517153)
    ·
      refine ⟨4603727032482174994137865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6138302709976233325517153 4603727032482174994137865)
      ·
        refine ⟨3452795274361631245603399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4603727032482174994137865 3452795274361631245603399)
        ·
          refine ⟨5179192911542446868405099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3452795274361631245603399 5179192911542446868405099)
          ·
            refine ⟨7768789367313670302607649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5179192911542446868405099 7768789367313670302607649)
            ·
              refine ⟨5826592025485252726955737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7768789367313670302607649 5826592025485252726955737)
              ·
                refine ⟨4369944019113939545216803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5826592025485252726955737 4369944019113939545216803)
                ·
                  refine ⟨6554916028670909317825205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4369944019113939545216803 6554916028670909317825205)
                  ·
                    refine ⟨614523377687897748546113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6554916028670909317825205 614523377687897748546113)
                    ·
                      rfl

theorem cell22_1795170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_1795170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1795170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1795170 prefixEnd_1795170 := by exact prefixLift 1795170
  have htrace : WordTrace (prefixWord ++ tailWord_1795170) baseStart_1795170 baseEnd_1795170 := by
    simpa [prefixWord, tailWord_1795170, baseEnd_1795170] using wordTrace_append hprefix tailTrace_1795170
  have hstable : (prefixWord ++ tailWord_1795170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795170).length < 2 ^ (prefixWord ++ tailWord_1795170).sum := by decide
  have hdescent : baseEnd_1795170 < baseStart_1795170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795228 : List Nat := [2, 2, 3, 2, 1, 2, 1, 2, 7]
def baseStart_1795228 : Nat := 118140960795 + 1795228 * 2 ^ 59
def prefixEnd_1795228 : Nat := 4983230072969 + 3 ^ 40 * 1795228 * 2
def baseEnd_1795228 : Nat := 204847744091068310198645

theorem tailTrace_1795228 : CollatzResearch.WordTrace tailWord_1795228 prefixEnd_1795228 204847744091068310198645 := by
  unfold tailWord_1795228
  simp only [CollatzResearch.WordTrace]
  refine ⟨32738672170101515688897169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43651562893468687585196225 32738672170101515688897169)
  ·
    refine ⟨24554004127576136766672877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32738672170101515688897169 24554004127576136766672877)
    ·
      refine ⟨9207751547841051287502329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24554004127576136766672877 9207751547841051287502329)
      ·
        refine ⟨6905813660880788465626747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9207751547841051287502329 6905813660880788465626747)
        ·
          refine ⟨10358720491321182698440121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6905813660880788465626747 10358720491321182698440121)
          ·
            refine ⟨7769040368490887023830091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10358720491321182698440121 7769040368490887023830091)
            ·
              refine ⟨11653560552736330535745137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7769040368490887023830091 11653560552736330535745137)
              ·
                refine ⟨8740170414552247901808853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11653560552736330535745137 8740170414552247901808853)
                ·
                  refine ⟨204847744091068310198645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8740170414552247901808853 204847744091068310198645)
                  ·
                    rfl

theorem cell22_1795228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 7].length) (baseStart_1795228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1795228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1795228 prefixEnd_1795228 := by exact prefixLift 1795228
  have htrace : WordTrace (prefixWord ++ tailWord_1795228) baseStart_1795228 baseEnd_1795228 := by
    simpa [prefixWord, tailWord_1795228, baseEnd_1795228] using wordTrace_append hprefix tailTrace_1795228
  have hstable : (prefixWord ++ tailWord_1795228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795228).length < 2 ^ (prefixWord ++ tailWord_1795228).sum := by decide
  have hdescent : baseEnd_1795228 < baseStart_1795228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795258 : List Nat := [3, 1, 1, 1, 2, 2, 1, 4, 3, 4]
def baseStart_1795258 : Nat := 118140960795 + 1795258 * 2 ^ 59
def prefixEnd_1795258 : Nat := 4983230072969 + 3 ^ 40 * 1795258 * 2
def baseEnd_1795258 : Nat := 614553501886294852345843

theorem tailTrace_1795258 : CollatzResearch.WordTrace tailWord_1795258 prefixEnd_1795258 614553501886294852345843 := by
  unfold tailWord_1795258
  simp only [CollatzResearch.WordTrace]
  refine ⟨16369609632523586625346607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43652292353396231000924285 16369609632523586625346607)
  ·
    refine ⟨24554414448785379938019911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16369609632523586625346607 24554414448785379938019911)
    ·
      refine ⟨36831621673178069907029867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24554414448785379938019911 36831621673178069907029867)
      ·
        refine ⟨55247432509767104860544801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36831621673178069907029867 55247432509767104860544801)
        ·
          refine ⟨41435574382325328645408601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55247432509767104860544801 41435574382325328645408601)
          ·
            refine ⟨31076680786743996484056451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41435574382325328645408601 31076680786743996484056451)
            ·
              refine ⟨46615021180115994726084677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31076680786743996484056451 46615021180115994726084677)
              ·
                refine ⟨8740316471271749011140877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46615021180115994726084677 8740316471271749011140877)
                ·
                  refine ⟨3277618676726905879177829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8740316471271749011140877 3277618676726905879177829)
                  ·
                    refine ⟨614553501886294852345843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3277618676726905879177829 614553501886294852345843)
                    ·
                      rfl

theorem cell22_1795258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 3, 4].length) (baseStart_1795258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1795258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1795258 prefixEnd_1795258 := by exact prefixLift 1795258
  have htrace : WordTrace (prefixWord ++ tailWord_1795258) baseStart_1795258 baseEnd_1795258 := by
    simpa [prefixWord, tailWord_1795258, baseEnd_1795258] using wordTrace_append hprefix tailTrace_1795258
  have hstable : (prefixWord ++ tailWord_1795258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795258).length < 2 ^ (prefixWord ++ tailWord_1795258).sum := by decide
  have hdescent : baseEnd_1795258 < baseStart_1795258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795262 : List Nat := [4, 2, 1, 1, 3, 1, 4, 1, 5]
def baseStart_1795262 : Nat := 118140960795 + 1795262 * 2 ^ 59
def prefixEnd_1795262 : Nat := 4983230072969 + 3 ^ 40 * 1795262 * 2
def baseEnd_1795262 : Nat := 204851623722680058415277

theorem tailTrace_1795262 : CollatzResearch.WordTrace tailWord_1795262 prefixEnd_1795262 204851623722680058415277 := by
  unfold tailWord_1795262
  simp only [CollatzResearch.WordTrace]
  refine ⟨8184823052759981898066505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43652389614719903456354693 8184823052759981898066505)
  ·
    refine ⟨6138617289569986423549879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8184823052759981898066505 6138617289569986423549879)
    ·
      refine ⟨9207925934354979635324819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6138617289569986423549879 9207925934354979635324819)
      ·
        refine ⟨13811888901532469452987229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9207925934354979635324819 13811888901532469452987229)
        ·
          refine ⟨5179458338074676044870211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13811888901532469452987229 5179458338074676044870211)
          ·
            refine ⟨7769187507112014067305317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5179458338074676044870211 7769187507112014067305317)
            ·
              refine ⟨1456722657583502637619747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7769187507112014067305317 1456722657583502637619747)
              ·
                refine ⟨2185083986375253956429621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1456722657583502637619747 2185083986375253956429621)
                ·
                  refine ⟨204851623722680058415277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2185083986375253956429621 204851623722680058415277)
                  ·
                    rfl

theorem cell22_1795262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_1795262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1795262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1795262 prefixEnd_1795262 := by exact prefixLift 1795262
  have htrace : WordTrace (prefixWord ++ tailWord_1795262) baseStart_1795262 baseEnd_1795262 := by
    simpa [prefixWord, tailWord_1795262, baseEnd_1795262] using wordTrace_append hprefix tailTrace_1795262
  have hstable : (prefixWord ++ tailWord_1795262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795262).length < 2 ^ (prefixWord ++ tailWord_1795262).sum := by decide
  have hdescent : baseEnd_1795262 < baseStart_1795262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795290 : List Nat := [3, 1, 1, 2, 2, 1, 1, 7, 4]
def baseStart_1795290 : Nat := 118140960795 + 1795290 * 2 ^ 59
def prefixEnd_1795290 : Nat := 4983230072969 + 3 ^ 40 * 1795290 * 2
def baseEnd_1795290 : Nat := 204854818713419145181915

theorem tailTrace_1795290 : CollatzResearch.WordTrace tailWord_1795290 prefixEnd_1795290 204854818713419145181915 := by
  unfold tailWord_1795290
  simp only [CollatzResearch.WordTrace]
  refine ⟨16369901416494603991637831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43653070443985610644367549 16369901416494603991637831)
  ·
    refine ⟨24554852124741905987456747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16369901416494603991637831 24554852124741905987456747)
    ·
      refine ⟨36832278187112858981185121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24554852124741905987456747 36832278187112858981185121)
      ·
        refine ⟨27624208640334644235888841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36832278187112858981185121 27624208640334644235888841)
        ·
          refine ⟨20718156480250983176916631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27624208640334644235888841 20718156480250983176916631)
          ·
            refine ⟨31077234720376474765374947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20718156480250983176916631 31077234720376474765374947)
            ·
              refine ⟨46615852080564712148062421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31077234720376474765374947 46615852080564712148062421)
              ·
                refine ⟨1092559033138235440970213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 46615852080564712148062421 1092559033138235440970213)
                ·
                  refine ⟨204854818713419145181915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1092559033138235440970213 204854818713419145181915)
                  ·
                    rfl

theorem cell22_1795290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 7, 4].length) (baseStart_1795290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1795290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1795290 prefixEnd_1795290 := by exact prefixLift 1795290
  have htrace : WordTrace (prefixWord ++ tailWord_1795290) baseStart_1795290 baseEnd_1795290 := by
    simpa [prefixWord, tailWord_1795290, baseEnd_1795290] using wordTrace_append hprefix tailTrace_1795290
  have hstable : (prefixWord ++ tailWord_1795290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795290).length < 2 ^ (prefixWord ++ tailWord_1795290).sum := by decide
  have hdescent : baseEnd_1795290 < baseStart_1795290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795307 : List Nat := [1, 1, 1, 1, 2, 6, 4, 2, 4]
def baseStart_1795307 : Nat := 118140960795 + 1795307 * 2 ^ 59
def prefixEnd_1795307 : Nat := 4983230072969 + 3 ^ 40 * 1795307 * 2
def baseEnd_1795307 : Nat := 204856758529225019290231

theorem tailTrace_1795307 : CollatzResearch.WordTrace tailWord_1795307 prefixEnd_1795307 204856758529225019290231 := by
  unfold tailWord_1795307
  simp only [CollatzResearch.WordTrace]
  refine ⟨65480225706916827869920175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43653483804611218579946783 65480225706916827869920175)
  ·
    refine ⟨98220338560375241804880263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65480225706916827869920175 98220338560375241804880263)
    ·
      refine ⟨147330507840562862707320395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98220338560375241804880263 147330507840562862707320395)
      ·
        refine ⟨220995761760844294060980593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147330507840562862707320395 220995761760844294060980593)
        ·
          refine ⟨165746821320633220545735445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220995761760844294060980593 165746821320633220545735445)
          ·
            refine ⟨7769382249404682213081349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 165746821320633220545735445 7769382249404682213081349)
            ·
              refine ⟨1456759171763377914952753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7769382249404682213081349 1456759171763377914952753)
              ·
                refine ⟨1092569378822533436214565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1456759171763377914952753 1092569378822533436214565)
                ·
                  refine ⟨204856758529225019290231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1092569378822533436214565 204856758529225019290231)
                  ·
                    rfl

theorem cell22_1795307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 2, 4].length) (baseStart_1795307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1795307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1795307 prefixEnd_1795307 := by exact prefixLift 1795307
  have htrace : WordTrace (prefixWord ++ tailWord_1795307) baseStart_1795307 baseEnd_1795307 := by
    simpa [prefixWord, tailWord_1795307, baseEnd_1795307] using wordTrace_append hprefix tailTrace_1795307
  have hstable : (prefixWord ++ tailWord_1795307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795307).length < 2 ^ (prefixWord ++ tailWord_1795307).sum := by decide
  have hdescent : baseEnd_1795307 < baseStart_1795307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795410 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 5, 4]
def baseStart_1795410 : Nat := 118140960795 + 1795410 * 2 ^ 59
def prefixEnd_1795410 : Nat := 4983230072969 + 3 ^ 40 * 1795410 * 2
def baseEnd_1795410 : Nat := 614605534592617122545377

theorem tailTrace_1795410 : CollatzResearch.WordTrace tailWord_1795410 prefixEnd_1795410 614605534592617122545377 := by
  unfold tailWord_1795410
  simp only [CollatzResearch.WordTrace]
  refine ⟨16370995606385919115229921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43655988283695784307279789 16370995606385919115229921)
  ·
    refine ⟨12278246704789439336422441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16370995606385919115229921 12278246704789439336422441)
    ·
      refine ⟨9208685028592079502316831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12278246704789439336422441 9208685028592079502316831)
      ·
        refine ⟨13813027542888119253475247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9208685028592079502316831 13813027542888119253475247)
        ·
          refine ⟨20719541314332178880212871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13813027542888119253475247 20719541314332178880212871)
          ·
            refine ⟨31079311971498268320319307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20719541314332178880212871 31079311971498268320319307)
            ·
              refine ⟨46618967957247402480478961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31079311971498268320319307 46618967957247402480478961)
              ·
                refine ⟨34964225967935551860359221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46618967957247402480478961 34964225967935551860359221)
                ·
                  refine ⟨3277896184493957986908677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34964225967935551860359221 3277896184493957986908677)
                  ·
                    refine ⟨614605534592617122545377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3277896184493957986908677 614605534592617122545377)
                    ·
                      rfl

theorem cell22_1795410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_1795410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1795410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1795410 prefixEnd_1795410 := by exact prefixLift 1795410
  have htrace : WordTrace (prefixWord ++ tailWord_1795410) baseStart_1795410 baseEnd_1795410 := by
    simpa [prefixWord, tailWord_1795410, baseEnd_1795410] using wordTrace_append hprefix tailTrace_1795410
  have hstable : (prefixWord ++ tailWord_1795410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795410).length < 2 ^ (prefixWord ++ tailWord_1795410).sum := by decide
  have hdescent : baseEnd_1795410 < baseStart_1795410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795431 : List Nat := [1, 1, 5, 1, 5, 1, 2, 1, 5]
def baseStart_1795431 : Nat := 118140960795 + 1795431 * 2 ^ 59
def prefixEnd_1795431 : Nat := 4983230072969 + 3 ^ 40 * 1795431 * 2
def baseEnd_1795431 : Nat := 204870907773926689256771

theorem tailTrace_1795431 : CollatzResearch.WordTrace tailWord_1795431 prefixEnd_1795431 204870907773926689256771 := by
  unfold tailWord_1795431
  simp only [CollatzResearch.WordTrace]
  refine ⟨65484748358467597047434147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43656498905645064698289431 65484748358467597047434147)
  ·
    refine ⟨98227122537701395571151221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65484748358467597047434147 98227122537701395571151221)
    ·
      refine ⟨9208792737909505834795427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98227122537701395571151221 9208792737909505834795427)
      ·
        refine ⟨13813189106864258752193141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9208792737909505834795427 13813189106864258752193141)
        ·
          refine ⟨1294986478768524258018107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13813189106864258752193141 1294986478768524258018107)
          ·
            refine ⟨1942479718152786387027161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1294986478768524258018107 1942479718152786387027161)
            ·
              refine ⟨1456859788614589790270371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1942479718152786387027161 1456859788614589790270371)
              ·
                refine ⟨2185289682921884685405557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1456859788614589790270371 2185289682921884685405557)
                ·
                  refine ⟨204870907773926689256771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2185289682921884685405557 204870907773926689256771)
                  ·
                    rfl

theorem cell22_1795431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 1, 5].length) (baseStart_1795431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1795431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1795431 prefixEnd_1795431 := by exact prefixLift 1795431
  have htrace : WordTrace (prefixWord ++ tailWord_1795431) baseStart_1795431 baseEnd_1795431 := by
    simpa [prefixWord, tailWord_1795431, baseEnd_1795431] using wordTrace_append hprefix tailTrace_1795431
  have hstable : (prefixWord ++ tailWord_1795431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795431).length < 2 ^ (prefixWord ++ tailWord_1795431).sum := by decide
  have hdescent : baseEnd_1795431 < baseStart_1795431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795440 : List Nat := [2, 1, 1, 1, 4, 2, 2, 3, 1, 5]
def baseStart_1795440 : Nat := 118140960795 + 1795440 * 2 ^ 59
def prefixEnd_1795440 : Nat := 4983230072969 + 3 ^ 40 * 1795440 * 2
def baseEnd_1795440 : Nat := 614615804205707044295285

theorem tailTrace_1795440 : CollatzResearch.WordTrace tailWord_1795440 prefixEnd_1795440 614615804205707044295285 := by
  unfold tailWord_1795440
  simp only [CollatzResearch.WordTrace]
  refine ⟨32742538307717495792255887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43656717743623327723007849 32742538307717495792255887)
  ·
    refine ⟨49113807461576243688383831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32742538307717495792255887 49113807461576243688383831)
    ·
      refine ⟨73670711192364365532575747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49113807461576243688383831 73670711192364365532575747)
      ·
        refine ⟨110506066788546548298863621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73670711192364365532575747 110506066788546548298863621)
        ·
          refine ⟨20719887522852477806036929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110506066788546548298863621 20719887522852477806036929)
          ·
            refine ⟨15539915642139358354527697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20719887522852477806036929 15539915642139358354527697)
            ·
              refine ⟨11654936731604518765895773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15539915642139358354527697 11654936731604518765895773)
              ·
                refine ⟨4370601274351694537210915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11654936731604518765895773 4370601274351694537210915)
                ·
                  refine ⟨6555901911527541805816373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4370601274351694537210915 6555901911527541805816373)
                  ·
                    refine ⟨614615804205707044295285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6555901911527541805816373 614615804205707044295285)
                    ·
                      rfl

theorem cell22_1795440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 1, 5].length) (baseStart_1795440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1795440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1795440 prefixEnd_1795440 := by exact prefixLift 1795440
  have htrace : WordTrace (prefixWord ++ tailWord_1795440) baseStart_1795440 baseEnd_1795440 := by
    simpa [prefixWord, tailWord_1795440, baseEnd_1795440] using wordTrace_append hprefix tailTrace_1795440
  have hstable : (prefixWord ++ tailWord_1795440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795440).length < 2 ^ (prefixWord ++ tailWord_1795440).sum := by decide
  have hdescent : baseEnd_1795440 < baseStart_1795440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795470 : List Nat := [4, 1, 1, 4, 12]
def baseStart_1795470 : Nat := 118140960795 + 1795470 * 2 ^ 59
def prefixEnd_1795470 : Nat := 4983230072969 + 3 ^ 40 * 1795470 * 2
def baseEnd_1795470 : Nat := 2529325406661715909651

theorem tailTrace_1795470 : CollatzResearch.WordTrace tailWord_1795470 prefixEnd_1795470 2529325406661715909651 := by
  unfold tailWord_1795470
  simp only [CollatzResearch.WordTrace]
  refine ⟨8185771350665788338512983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43657447203550871138735909 8185771350665788338512983)
  ·
    refine ⟨12278657025998682507769475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8185771350665788338512983 12278657025998682507769475)
    ·
      refine ⟨18417985538998023761654213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12278657025998682507769475 18417985538998023761654213)
      ·
        refine ⟨3453372288562129455310165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18417985538998023761654213 3453372288562129455310165)
        ·
          refine ⟨2529325406661715909651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3453372288562129455310165 2529325406661715909651)
          ·
            rfl

theorem cell22_1795470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 12].length) (baseStart_1795470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1795470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1795470 prefixEnd_1795470 := by exact prefixLift 1795470
  have htrace : WordTrace (prefixWord ++ tailWord_1795470) baseStart_1795470 baseEnd_1795470 := by
    simpa [prefixWord, tailWord_1795470, baseEnd_1795470] using wordTrace_append hprefix tailTrace_1795470
  have hstable : (prefixWord ++ tailWord_1795470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795470).length < 2 ^ (prefixWord ++ tailWord_1795470).sum := by decide
  have hdescent : baseEnd_1795470 < baseStart_1795470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795476 : List Nat := [2, 4, 2, 1, 2, 1, 4, 2, 4]
def baseStart_1795476 : Nat := 118140960795 + 1795476 * 2 ^ 59
def prefixEnd_1795476 : Nat := 4983230072969 + 3 ^ 40 * 1795476 * 2
def baseEnd_1795476 : Nat := 204876042580471650131725

theorem tailTrace_1795476 : CollatzResearch.WordTrace tailWord_1795476 prefixEnd_1795476 204876042580471650131725 := by
  unfold tailWord_1795476
  simp only [CollatzResearch.WordTrace]
  refine ⟨32743194821652284866411141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43657593095536379821881521 32743194821652284866411141)
  ·
    refine ⟨6139349029059803412452089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32743194821652284866411141 6139349029059803412452089)
    ·
      refine ⟨4604511771794852559339067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6139349029059803412452089 4604511771794852559339067)
      ·
        refine ⟨6906767657692278839008601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4604511771794852559339067 6906767657692278839008601)
        ·
          refine ⟨5180075743269209129256451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6906767657692278839008601 5180075743269209129256451)
          ·
            refine ⟨7770113614903813693884677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5180075743269209129256451 7770113614903813693884677)
            ·
              refine ⟨1456896302794465067603377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7770113614903813693884677 1456896302794465067603377)
              ·
                refine ⟨1092672227095848800702533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1456896302794465067603377 1092672227095848800702533)
                ·
                  refine ⟨204876042580471650131725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1092672227095848800702533 204876042580471650131725)
                  ·
                    rfl

theorem cell22_1795476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_1795476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1795476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1795476 prefixEnd_1795476 := by exact prefixLift 1795476
  have htrace : WordTrace (prefixWord ++ tailWord_1795476) baseStart_1795476 baseEnd_1795476 := by
    simpa [prefixWord, tailWord_1795476, baseEnd_1795476] using wordTrace_append hprefix tailTrace_1795476
  have hstable : (prefixWord ++ tailWord_1795476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795476).length < 2 ^ (prefixWord ++ tailWord_1795476).sum := by decide
  have hdescent : baseEnd_1795476 < baseStart_1795476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795487 : List Nat := [1, 1, 2, 5, 1, 4, 1, 7]
def baseStart_1795487 : Nat := 118140960795 + 1795487 * 2 ^ 59
def prefixEnd_1795487 : Nat := 4983230072969 + 3 ^ 40 * 1795487 * 2
def baseEnd_1795487 : Nat := 68292432585134954263349

theorem tailTrace_1795487 : CollatzResearch.WordTrace tailWord_1795487 prefixEnd_1795487 68292432585134954263349 := by
  unfold tailWord_1795487
  simp only [CollatzResearch.WordTrace]
  refine ⟨65486790846264718611472715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43657860564176479074315143 65486790846264718611472715)
  ·
    refine ⟨98230186269397077917209073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65486790846264718611472715 98230186269397077917209073)
    ·
      refine ⟨73672639702047808437906805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98230186269397077917209073 73672639702047808437906805)
      ·
        refine ⟨6906809972066982041053763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73672639702047808437906805 6906809972066982041053763)
        ·
          refine ⟨10360214958100473061580645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6906809972066982041053763 10360214958100473061580645)
          ·
            refine ⟨1942540304643838699046371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10360214958100473061580645 1942540304643838699046371)
            ·
              refine ⟨2913810456965758048569557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1942540304643838699046371 2913810456965758048569557)
              ·
                refine ⟨68292432585134954263349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2913810456965758048569557 68292432585134954263349)
                ·
                  rfl

theorem cell22_1795487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 7].length) (baseStart_1795487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1795487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1795487 prefixEnd_1795487 := by exact prefixLift 1795487
  have htrace : WordTrace (prefixWord ++ tailWord_1795487) baseStart_1795487 baseEnd_1795487 := by
    simpa [prefixWord, tailWord_1795487, baseEnd_1795487] using wordTrace_append hprefix tailTrace_1795487
  have hstable : (prefixWord ++ tailWord_1795487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795487).length < 2 ^ (prefixWord ++ tailWord_1795487).sum := by decide
  have hdescent : baseEnd_1795487 < baseStart_1795487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795532 : List Nat := [2, 2, 1, 4, 2, 2, 1, 1, 7]
def baseStart_1795532 : Nat := 118140960795 + 1795532 * 2 ^ 59
def prefixEnd_1795532 : Nat := 4983230072969 + 3 ^ 40 * 1795532 * 2
def baseEnd_1795532 : Nat := 204882432561949823665001

theorem tailTrace_1795532 : CollatzResearch.WordTrace tailWord_1795532 prefixEnd_1795532 204882432561949823665001 := by
  unfold tailWord_1795532
  simp only [CollatzResearch.WordTrace]
  refine ⟨32744216065550845648430425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43658954754067794197907233 32744216065550845648430425)
  ·
    refine ⟨24558162049163134236322819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32744216065550845648430425 24558162049163134236322819)
    ·
      refine ⟨36837243073744701354484229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24558162049163134236322819 36837243073744701354484229)
      ·
        refine ⟨6906983076327131503965793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36837243073744701354484229 6906983076327131503965793)
        ·
          refine ⟨5180237307245348627974345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6906983076327131503965793 5180237307245348627974345)
          ·
            refine ⟨3885177980434011470980759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5180237307245348627974345 3885177980434011470980759)
            ·
              refine ⟨5827766970651017206471139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3885177980434011470980759 5827766970651017206471139)
              ·
                refine ⟨8741650455976525809706709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5827766970651017206471139 8741650455976525809706709)
                ·
                  refine ⟨204882432561949823665001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8741650455976525809706709 204882432561949823665001)
                  ·
                    rfl

theorem cell22_1795532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 7].length) (baseStart_1795532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1795532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1795532 prefixEnd_1795532 := by exact prefixLift 1795532
  have htrace : WordTrace (prefixWord ++ tailWord_1795532) baseStart_1795532 baseEnd_1795532 := by
    simpa [prefixWord, tailWord_1795532, baseEnd_1795532] using wordTrace_append hprefix tailTrace_1795532
  have hstable : (prefixWord ++ tailWord_1795532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795532).length < 2 ^ (prefixWord ++ tailWord_1795532).sum := by decide
  have hdescent : baseEnd_1795532 < baseStart_1795532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795594 : List Nat := [3, 1, 2, 2, 2, 4, 1, 1, 6]
def baseStart_1795594 : Nat := 118140960795 + 1795594 * 2 ^ 59
def prefixEnd_1795594 : Nat := 4983230072969 + 3 ^ 40 * 1795594 * 2
def baseEnd_1795594 : Nat := 204889507184300658648271

theorem tailTrace_1795594 : CollatzResearch.WordTrace tailWord_1795594 prefixEnd_1795594 204889507184300658648271 := by
  unfold tailWord_1795594
  simp only [CollatzResearch.WordTrace]
  refine ⟨16372673364219268971404459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43660462304584717257078557 16372673364219268971404459)
  ·
    refine ⟨24559010046328903457106689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16372673364219268971404459 24559010046328903457106689)
    ·
      refine ⟨18419257534746677592830017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24559010046328903457106689 18419257534746677592830017)
      ·
        refine ⟨13814443151060008194622513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18419257534746677592830017 13814443151060008194622513)
        ·
          refine ⟨10360832363295006145966885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13814443151060008194622513 10360832363295006145966885)
          ·
            refine ⟨1942656068117813652368791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10360832363295006145966885 1942656068117813652368791)
            ·
              refine ⟨2913984102176720478553187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1942656068117813652368791 2913984102176720478553187)
              ·
                refine ⟨4370976153265080717829781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2913984102176720478553187 4370976153265080717829781)
                ·
                  refine ⟨204889507184300658648271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4370976153265080717829781 204889507184300658648271)
                  ·
                    rfl

theorem cell22_1795594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 6].length) (baseStart_1795594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1795594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1795594 prefixEnd_1795594 := by exact prefixLift 1795594
  have htrace : WordTrace (prefixWord ++ tailWord_1795594) baseStart_1795594 baseEnd_1795594 := by
    simpa [prefixWord, tailWord_1795594, baseEnd_1795594] using wordTrace_append hprefix tailTrace_1795594
  have hstable : (prefixWord ++ tailWord_1795594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795594).length < 2 ^ (prefixWord ++ tailWord_1795594).sum := by decide
  have hdescent : baseEnd_1795594 < baseStart_1795594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795645 : List Nat := [1, 4, 1, 3, 4, 1, 2, 2, 4]
def baseStart_1795645 : Nat := 118140960795 + 1795645 * 2 ^ 59
def prefixEnd_1795645 : Nat := 4983230072969 + 3 ^ 40 * 1795645 * 2
def baseEnd_1795645 : Nat := 204895326631718280973219

theorem tailTrace_1795645 : CollatzResearch.WordTrace tailWord_1795645 prefixEnd_1795645 204895326631718280973219 := by
  unfold tailWord_1795645
  simp only [CollatzResearch.WordTrace]
  refine ⟨65492553579692311595724389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43661702386461541063816259 65492553579692311595724389)
  ·
    refine ⟨12279853796192308424198323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65492553579692311595724389 12279853796192308424198323)
    ·
      refine ⟨18419780694288462636297485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12279853796192308424198323 18419780694288462636297485)
      ·
        refine ⟨6907417760358173488611557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18419780694288462636297485 6907417760358173488611557)
        ·
          refine ⟨1295140830067157529114667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6907417760358173488611557 1295140830067157529114667)
          ·
            refine ⟨1942711245100736293672001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1295140830067157529114667 1942711245100736293672001)
            ·
              refine ⟨1457033433825552220254001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1942711245100736293672001 1457033433825552220254001)
              ·
                refine ⟨1092775075369164165190501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1457033433825552220254001 1092775075369164165190501)
                ·
                  refine ⟨204895326631718280973219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1092775075369164165190501 204895326631718280973219)
                  ·
                    rfl

theorem cell22_1795645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 2, 4].length) (baseStart_1795645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1795645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1795645 prefixEnd_1795645 := by exact prefixLift 1795645
  have htrace : WordTrace (prefixWord ++ tailWord_1795645) baseStart_1795645 baseEnd_1795645 := by
    simpa [prefixWord, tailWord_1795645, baseEnd_1795645] using wordTrace_append hprefix tailTrace_1795645
  have hstable : (prefixWord ++ tailWord_1795645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795645).length < 2 ^ (prefixWord ++ tailWord_1795645).sum := by decide
  have hdescent : baseEnd_1795645 < baseStart_1795645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795688 : List Nat := [2, 1, 4, 3, 1, 1, 1, 5, 1, 3]
def baseStart_1795688 : Nat := 118140960795 + 1795688 * 2 ^ 59
def prefixEnd_1795688 : Nat := 4983230072969 + 3 ^ 40 * 1795688 * 2
def baseEnd_1795688 : Nat := 614700699673917064094525

theorem tailTrace_1795688 : CollatzResearch.WordTrace tailWord_1795688 prefixEnd_1795688 614700699673917064094525 := by
  unfold tailWord_1795688
  simp only [CollatzResearch.WordTrace]
  refine ⟨32747060959268264969769859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43662747945691019959693145 32747060959268264969769859)
  ·
    refine ⟨49120591438902397454654789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32747060959268264969769859 49120591438902397454654789)
    ·
      refine ⟨9210110894794199522747773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49120591438902397454654789 9210110894794199522747773)
      ·
        refine ⟨3453791585547824821030415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9210110894794199522747773 3453791585547824821030415)
        ·
          refine ⟨5180687378321737231545623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3453791585547824821030415 5180687378321737231545623)
          ·
            refine ⟨7771031067482605847318435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5180687378321737231545623 7771031067482605847318435)
            ·
              refine ⟨11656546601223908770977653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7771031067482605847318435 11656546601223908770977653)
              ·
                refine ⟨1092801243864741447279155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11656546601223908770977653 1092801243864741447279155)
                ·
                  refine ⟨1639201865797112170918733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1092801243864741447279155 1639201865797112170918733)
                  ·
                    refine ⟨614700699673917064094525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1639201865797112170918733 614700699673917064094525)
                    ·
                      rfl

theorem cell22_1795688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_1795688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1795688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1795688 prefixEnd_1795688 := by exact prefixLift 1795688
  have htrace : WordTrace (prefixWord ++ tailWord_1795688) baseStart_1795688 baseEnd_1795688 := by
    simpa [prefixWord, tailWord_1795688, baseEnd_1795688] using wordTrace_append hprefix tailTrace_1795688
  have hstable : (prefixWord ++ tailWord_1795688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795688).length < 2 ^ (prefixWord ++ tailWord_1795688).sum := by decide
  have hdescent : baseEnd_1795688 < baseStart_1795688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795701 : List Nat := [1, 3, 4, 2, 1, 1, 3, 2, 5]
def baseStart_1795701 : Nat := 118140960795 + 1795701 * 2 ^ 59
def prefixEnd_1795701 : Nat := 4983230072969 + 3 ^ 40 * 1795701 * 2
def baseEnd_1795701 : Nat := 204901716613196454506495

theorem tailTrace_1795701 : CollatzResearch.WordTrace tailWord_1795701 prefixEnd_1795701 204901716613196454506495 := by
  unfold tailWord_1795701
  simp only [CollatzResearch.WordTrace]
  refine ⟨65494596067489433159762957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43663064044992955439841971 65494596067489433159762957)
  ·
    refine ⟨24560473525308537434911109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65494596067489433159762957 24560473525308537434911109)
    ·
      refine ⟨4605088785995350769045833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24560473525308537434911109 4605088785995350769045833)
      ·
        refine ⟨3453816589496513076784375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4605088785995350769045833 3453816589496513076784375)
        ·
          refine ⟨5180724884244769615176563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3453816589496513076784375 5180724884244769615176563)
          ·
            refine ⟨7771087326367154422764845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5180724884244769615176563 7771087326367154422764845)
            ·
              refine ⟨2914157747387682908536817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7771087326367154422764845 2914157747387682908536817)
              ·
                refine ⟨2185618310540762181402613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2914157747387682908536817 2185618310540762181402613)
                ·
                  refine ⟨204901716613196454506495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2185618310540762181402613 204901716613196454506495)
                  ·
                    rfl

theorem cell22_1795701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2, 5].length) (baseStart_1795701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1795701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1795701 prefixEnd_1795701 := by exact prefixLift 1795701
  have htrace : WordTrace (prefixWord ++ tailWord_1795701) baseStart_1795701 baseEnd_1795701 := by
    simpa [prefixWord, tailWord_1795701, baseEnd_1795701] using wordTrace_append hprefix tailTrace_1795701
  have hstable : (prefixWord ++ tailWord_1795701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795701).length < 2 ^ (prefixWord ++ tailWord_1795701).sum := by decide
  have hdescent : baseEnd_1795701 < baseStart_1795701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795759 : List Nat := [1, 1, 2, 1, 2, 4, 3, 2, 2, 4]
def baseStart_1795759 : Nat := 118140960795 + 1795759 * 2 ^ 59
def prefixEnd_1795759 : Nat := 4983230072969 + 3 ^ 40 * 1795759 * 2
def baseEnd_1795759 : Nat := 614725004424896545569307

theorem tailTrace_1795759 : CollatzResearch.WordTrace tailWord_1795759 prefixEnd_1795759 614725004424896545569307 := by
  unfold tailWord_1795759
  simp only [CollatzResearch.WordTrace]
  refine ⟨65496711501279309065374331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43664474334186206043582887 65496711501279309065374331)
  ·
    refine ⟨98245067251918963598061497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65496711501279309065374331 98245067251918963598061497)
    ·
      refine ⟨73683800438939222698546123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98245067251918963598061497 73683800438939222698546123)
      ·
        refine ⟨110525700658408834047819185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73683800438939222698546123 110525700658408834047819185)
        ·
          refine ⟨82894275493806625535864389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110525700658408834047819185 82894275493806625535864389)
          ·
            refine ⟨15542676655088742287974573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82894275493806625535864389 15542676655088742287974573)
            ·
              refine ⟨5828503745658278357990465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15542676655088742287974573 5828503745658278357990465)
              ·
                refine ⟨4371377809243708768492849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5828503745658278357990465 4371377809243708768492849)
                ·
                  refine ⟨3278533356932781576369637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4371377809243708768492849 3278533356932781576369637)
                  ·
                    refine ⟨614725004424896545569307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3278533356932781576369637 614725004424896545569307)
                    ·
                      rfl

theorem cell22_1795759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2, 4].length) (baseStart_1795759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1795759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1795759 prefixEnd_1795759 := by exact prefixLift 1795759
  have htrace : WordTrace (prefixWord ++ tailWord_1795759) baseStart_1795759 baseEnd_1795759 := by
    simpa [prefixWord, tailWord_1795759, baseEnd_1795759] using wordTrace_append hprefix tailTrace_1795759
  have hstable : (prefixWord ++ tailWord_1795759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795759).length < 2 ^ (prefixWord ++ tailWord_1795759).sum := by decide
  have hdescent : baseEnd_1795759 < baseStart_1795759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795774 : List Nat := [4, 2, 1, 1, 2, 2, 1, 9]
def baseStart_1795774 : Nat := 118140960795 + 1795774 * 2 ^ 59
def prefixEnd_1795774 : Nat := 4983230072969 + 3 ^ 40 * 1795774 * 2
def baseEnd_1795774 : Nat := 68303348803493500716029

theorem tailTrace_1795774 : CollatzResearch.WordTrace tailWord_1795774 prefixEnd_1795774 68303348803493500716029 := by
  unfold tailWord_1795774
  simp only [CollatzResearch.WordTrace]
  refine ⟨8187157324528120828396297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43664839064149977751446917 8187157324528120828396297)
  ·
    refine ⟨6140367993396090621297223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8187157324528120828396297 6140367993396090621297223)
    ·
      refine ⟨9210551990094135931945835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6140367993396090621297223 9210551990094135931945835)
      ·
        refine ⟨13815827985141203897918753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9210551990094135931945835 13815827985141203897918753)
        ·
          refine ⟨10361870988855902923439065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13815827985141203897918753 10361870988855902923439065)
          ·
            refine ⟨7771403241641927192579299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10361870988855902923439065 7771403241641927192579299)
            ·
              refine ⟨11657104862462890788868949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7771403241641927192579299 11657104862462890788868949)
              ·
                refine ⟨68303348803493500716029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11657104862462890788868949 68303348803493500716029)
                ·
                  rfl

theorem cell22_1795774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 9].length) (baseStart_1795774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1795774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1795774 prefixEnd_1795774 := by exact prefixLift 1795774
  have htrace : WordTrace (prefixWord ++ tailWord_1795774) baseStart_1795774 baseEnd_1795774 := by
    simpa [prefixWord, tailWord_1795774, baseEnd_1795774] using wordTrace_append hprefix tailTrace_1795774
  have hstable : (prefixWord ++ tailWord_1795774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795774).length < 2 ^ (prefixWord ++ tailWord_1795774).sum := by decide
  have hdescent : baseEnd_1795774 < baseStart_1795774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795782 : List Nat := [6, 1, 2, 1, 1, 3, 1, 2, 1, 4]
def baseStart_1795782 : Nat := 118140960795 + 1795782 * 2 ^ 59
def prefixEnd_1795782 : Nat := 4983230072969 + 3 ^ 40 * 1795782 * 2
def baseEnd_1795782 : Nat := 614732877794932152244237

theorem tailTrace_1795782 : CollatzResearch.WordTrace tailWord_1795782 prefixEnd_1795782 614732877794932152244237 := by
  unfold tailWord_1795782
  simp only [CollatzResearch.WordTrace]
  refine ⟨2046798449381124499795675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43665033586797322662307733 2046798449381124499795675)
  ·
    refine ⟨3070197674071686749693513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2046798449381124499795675 3070197674071686749693513)
    ·
      refine ⟨2302648255553765062270135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3070197674071686749693513 2302648255553765062270135)
      ·
        refine ⟨3453972383330647593405203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2302648255553765062270135 3453972383330647593405203)
        ·
          refine ⟨5180958574995971390107805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3453972383330647593405203 5180958574995971390107805)
          ·
            refine ⟨1942859465623489271290427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5180958574995971390107805 1942859465623489271290427)
            ·
              refine ⟨2914289198435233906935641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1942859465623489271290427 2914289198435233906935641)
              ·
                refine ⟨2185716898826425430201731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2914289198435233906935641 2185716898826425430201731)
                ·
                  refine ⟨3278575348239638145302597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2185716898826425430201731 3278575348239638145302597)
                  ·
                    refine ⟨614732877794932152244237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3278575348239638145302597 614732877794932152244237)
                    ·
                      rfl

theorem cell22_1795782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_1795782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1795782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1795782 prefixEnd_1795782 := by exact prefixLift 1795782
  have htrace : WordTrace (prefixWord ++ tailWord_1795782) baseStart_1795782 baseEnd_1795782 := by
    simpa [prefixWord, tailWord_1795782, baseEnd_1795782] using wordTrace_append hprefix tailTrace_1795782
  have hstable : (prefixWord ++ tailWord_1795782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795782).length < 2 ^ (prefixWord ++ tailWord_1795782).sum := by decide
  have hdescent : baseEnd_1795782 < baseStart_1795782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795819 : List Nat := [1, 1, 1, 1, 2, 4, 3, 4, 5]
def baseStart_1795819 : Nat := 118140960795 + 1795819 * 2 ^ 59
def prefixEnd_1795819 : Nat := 4983230072969 + 3 ^ 40 * 1795819 * 2
def baseEnd_1795819 : Nat := 204915181217025463023041

theorem tailTrace_1795819 : CollatzResearch.WordTrace tailWord_1795819 prefixEnd_1795819 204915181217025463023041 := by
  unfold tailWord_1795819
  simp only [CollatzResearch.WordTrace]
  refine ⟨65498899881061939312558511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43665933254041292875039007 65498899881061939312558511)
  ·
    refine ⟨98248349821592908968837767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65498899881061939312558511 98248349821592908968837767)
    ·
      refine ⟨147372524732389363453256651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98248349821592908968837767 147372524732389363453256651)
      ·
        refine ⟨221058787098584045179884977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147372524732389363453256651 221058787098584045179884977)
        ·
          refine ⟨165794090323938033884913733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221058787098584045179884977 165794090323938033884913733)
          ·
            refine ⟨31086391935738381353421325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165794090323938033884913733 31086391935738381353421325)
            ·
              refine ⟨11657396975901893007532997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31086391935738381353421325 11657396975901893007532997)
              ·
                refine ⟨2185761932981604938912437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11657396975901893007532997 2185761932981604938912437)
                ·
                  refine ⟨204915181217025463023041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2185761932981604938912437 204915181217025463023041)
                  ·
                    rfl

theorem cell22_1795819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4, 5].length) (baseStart_1795819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1795819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1795819 prefixEnd_1795819 := by exact prefixLift 1795819
  have htrace : WordTrace (prefixWord ++ tailWord_1795819) baseStart_1795819 baseEnd_1795819 := by
    simpa [prefixWord, tailWord_1795819, baseEnd_1795819] using wordTrace_append hprefix tailTrace_1795819
  have hstable : (prefixWord ++ tailWord_1795819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795819).length < 2 ^ (prefixWord ++ tailWord_1795819).sum := by decide
  have hdescent : baseEnd_1795819 < baseStart_1795819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795823 : List Nat := [1, 1, 2, 1, 5, 1, 3, 4, 1, 3]
def baseStart_1795823 : Nat := 118140960795 + 1795823 * 2 ^ 59
def prefixEnd_1795823 : Nat := 4983230072969 + 3 ^ 40 * 1795823 * 2
def baseEnd_1795823 : Nat := 614746912932821711969111

theorem tailTrace_1795823 : CollatzResearch.WordTrace tailWord_1795823 prefixEnd_1795823 614746912932821711969111 := by
  unfold tailWord_1795823
  simp only [CollatzResearch.WordTrace]
  refine ⟨65499045773047447995704123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43666030515364965330469415 65499045773047447995704123)
  ·
    refine ⟨98248568659571171993556185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65499045773047447995704123 98248568659571171993556185)
    ·
      refine ⟨73686426494678378995167139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98248568659571171993556185 73686426494678378995167139)
      ·
        refine ⟨110529639742017568492750709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73686426494678378995167139 110529639742017568492750709)
        ·
          refine ⟨10362153725814147046195379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110529639742017568492750709 10362153725814147046195379)
          ·
            refine ⟨15543230588721220569293069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10362153725814147046195379 15543230588721220569293069)
            ·
              refine ⟨5828711470770457713484901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15543230588721220569293069 5828711470770457713484901)
              ·
                refine ⟨1092883400769460821278419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5828711470770457713484901 1092883400769460821278419)
                ·
                  refine ⟨1639325101154191231917629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1092883400769460821278419 1639325101154191231917629)
                  ·
                    refine ⟨614746912932821711969111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1639325101154191231917629 614746912932821711969111)
                    ·
                      rfl

theorem cell22_1795823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 4, 1, 3].length) (baseStart_1795823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1795823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1795823 prefixEnd_1795823 := by exact prefixLift 1795823
  have htrace : WordTrace (prefixWord ++ tailWord_1795823) baseStart_1795823 baseEnd_1795823 := by
    simpa [prefixWord, tailWord_1795823, baseEnd_1795823] using wordTrace_append hprefix tailTrace_1795823
  have hstable : (prefixWord ++ tailWord_1795823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795823).length < 2 ^ (prefixWord ++ tailWord_1795823).sum := by decide
  have hdescent : baseEnd_1795823 < baseStart_1795823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795870 : List Nat := [4, 3, 2, 2, 1, 1, 1, 1, 7]
def baseStart_1795870 : Nat := 118140960795 + 1795870 * 2 ^ 59
def prefixEnd_1795870 : Nat := 4983230072969 + 3 ^ 40 * 1795870 * 2
def baseEnd_1795870 : Nat := 204921000664443085347989

theorem tailTrace_1795870 : CollatzResearch.WordTrace tailWord_1795870 prefixEnd_1795870 204921000664443085347989 := by
  unfold tailWord_1795870
  simp only [CollatzResearch.WordTrace]
  refine ⟨8187595000484646877833133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43667173335918116681776709 8187595000484646877833133)
  ·
    refine ⟨3070348125181742579187425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8187595000484646877833133 3070348125181742579187425)
    ·
      refine ⟨2302761093886306934390569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3070348125181742579187425 2302761093886306934390569)
      ·
        refine ⟨1727070820414730200792927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2302761093886306934390569 1727070820414730200792927)
        ·
          refine ⟨2590606230622095301189391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1727070820414730200792927 2590606230622095301189391)
          ·
            refine ⟨3885909345933142951784087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2590606230622095301189391 3885909345933142951784087)
            ·
              refine ⟨5828864018899714427676131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3885909345933142951784087 5828864018899714427676131)
              ·
                refine ⟨8743296028349571641514197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5828864018899714427676131 8743296028349571641514197)
                ·
                  refine ⟨204921000664443085347989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8743296028349571641514197 204921000664443085347989)
                  ·
                    rfl

theorem cell22_1795870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_1795870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1795870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1795870 prefixEnd_1795870 := by exact prefixLift 1795870
  have htrace : WordTrace (prefixWord ++ tailWord_1795870) baseStart_1795870 baseEnd_1795870 := by
    simpa [prefixWord, tailWord_1795870, baseEnd_1795870] using wordTrace_append hprefix tailTrace_1795870
  have hstable : (prefixWord ++ tailWord_1795870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795870).length < 2 ^ (prefixWord ++ tailWord_1795870).sum := by decide
  have hdescent : baseEnd_1795870 < baseStart_1795870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795896 : List Nat := [2, 1, 2, 1, 3, 3, 3, 1, 1, 5]
def baseStart_1795896 : Nat := 118140960795 + 1795896 * 2 ^ 59
def prefixEnd_1795896 : Nat := 4983230072969 + 3 ^ 40 * 1795896 * 2
def baseEnd_1795896 : Nat := 614771902324673854893887

theorem tailTrace_1795896 : CollatzResearch.WordTrace tailWord_1795896 prefixEnd_1795896 614771902324673854893887 := by
  unfold tailWord_1795896
  simp only [CollatzResearch.WordTrace]
  refine ⟨32750854150891490731555771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43667805534521987642074361 32750854150891490731555771)
  ·
    refine ⟨49126281226337236097333657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32750854150891490731555771 49126281226337236097333657)
    ·
      refine ⟨36844710919752927073000243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49126281226337236097333657 36844710919752927073000243)
      ·
        refine ⟨55267066379629390609500365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36844710919752927073000243 55267066379629390609500365)
        ·
          refine ⟨20725149892361021478562637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55267066379629390609500365 20725149892361021478562637)
          ·
            refine ⟨7771931209635383054460989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20725149892361021478562637 7771931209635383054460989)
            ·
              refine ⟨2914474203613268645422871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7771931209635383054460989 2914474203613268645422871)
              ·
                refine ⟨4371711305419902968134307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2914474203613268645422871 4371711305419902968134307)
                ·
                  refine ⟨6557566958129854452201461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4371711305419902968134307 6557566958129854452201461)
                  ·
                    refine ⟨614771902324673854893887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6557566958129854452201461 614771902324673854893887)
                    ·
                      rfl

theorem cell22_1795896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 1, 5].length) (baseStart_1795896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1795896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1795896 prefixEnd_1795896 := by exact prefixLift 1795896
  have htrace : WordTrace (prefixWord ++ tailWord_1795896) baseStart_1795896 baseEnd_1795896 := by
    simpa [prefixWord, tailWord_1795896, baseEnd_1795896] using wordTrace_append hprefix tailTrace_1795896
  have hstable : (prefixWord ++ tailWord_1795896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795896).length < 2 ^ (prefixWord ++ tailWord_1795896).sum := by decide
  have hdescent : baseEnd_1795896 < baseStart_1795896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795909 : List Nat := [1, 3, 1, 1, 1, 2, 5, 8]
def baseStart_1795909 : Nat := 118140960795 + 1795909 * 2 ^ 59
def prefixEnd_1795909 : Nat := 4983230072969 + 3 ^ 40 * 1795909 * 2
def baseEnd_1795909 : Nat := 68308483610038461590983

theorem tailTrace_1795909 : CollatzResearch.WordTrace tailWord_1795909 prefixEnd_1795909 68308483610038461590983 := by
  unfold tailWord_1795909
  simp only [CollatzResearch.WordTrace]
  refine ⟨65502182450735884683334781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43668121633823923122223187 65502182450735884683334781)
  ·
    refine ⟨24563318419025956756250543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65502182450735884683334781 24563318419025956756250543)
    ·
      refine ⟨36844977628538935134375815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24563318419025956756250543 36844977628538935134375815)
      ·
        refine ⟨55267466442808402701563723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36844977628538935134375815 55267466442808402701563723)
        ·
          refine ⟨82901199664212604052345585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55267466442808402701563723 82901199664212604052345585)
          ·
            refine ⟨62175899748159453039259189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82901199664212604052345585 62175899748159453039259189)
            ·
              refine ⟨5828990601389948722430549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62175899748159453039259189 5828990601389948722430549)
              ·
                refine ⟨68308483610038461590983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5828990601389948722430549 68308483610038461590983)
                ·
                  rfl

theorem cell22_1795909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 8].length) (baseStart_1795909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1795909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1795909 prefixEnd_1795909 := by exact prefixLift 1795909
  have htrace : WordTrace (prefixWord ++ tailWord_1795909) baseStart_1795909 baseEnd_1795909 := by
    simpa [prefixWord, tailWord_1795909, baseEnd_1795909] using wordTrace_append hprefix tailTrace_1795909
  have hstable : (prefixWord ++ tailWord_1795909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795909).length < 2 ^ (prefixWord ++ tailWord_1795909).sum := by decide
  have hdescent : baseEnd_1795909 < baseStart_1795909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795932 : List Nat := [2, 2, 4, 2, 2, 1, 3, 2, 4]
def baseStart_1795932 : Nat := 118140960795 + 1795932 * 2 ^ 59
def prefixEnd_1795932 : Nat := 4983230072969 + 3 ^ 40 * 1795932 * 2
def baseEnd_1795932 : Nat := 204928075286793920331259

theorem tailTrace_1795932 : CollatzResearch.WordTrace tailWord_1795932 prefixEnd_1795932 204928075286793920331259 := by
  unfold tailWord_1795932
  simp only [CollatzResearch.WordTrace]
  refine ⟨32751510664826279805711025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43668680886435039740948033 32751510664826279805711025)
  ·
    refine ⟨24563632998619709854283269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32751510664826279805711025 24563632998619709854283269)
    ·
      refine ⟨4605681187241195597678113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24563632998619709854283269 4605681187241195597678113)
      ·
        refine ⟨3454260890430896698258585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4605681187241195597678113 3454260890430896698258585)
        ·
          refine ⟨2590695667823172523693939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3454260890430896698258585 2590695667823172523693939)
          ·
            refine ⟨3886043501734758785540909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2590695667823172523693939 3886043501734758785540909)
            ·
              refine ⟨1457266313150534544577841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3886043501734758785540909 1457266313150534544577841)
              ·
                refine ⟨1092949734862900908433381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1457266313150534544577841 1092949734862900908433381)
                ·
                  refine ⟨204928075286793920331259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1092949734862900908433381 204928075286793920331259)
                  ·
                    rfl

theorem cell22_1795932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 2, 4].length) (baseStart_1795932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1795932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1795932 prefixEnd_1795932 := by exact prefixLift 1795932
  have htrace : WordTrace (prefixWord ++ tailWord_1795932) baseStart_1795932 baseEnd_1795932 := by
    simpa [prefixWord, tailWord_1795932, baseEnd_1795932] using wordTrace_append hprefix tailTrace_1795932
  have hstable : (prefixWord ++ tailWord_1795932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795932).length < 2 ^ (prefixWord ++ tailWord_1795932).sum := by decide
  have hdescent : baseEnd_1795932 < baseStart_1795932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795988 : List Nat := [2, 4, 2, 1, 1, 2, 1, 4, 5]
def baseStart_1795988 : Nat := 118140960795 + 1795988 * 2 ^ 59
def prefixEnd_1795988 : Nat := 4983230072969 + 3 ^ 40 * 1795988 * 2
def baseEnd_1795988 : Nat := 204934465268272093864535

theorem tailTrace_1795988 : CollatzResearch.WordTrace tailWord_1795988 prefixEnd_1795988 204934465268272093864535 := by
  unfold tailWord_1795988
  simp only [CollatzResearch.WordTrace]
  refine ⟨32752531908724840587730309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43670042544966454116973745 32752531908724840587730309)
  ·
    refine ⟨6141099732885907610199433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32752531908724840587730309 6141099732885907610199433)
    ·
      refine ⟨4605824799664430707649575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6141099732885907610199433 4605824799664430707649575)
      ·
        refine ⟨6908737199496646061474363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4605824799664430707649575 6908737199496646061474363)
        ·
          refine ⟨10363105799244969092211545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6908737199496646061474363 10363105799244969092211545)
          ·
            refine ⟨7772329349433726819158659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10363105799244969092211545 7772329349433726819158659)
            ·
              refine ⟨11658494024150590228737989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7772329349433726819158659 11658494024150590228737989)
              ·
                refine ⟨2185967629528235667888373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11658494024150590228737989 2185967629528235667888373)
                ·
                  refine ⟨204934465268272093864535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2185967629528235667888373 204934465268272093864535)
                  ·
                    rfl

theorem cell22_1795988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_1795988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1795988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1795988 prefixEnd_1795988 := by exact prefixLift 1795988
  have htrace : WordTrace (prefixWord ++ tailWord_1795988) baseStart_1795988 baseEnd_1795988 := by
    simpa [prefixWord, tailWord_1795988, baseEnd_1795988] using wordTrace_append hprefix tailTrace_1795988
  have hstable : (prefixWord ++ tailWord_1795988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795988).length < 2 ^ (prefixWord ++ tailWord_1795988).sum := by decide
  have hdescent : baseEnd_1795988 < baseStart_1795988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796031 : List Nat := [1, 1, 2, 2, 2, 1, 3, 4, 1, 5]
def baseStart_1796031 : Nat := 118140960795 + 1796031 * 2 ^ 59
def prefixEnd_1796031 : Nat := 4983230072969 + 3 ^ 40 * 1796031 * 2
def baseEnd_1796031 : Nat := 614818115583578502768473

theorem tailTrace_1796031 : CollatzResearch.WordTrace tailWord_1796031 prefixEnd_1796031 614818115583578502768473 := by
  unfold tailWord_1796031
  simp only [CollatzResearch.WordTrace]
  refine ⟨65506632156293899519275947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43671088104195933012850631 65506632156293899519275947)
  ·
    refine ⟨98259948234440849278913921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65506632156293899519275947 98259948234440849278913921)
    ·
      refine ⟨73694961175830636959185441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98259948234440849278913921 73694961175830636959185441)
      ·
        refine ⟨55271220881872977719389081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73694961175830636959185441 55271220881872977719389081)
        ·
          refine ⟨41453415661404733289541811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55271220881872977719389081 41453415661404733289541811)
          ·
            refine ⟨62180123492107099934312717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41453415661404733289541811 62180123492107099934312717)
            ·
              refine ⟨23317546309540162475367269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62180123492107099934312717 23317546309540162475367269)
              ·
                refine ⟨4372039933038780464131363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23317546309540162475367269 4372039933038780464131363)
                ·
                  refine ⟨6558059899558170696197045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4372039933038780464131363 6558059899558170696197045)
                  ·
                    refine ⟨614818115583578502768473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6558059899558170696197045 614818115583578502768473)
                    ·
                      rfl

theorem cell22_1796031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 5].length) (baseStart_1796031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1796031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1796031 prefixEnd_1796031 := by exact prefixLift 1796031
  have htrace : WordTrace (prefixWord ++ tailWord_1796031) baseStart_1796031 baseEnd_1796031 := by
    simpa [prefixWord, tailWord_1796031, baseEnd_1796031] using wordTrace_append hprefix tailTrace_1796031
  have hstable : (prefixWord ++ tailWord_1796031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796031).length < 2 ^ (prefixWord ++ tailWord_1796031).sum := by decide
  have hdescent : baseEnd_1796031 < baseStart_1796031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796050 : List Nat := [3, 2, 2, 3, 2, 1, 2, 1, 6]
def baseStart_1796050 : Nat := 118140960795 + 1796050 * 2 ^ 59
def prefixEnd_1796050 : Nat := 4983230072969 + 3 ^ 40 * 1796050 * 2
def baseEnd_1796050 : Nat := 204941539890622928847805

theorem tailTrace_1796050 : CollatzResearch.WordTrace tailWord_1796050 prefixEnd_1796050 204941539890622928847805 := by
  unfold tailWord_1796050
  simp only [CollatzResearch.WordTrace]
  refine ⟨16376831285806266441054401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43671550095483377176145069 16376831285806266441054401)
  ·
    refine ⟨12282623464354699830790801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16376831285806266441054401 12282623464354699830790801)
    ·
      refine ⟨9211967598266024873093101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12282623464354699830790801 9211967598266024873093101)
      ·
        refine ⟨3454487849349759327409913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9211967598266024873093101 3454487849349759327409913)
        ·
          refine ⟨2590865887012319495557435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3454487849349759327409913 2590865887012319495557435)
          ·
            refine ⟨3886298830518479243336153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2590865887012319495557435 3886298830518479243336153)
            ·
              refine ⟨2914724122888859432502115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3886298830518479243336153 2914724122888859432502115)
              ·
                refine ⟨4372086184333289148753173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2914724122888859432502115 4372086184333289148753173)
                ·
                  refine ⟨204941539890622928847805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4372086184333289148753173 204941539890622928847805)
                  ·
                    rfl

theorem cell22_1796050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_1796050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1796050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1796050 prefixEnd_1796050 := by exact prefixLift 1796050
  have htrace : WordTrace (prefixWord ++ tailWord_1796050) baseStart_1796050 baseEnd_1796050 := by
    simpa [prefixWord, tailWord_1796050, baseEnd_1796050] using wordTrace_append hprefix tailTrace_1796050
  have hstable : (prefixWord ++ tailWord_1796050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796050).length < 2 ^ (prefixWord ++ tailWord_1796050).sum := by decide
  have hdescent : baseEnd_1796050 < baseStart_1796050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796078 : List Nat := [4, 1, 2, 1, 3, 2, 1, 8]
def baseStart_1796078 : Nat := 118140960795 + 1796078 * 2 ^ 59
def prefixEnd_1796078 : Nat := 4983230072969 + 3 ^ 40 * 1796078 * 2
def baseEnd_1796078 : Nat := 68314911627120671871481

theorem tailTrace_1796078 : CollatzResearch.WordTrace tailWord_1796078 prefixEnd_1796078 68314911627120671871481 := by
  unfold tailWord_1796078
  simp only [CollatzResearch.WordTrace]
  refine ⟨8188543298390453318279611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43672230924749084364157925 8188543298390453318279611)
  ·
    refine ⟨12282814947585679977419417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8188543298390453318279611 12282814947585679977419417)
    ·
      refine ⟨9212111210689259983064563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12282814947585679977419417 9212111210689259983064563)
      ·
        refine ⟨13818166816033889974596845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9212111210689259983064563 13818166816033889974596845)
        ·
          refine ⟨5181812556012708740473817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13818166816033889974596845 5181812556012708740473817)
          ·
            refine ⟨3886359417009531555355363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5181812556012708740473817 3886359417009531555355363)
            ·
              refine ⟨5829539125514297333033045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3886359417009531555355363 5829539125514297333033045)
              ·
                refine ⟨68314911627120671871481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5829539125514297333033045 68314911627120671871481)
                ·
                  rfl

theorem cell22_1796078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 8].length) (baseStart_1796078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1796078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1796078 prefixEnd_1796078 := by exact prefixLift 1796078
  have htrace : WordTrace (prefixWord ++ tailWord_1796078) baseStart_1796078 baseEnd_1796078 := by
    simpa [prefixWord, tailWord_1796078, baseEnd_1796078] using wordTrace_append hprefix tailTrace_1796078
  have hstable : (prefixWord ++ tailWord_1796078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796078).length < 2 ^ (prefixWord ++ tailWord_1796078).sum := by decide
  have hdescent : baseEnd_1796078 < baseStart_1796078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796093 : List Nat := [1, 4, 1, 1, 1, 2, 2, 2, 5, 3]
def baseStart_1796093 : Nat := 118140960795 + 1796093 * 2 ^ 59
def prefixEnd_1796093 : Nat := 4983230072969 + 3 ^ 40 * 1796093 * 2
def baseEnd_1796093 : Nat := 614839339450631007718283

theorem tailTrace_1796093 : CollatzResearch.WordTrace tailWord_1796093 prefixEnd_1796093 614839339450631007718283 := by
  unfold tailWord_1796093
  simp only [CollatzResearch.WordTrace]
  refine ⟨65508893482069284108032933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43672595654712856072021955 65508893482069284108032933)
  ·
    refine ⟨12282917527887990770256175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65508893482069284108032933 12282917527887990770256175)
    ·
      refine ⟨18424376291831986155384263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12282917527887990770256175 18424376291831986155384263)
      ·
        refine ⟨27636564437747979233076395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18424376291831986155384263 27636564437747979233076395)
        ·
          refine ⟨41454846656621968849614593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27636564437747979233076395 41454846656621968849614593)
          ·
            refine ⟨31091134992466476637210945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41454846656621968849614593 31091134992466476637210945)
            ·
              refine ⟨23318351244349857477908209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31091134992466476637210945 23318351244349857477908209)
              ·
                refine ⟨17488763433262393108431157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23318351244349857477908209 17488763433262393108431157)
                ·
                  refine ⟨1639571571868349353915421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17488763433262393108431157 1639571571868349353915421)
                  ·
                    refine ⟨614839339450631007718283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1639571571868349353915421 614839339450631007718283)
                    ·
                      rfl

theorem cell22_1796093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 5, 3].length) (baseStart_1796093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1796093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1796093 prefixEnd_1796093 := by exact prefixLift 1796093
  have htrace : WordTrace (prefixWord ++ tailWord_1796093) baseStart_1796093 baseEnd_1796093 := by
    simpa [prefixWord, tailWord_1796093, baseEnd_1796093] using wordTrace_append hprefix tailTrace_1796093
  have hstable : (prefixWord ++ tailWord_1796093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796093).length < 2 ^ (prefixWord ++ tailWord_1796093).sum := by decide
  have hdescent : baseEnd_1796093 < baseStart_1796093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796121 : List Nat := [1, 2, 1, 2, 1, 1, 3, 3, 1, 7]
def baseStart_1796121 : Nat := 118140960795 + 1796121 * 2 ^ 59
def prefixEnd_1796121 : Nat := 4983230072969 + 3 ^ 40 * 1796121 * 2
def baseEnd_1796121 : Nat := 614848924422848268018197

theorem tailTrace_1796121 : CollatzResearch.WordTrace tailWord_1796121 prefixEnd_1796121 614848924422848268018197 := by
  unfold tailWord_1796121
  simp only [CollatzResearch.WordTrace]
  refine ⟨65509914725967844890052217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43673276483978563260034811 65509914725967844890052217)
  ·
    refine ⟨49132436044475883667539163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65509914725967844890052217 49132436044475883667539163)
    ·
      refine ⟨73698654066713825501308745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49132436044475883667539163 73698654066713825501308745)
      ·
        refine ⟨55273990550035369125981559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73698654066713825501308745 55273990550035369125981559)
        ·
          refine ⟨82910985825053053688972339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55273990550035369125981559 82910985825053053688972339)
          ·
            refine ⟨124366478737579580533458509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82910985825053053688972339 124366478737579580533458509)
            ·
              refine ⟨46637429526592342700046941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124366478737579580533458509 46637429526592342700046941)
              ·
                refine ⟨17489036072472128512517603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46637429526592342700046941 17489036072472128512517603)
                ·
                  refine ⟨26233554108708192768776405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17489036072472128512517603 26233554108708192768776405)
                  ·
                    refine ⟨614848924422848268018197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26233554108708192768776405 614848924422848268018197)
                    ·
                      rfl

theorem cell22_1796121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 7].length) (baseStart_1796121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1796121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1796121 prefixEnd_1796121 := by exact prefixLift 1796121
  have htrace : WordTrace (prefixWord ++ tailWord_1796121) baseStart_1796121 baseEnd_1796121 := by
    simpa [prefixWord, tailWord_1796121, baseEnd_1796121] using wordTrace_append hprefix tailTrace_1796121
  have hstable : (prefixWord ++ tailWord_1796121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796121).length < 2 ^ (prefixWord ++ tailWord_1796121).sum := by decide
  have hdescent : baseEnd_1796121 < baseStart_1796121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796161 : List Nat := [1, 2, 5, 1, 2, 3, 2, 2, 1, 3]
def baseStart_1796161 : Nat := 118140960795 + 1796161 * 2 ^ 59
def prefixEnd_1796161 : Nat := 4983230072969 + 3 ^ 40 * 1796161 * 2
def baseEnd_1796161 : Nat := 614862617240301497018075

theorem tailTrace_1796161 : CollatzResearch.WordTrace tailWord_1796161 prefixEnd_1796161 614862617240301497018075 := by
  unfold tailWord_1796161
  simp only [CollatzResearch.WordTrace]
  refine ⟨65511373645822931721508337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43674249097215287814338891 65511373645822931721508337)
  ·
    refine ⟨49133530234367198791131253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65511373645822931721508337 49133530234367198791131253)
    ·
      refine ⟨4606268459471924886668555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49133530234367198791131253 4606268459471924886668555)
      ·
        refine ⟨6909402689207887330002833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4606268459471924886668555 6909402689207887330002833)
        ·
          refine ⟨5182052016905915497502125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6909402689207887330002833 5182052016905915497502125)
          ·
            refine ⟨1943269506339718311563297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5182052016905915497502125 1943269506339718311563297)
            ·
              refine ⟨1457452129754788733672473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1943269506339718311563297 1457452129754788733672473)
              ·
                refine ⟨1093089097316091550254355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1457452129754788733672473 1093089097316091550254355)
                ·
                  refine ⟨1639633645974137325381533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1093089097316091550254355 1639633645974137325381533)
                  ·
                    refine ⟨614862617240301497018075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1639633645974137325381533 614862617240301497018075)
                    ·
                      rfl

theorem cell22_1796161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_1796161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1796161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1796161 prefixEnd_1796161 := by exact prefixLift 1796161
  have htrace : WordTrace (prefixWord ++ tailWord_1796161) baseStart_1796161 baseEnd_1796161 := by
    simpa [prefixWord, tailWord_1796161, baseEnd_1796161] using wordTrace_append hprefix tailTrace_1796161
  have hstable : (prefixWord ++ tailWord_1796161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796161).length < 2 ^ (prefixWord ++ tailWord_1796161).sum := by decide
  have hdescent : baseEnd_1796161 < baseStart_1796161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796183 : List Nat := [1, 1, 3, 2, 2, 1, 3, 3, 1, 5]
def baseStart_1796183 : Nat := 118140960795 + 1796183 * 2 ^ 59
def prefixEnd_1796183 : Nat := 4983230072969 + 3 ^ 40 * 1796183 * 2
def baseEnd_1796183 : Nat := 614870148289900772968007

theorem tailTrace_1796183 : CollatzResearch.WordTrace tailWord_1796183 prefixEnd_1796183 614870148289900772968007 := by
  unfold tailWord_1796183
  simp only [CollatzResearch.WordTrace]
  refine ⟨65512176051743229478809203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43674784034495486319206135 65512176051743229478809203)
  ·
    refine ⟨98268264077614844218213805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65512176051743229478809203 98268264077614844218213805)
    ·
      refine ⟨36850599029105566581830177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98268264077614844218213805 36850599029105566581830177)
      ·
        refine ⟨27637949271829174936372633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36850599029105566581830177 27637949271829174936372633)
        ·
          refine ⟨20728461953871881202279475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27637949271829174936372633 20728461953871881202279475)
          ·
            refine ⟨31092692930807821803419213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20728461953871881202279475 31092692930807821803419213)
            ·
              refine ⟨11659759849052933176282205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31092692930807821803419213 11659759849052933176282205)
              ·
                refine ⟨4372409943394849941105827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11659759849052933176282205 4372409943394849941105827)
                ·
                  refine ⟨6558614915092274911658741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4372409943394849941105827 6558614915092274911658741)
                  ·
                    refine ⟨614870148289900772968007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6558614915092274911658741 614870148289900772968007)
                    ·
                      rfl

theorem cell22_1796183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 5].length) (baseStart_1796183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1796183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1796183 prefixEnd_1796183 := by exact prefixLift 1796183
  have htrace : WordTrace (prefixWord ++ tailWord_1796183) baseStart_1796183 baseEnd_1796183 := by
    simpa [prefixWord, tailWord_1796183, baseEnd_1796183] using wordTrace_append hprefix tailTrace_1796183
  have hstable : (prefixWord ++ tailWord_1796183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796183).length < 2 ^ (prefixWord ++ tailWord_1796183).sum := by decide
  have hdescent : baseEnd_1796183 < baseStart_1796183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796217 : List Nat := [1, 2, 1, 3, 4, 1, 3, 2, 2, 3]
def baseStart_1796217 : Nat := 118140960795 + 1796217 * 2 ^ 59
def prefixEnd_1796217 : Nat := 4983230072969 + 3 ^ 40 * 1796217 * 2
def baseEnd_1796217 : Nat := 614881787184736017617903

theorem tailTrace_1796217 : CollatzResearch.WordTrace tailWord_1796217 prefixEnd_1796217 614881787184736017617903 := by
  unfold tailWord_1796217
  simp only [CollatzResearch.WordTrace]
  refine ⟨65513416133620053285546905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43675610755746702190364603 65513416133620053285546905)
  ·
    refine ⟨49135062100215039964160179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65513416133620053285546905 49135062100215039964160179)
    ·
      refine ⟨73702593150322559946240269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49135062100215039964160179 73702593150322559946240269)
      ·
        refine ⟨27638472431370959979840101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73702593150322559946240269 27638472431370959979840101)
        ·
          refine ⟨5182213580882054996220019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27638472431370959979840101 5182213580882054996220019)
          ·
            refine ⟨7773320371323082494330029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5182213580882054996220019 7773320371323082494330029)
            ·
              refine ⟨2914995139246155935373761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7773320371323082494330029 2914995139246155935373761)
              ·
                refine ⟨2186246354434616951530321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2914995139246155935373761 2186246354434616951530321)
                ·
                  refine ⟨1639684765825962713647741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2186246354434616951530321 1639684765825962713647741)
                  ·
                    refine ⟨614881787184736017617903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1639684765825962713647741 614881787184736017617903)
                    ·
                      rfl

theorem cell22_1796217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2, 2, 3].length) (baseStart_1796217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1796217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1796217 prefixEnd_1796217 := by exact prefixLift 1796217
  have htrace : WordTrace (prefixWord ++ tailWord_1796217) baseStart_1796217 baseEnd_1796217 := by
    simpa [prefixWord, tailWord_1796217, baseEnd_1796217] using wordTrace_append hprefix tailTrace_1796217
  have hstable : (prefixWord ++ tailWord_1796217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796217).length < 2 ^ (prefixWord ++ tailWord_1796217).sum := by decide
  have hdescent : baseEnd_1796217 < baseStart_1796217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796234 : List Nat := [3, 1, 2, 3, 1, 3, 3, 1, 2, 3]
def baseStart_1796234 : Nat := 118140960795 + 1796234 * 2 ^ 59
def prefixEnd_1796234 : Nat := 4983230072969 + 3 ^ 40 * 1796234 * 2
def baseEnd_1796234 : Nat := 614887606632153639942851

theorem tailTrace_1796234 : CollatzResearch.WordTrace tailWord_1796234 prefixEnd_1796234 614887606632153639942851 := by
  unfold tailWord_1796234
  simp only [CollatzResearch.WordTrace]
  refine ⟨16378509043639616297228939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43676024116372310125943837 16378509043639616297228939)
  ·
    refine ⟨24567763565459424445843409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16378509043639616297228939 24567763565459424445843409)
    ·
      refine ⟨18425822674094568334382557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24567763565459424445843409 18425822674094568334382557)
      ·
        refine ⟨6909683502785463125393459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18425822674094568334382557 6909683502785463125393459)
        ·
          refine ⟨10364525254178194688090189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6909683502785463125393459 10364525254178194688090189)
          ·
            refine ⟨3886696970316823008033821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10364525254178194688090189 3886696970316823008033821)
            ·
              refine ⟨1457511363868808628012683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3886696970316823008033821 1457511363868808628012683)
              ·
                refine ⟨2186267045803212942019025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1457511363868808628012683 2186267045803212942019025)
                ·
                  refine ⟨1639700284352409706514269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2186267045803212942019025 1639700284352409706514269)
                  ·
                    refine ⟨614887606632153639942851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1639700284352409706514269 614887606632153639942851)
                    ·
                      rfl

theorem cell22_1796234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 1, 2, 3].length) (baseStart_1796234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1796234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1796234 prefixEnd_1796234 := by exact prefixLift 1796234
  have htrace : WordTrace (prefixWord ++ tailWord_1796234) baseStart_1796234 baseEnd_1796234 := by
    simpa [prefixWord, tailWord_1796234, baseEnd_1796234] using wordTrace_append hprefix tailTrace_1796234
  have hstable : (prefixWord ++ tailWord_1796234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796234).length < 2 ^ (prefixWord ++ tailWord_1796234).sum := by decide
  have hdescent : baseEnd_1796234 < baseStart_1796234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796245 : List Nat := [1, 3, 2, 1, 1, 1, 3, 4, 3, 3]
def baseStart_1796245 : Nat := 118140960795 + 1796245 * 2 ^ 59
def prefixEnd_1796245 : Nat := 4983230072969 + 3 ^ 40 * 1796245 * 2
def baseEnd_1796245 : Nat := 614891372156953277917817

theorem tailTrace_1796245 : CollatzResearch.WordTrace tailWord_1796245 prefixEnd_1796245 614891372156953277917817 := by
  unfold tailWord_1796245
  simp only [CollatzResearch.WordTrace]
  refine ⟨65514437377518614067566189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43676291585012409378377459 65514437377518614067566189)
  ·
    refine ⟨24567914016569480275337321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65514437377518614067566189 24567914016569480275337321)
    ·
      refine ⟨18425935512427110206502991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24567914016569480275337321 18425935512427110206502991)
      ·
        refine ⟨27638903268640665309754487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18425935512427110206502991 27638903268640665309754487)
        ·
          refine ⟨41458354902960997964631731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27638903268640665309754487 41458354902960997964631731)
          ·
            refine ⟨62187532354441496946947597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41458354902960997964631731 62187532354441496946947597)
            ·
              refine ⟨23320324632915561355105349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62187532354441496946947597 23320324632915561355105349)
              ·
                refine ⟨4372560868671667754082253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23320324632915561355105349 4372560868671667754082253)
                ·
                  refine ⟨1639710325751875407780845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4372560868671667754082253 1639710325751875407780845)
                  ·
                    refine ⟨614891372156953277917817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1639710325751875407780845 614891372156953277917817)
                    ·
                      rfl

theorem cell22_1796245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 3, 3].length) (baseStart_1796245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1796245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1796245 prefixEnd_1796245 := by exact prefixLift 1796245
  have htrace : WordTrace (prefixWord ++ tailWord_1796245) baseStart_1796245 baseEnd_1796245 := by
    simpa [prefixWord, tailWord_1796245, baseEnd_1796245] using wordTrace_append hprefix tailTrace_1796245
  have hstable : (prefixWord ++ tailWord_1796245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796245).length < 2 ^ (prefixWord ++ tailWord_1796245).sum := by decide
  have hdescent : baseEnd_1796245 < baseStart_1796245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796247 : List Nat := [1, 1, 3, 3, 4, 2, 2, 6]
def baseStart_1796247 : Nat := 118140960795 + 1796247 * 2 ^ 59
def prefixEnd_1796247 : Nat := 4983230072969 + 3 ^ 40 * 1796247 * 2
def baseEnd_1796247 : Nat := 68321339644202882151979

theorem tailTrace_1796247 : CollatzResearch.WordTrace tailWord_1796247 prefixEnd_1796247 68321339644202882151979 := by
  unfold tailWord_1796247
  simp only [CollatzResearch.WordTrace]
  refine ⟨65514510323511368409138995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43676340215674245606092663 65514510323511368409138995)
  ·
    refine ⟨98271765485267052613708493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65514510323511368409138995 98271765485267052613708493)
    ·
      refine ⟨36851912056975144730140685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98271765485267052613708493 36851912056975144730140685)
      ·
        refine ⟨13819467021365679273802757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36851912056975144730140685 13819467021365679273802757)
        ·
          refine ⟨2591150066506064863838017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13819467021365679273802757 2591150066506064863838017)
          ·
            refine ⟨1943362549879548647878513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2591150066506064863838017 1943362549879548647878513)
            ·
              refine ⟨1457521912409661485908885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1943362549879548647878513 1457521912409661485908885)
              ·
                refine ⟨68321339644202882151979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1457521912409661485908885 68321339644202882151979)
                ·
                  rfl

theorem cell22_1796247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 6].length) (baseStart_1796247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1796247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1796247 prefixEnd_1796247 := by exact prefixLift 1796247
  have htrace : WordTrace (prefixWord ++ tailWord_1796247) baseStart_1796247 baseEnd_1796247 := by
    simpa [prefixWord, tailWord_1796247, baseEnd_1796247] using wordTrace_append hprefix tailTrace_1796247
  have hstable : (prefixWord ++ tailWord_1796247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796247).length < 2 ^ (prefixWord ++ tailWord_1796247).sum := by decide
  have hdescent : baseEnd_1796247 < baseStart_1796247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796292 : List Nat := [2, 3, 3, 1, 2, 2, 1, 3, 5]
def baseStart_1796292 : Nat := 118140960795 + 1796292 * 2 ^ 59
def prefixEnd_1796292 : Nat := 4983230072969 + 3 ^ 40 * 1796292 * 2
def baseEnd_1796292 : Nat := 204969153739153607330891

theorem tailTrace_1796292 : CollatzResearch.WordTrace tailWord_1796292 prefixEnd_1796292 204969153739153607330891 := by
  unfold tailWord_1796292
  simp only [CollatzResearch.WordTrace]
  refine ⟨32758075804174170547263565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43677434405565560729684753 32758075804174170547263565)
  ·
    refine ⟨12284278426565313955223837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32758075804174170547263565 12284278426565313955223837)
    ·
      refine ⟨4606604409961992733208939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12284278426565313955223837 4606604409961992733208939)
      ·
        refine ⟨6909906614942989099813409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4606604409961992733208939 6909906614942989099813409)
        ·
          refine ⟨5182429961207241824860057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6909906614942989099813409 5182429961207241824860057)
          ·
            refine ⟨3886822470905431368645043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5182429961207241824860057 3886822470905431368645043)
            ·
              refine ⟨5830233706358147052967565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3886822470905431368645043 5830233706358147052967565)
              ·
                refine ⟨2186337639884305144862837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5830233706358147052967565 2186337639884305144862837)
                ·
                  refine ⟨204969153739153607330891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2186337639884305144862837 204969153739153607330891)
                  ·
                    rfl

theorem cell22_1796292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_1796292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1796292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1796292 prefixEnd_1796292 := by exact prefixLift 1796292
  have htrace : WordTrace (prefixWord ++ tailWord_1796292) baseStart_1796292 baseEnd_1796292 := by
    simpa [prefixWord, tailWord_1796292, baseEnd_1796292] using wordTrace_append hprefix tailTrace_1796292
  have hstable : (prefixWord ++ tailWord_1796292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796292).length < 2 ^ (prefixWord ++ tailWord_1796292).sum := by decide
  have hdescent : baseEnd_1796292 < baseStart_1796292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796303 : List Nat := [1, 1, 2, 1, 1, 3, 4, 1, 8]
def baseStart_1796303 : Nat := 118140960795 + 1796303 * 2 ^ 59
def prefixEnd_1796303 : Nat := 4983230072969 + 3 ^ 40 * 1796303 * 2
def baseEnd_1796303 : Nat := 204970408914086819989213

theorem tailTrace_1796303 : CollatzResearch.WordTrace tailWord_1796303 prefixEnd_1796303 204970408914086819989213 := by
  unfold tailWord_1796303
  simp only [CollatzResearch.WordTrace]
  refine ⟨65516552811308489973177563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43677701874205659982118375 65516552811308489973177563)
  ·
    refine ⟨98274829216962734959766345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65516552811308489973177563 98274829216962734959766345)
    ·
      refine ⟨73706121912722051219824759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98274829216962734959766345 73706121912722051219824759)
      ·
        refine ⟨110559182869083076829737139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73706121912722051219824759 110559182869083076829737139)
        ·
          refine ⟨165838774303624615244605709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110559182869083076829737139 165838774303624615244605709)
          ·
            refine ⟨62189540363859230716727141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165838774303624615244605709 62189540363859230716727141)
            ·
              refine ⟨11660538818223605759386339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62189540363859230716727141 11660538818223605759386339)
              ·
                refine ⟨17490808227335408639079509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11660538818223605759386339 17490808227335408639079509)
                ·
                  refine ⟨204970408914086819989213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17490808227335408639079509 204970408914086819989213)
                  ·
                    rfl

theorem cell22_1796303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 8].length) (baseStart_1796303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1796303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1796303 prefixEnd_1796303 := by exact prefixLift 1796303
  have htrace : WordTrace (prefixWord ++ tailWord_1796303) baseStart_1796303 baseEnd_1796303 := by
    simpa [prefixWord, tailWord_1796303, baseEnd_1796303] using wordTrace_append hprefix tailTrace_1796303
  have hstable : (prefixWord ++ tailWord_1796303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796303).length < 2 ^ (prefixWord ++ tailWord_1796303).sum := by decide
  have hdescent : baseEnd_1796303 < baseStart_1796303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796352 : List Nat := [2, 1, 1, 2, 1, 1, 6, 3, 2, 3]
def baseStart_1796352 : Nat := 118140960795 + 1796352 * 2 ^ 59
def prefixEnd_1796352 : Nat := 4983230072969 + 3 ^ 40 * 1796352 * 2
def baseEnd_1796352 : Nat := 614928000443640665492489

theorem tailTrace_1796352 : CollatzResearch.WordTrace tailWord_1796352 prefixEnd_1796352 614928000443640665492489 := by
  unfold tailWord_1796352
  simp only [CollatzResearch.WordTrace]
  refine ⟨32759169994065485670855655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43678893325420647561140873 32759169994065485670855655)
  ·
    refine ⟨49138754991098228506283483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32759169994065485670855655 49138754991098228506283483)
    ·
      refine ⟨73708132486647342759425225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49138754991098228506283483 73708132486647342759425225)
      ·
        refine ⟨55281099364985507069568919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73708132486647342759425225 55281099364985507069568919)
        ·
          refine ⟨82921649047478260604353379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55281099364985507069568919 82921649047478260604353379)
          ·
            refine ⟨124382473571217390906530069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82921649047478260604353379 124382473571217390906530069)
            ·
              refine ⟨5830428448650815198743597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 124382473571217390906530069 5830428448650815198743597)
              ·
                refine ⟨2186410668244055699528849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5830428448650815198743597 2186410668244055699528849)
                ·
                  refine ⟨1639808001183041774646637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2186410668244055699528849 1639808001183041774646637)
                  ·
                    refine ⟨614928000443640665492489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1639808001183041774646637 614928000443640665492489)
                    ·
                      rfl

theorem cell22_1796352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3, 2, 3].length) (baseStart_1796352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1796352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1796352 prefixEnd_1796352 := by exact prefixLift 1796352
  have htrace : WordTrace (prefixWord ++ tailWord_1796352) baseStart_1796352 baseEnd_1796352 := by
    simpa [prefixWord, tailWord_1796352, baseEnd_1796352] using wordTrace_append hprefix tailTrace_1796352
  have hstable : (prefixWord ++ tailWord_1796352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796352).length < 2 ^ (prefixWord ++ tailWord_1796352).sum := by decide
  have hdescent : baseEnd_1796352 < baseStart_1796352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796386 : List Nat := [3, 3, 1, 1, 3, 3, 1, 2, 2, 3]
def baseStart_1796386 : Nat := 118140960795 + 1796386 * 2 ^ 59
def prefixEnd_1796386 : Nat := 4983230072969 + 3 ^ 40 * 1796386 * 2
def baseEnd_1796386 : Nat := 614939639338475910142385

theorem tailTrace_1796386 : CollatzResearch.WordTrace tailWord_1796386 prefixEnd_1796386 614939639338475910142385 := by
  unfold tailWord_1796386
  simp only [CollatzResearch.WordTrace]
  refine ⟨16379895017501948787112253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43679720046671863432299341 16379895017501948787112253)
  ·
    refine ⟨6142460631563230795167095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16379895017501948787112253 6142460631563230795167095)
    ·
      refine ⟨9213690947344846192750643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6142460631563230795167095 9213690947344846192750643)
      ·
        refine ⟨13820536421017269289125965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9213690947344846192750643 13820536421017269289125965)
        ·
          refine ⟨5182701157881475983422237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13820536421017269289125965 5182701157881475983422237)
          ·
            refine ⟨1943512934205553493783339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5182701157881475983422237 1943512934205553493783339)
            ·
              refine ⟨2915269401308330240675009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1943512934205553493783339 2915269401308330240675009)
              ·
                refine ⟨2186452050981247680506257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2915269401308330240675009 2186452050981247680506257)
                ·
                  refine ⟨1639839038235935760379693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2186452050981247680506257 1639839038235935760379693)
                  ·
                    refine ⟨614939639338475910142385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1639839038235935760379693 614939639338475910142385)
                    ·
                      rfl

theorem cell22_1796386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_1796386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1796386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1796386 prefixEnd_1796386 := by exact prefixLift 1796386
  have htrace : WordTrace (prefixWord ++ tailWord_1796386) baseStart_1796386 baseEnd_1796386 := by
    simpa [prefixWord, tailWord_1796386, baseEnd_1796386] using wordTrace_append hprefix tailTrace_1796386
  have hstable : (prefixWord ++ tailWord_1796386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796386).length < 2 ^ (prefixWord ++ tailWord_1796386).sum := by decide
  have hdescent : baseEnd_1796386 < baseStart_1796386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796414 : List Nat := [4, 2, 1, 2, 1, 2, 2, 2, 3, 3]
def baseStart_1796414 : Nat := 118140960795 + 1796414 * 2 ^ 59
def prefixEnd_1796414 : Nat := 4983230072969 + 3 ^ 40 * 1796414 * 2
def baseEnd_1796414 : Nat := 614949224310693170442299

theorem tailTrace_1796414 : CollatzResearch.WordTrace tailWord_1796414 prefixEnd_1796414 614949224310693170442299 := by
  unfold tailWord_1796414
  simp only [CollatzResearch.WordTrace]
  refine ⟨8190075164238294491308537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43680400875937570620312197 8190075164238294491308537)
  ·
    refine ⟨6142556373178720868481403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8190075164238294491308537 6142556373178720868481403)
    ·
      refine ⟨9213834559768081302722105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6142556373178720868481403 9213834559768081302722105)
      ·
        refine ⟨6910375919826060977041579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9213834559768081302722105 6910375919826060977041579)
        ·
          refine ⟨10365563879739091465562369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6910375919826060977041579 10365563879739091465562369)
          ·
            refine ⟨7774172909804318599171777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10365563879739091465562369 7774172909804318599171777)
            ·
              refine ⟨5830629682353238949378833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7774172909804318599171777 5830629682353238949378833)
              ·
                refine ⟨4372972261764929212034125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5830629682353238949378833 4372972261764929212034125)
                ·
                  refine ⟨1639864598161848454512797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4372972261764929212034125 1639864598161848454512797)
                  ·
                    refine ⟨614949224310693170442299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1639864598161848454512797 614949224310693170442299)
                    ·
                      rfl

theorem cell22_1796414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_1796414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1796414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1796414 prefixEnd_1796414 := by exact prefixLift 1796414
  have htrace : WordTrace (prefixWord ++ tailWord_1796414) baseStart_1796414 baseEnd_1796414 := by
    simpa [prefixWord, tailWord_1796414, baseEnd_1796414] using wordTrace_append hprefix tailTrace_1796414
  have hstable : (prefixWord ++ tailWord_1796414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796414).length < 2 ^ (prefixWord ++ tailWord_1796414).sum := by decide
  have hdescent : baseEnd_1796414 < baseStart_1796414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796448 : List Nat := [2, 1, 1, 3, 5, 1, 3, 2, 1, 3]
def baseStart_1796448 : Nat := 118140960795 + 1796448 * 2 ^ 59
def prefixEnd_1796448 : Nat := 4983230072969 + 3 ^ 40 * 1796448 * 2
def baseEnd_1796448 : Nat := 614960863205528415092195

theorem tailTrace_1796448 : CollatzResearch.WordTrace tailWord_1796448 prefixEnd_1796448 614960863205528415092195 := by
  unfold tailWord_1796448
  simp only [CollatzResearch.WordTrace]
  refine ⟨32760920697891589868602999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43681227597188786491470665 32760920697891589868602999)
  ·
    refine ⟨49141381046837384802904499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32760920697891589868602999 49141381046837384802904499)
    ·
      refine ⟨73712071570256077204356749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49141381046837384802904499 73712071570256077204356749)
      ·
        refine ⟨27642026838846028951633781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73712071570256077204356749 27642026838846028951633781)
        ·
          refine ⟨2591440016141815214215667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27642026838846028951633781 2591440016141815214215667)
          ·
            refine ⟨3887160024212722821323501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2591440016141815214215667 3887160024212722821323501)
            ·
              refine ⟨1457685009079771057996313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3887160024212722821323501 1457685009079771057996313)
              ·
                refine ⟨1093263756809828293497235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1457685009079771057996313 1093263756809828293497235)
                ·
                  refine ⟨1639895635214742440245853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1093263756809828293497235 1639895635214742440245853)
                  ·
                    refine ⟨614960863205528415092195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1639895635214742440245853 614960863205528415092195)
                    ·
                      rfl

theorem cell22_1796448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 2, 1, 3].length) (baseStart_1796448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1796448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1796448 prefixEnd_1796448 := by exact prefixLift 1796448
  have htrace : WordTrace (prefixWord ++ tailWord_1796448) baseStart_1796448 baseEnd_1796448 := by
    simpa [prefixWord, tailWord_1796448, baseEnd_1796448] using wordTrace_append hprefix tailTrace_1796448
  have hstable : (prefixWord ++ tailWord_1796448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796448).length < 2 ^ (prefixWord ++ tailWord_1796448).sum := by decide
  have hdescent : baseEnd_1796448 < baseStart_1796448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796487 : List Nat := [1, 1, 4, 2, 2, 1, 3, 2, 1, 5]
def baseStart_1796487 : Nat := 118140960795 + 1796487 * 2 ^ 59
def prefixEnd_1796487 : Nat := 4983230072969 + 3 ^ 40 * 1796487 * 2
def baseEnd_1796487 : Nat := 614974213702545313367075

theorem tailTrace_1796487 : CollatzResearch.WordTrace tailWord_1796487 prefixEnd_1796487 614974213702545313367075 := by
  unfold tailWord_1796487
  simp only [CollatzResearch.WordTrace]
  refine ⟨65523263842641889397875715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43682175895094592931917143 65523263842641889397875715)
  ·
    refine ⟨98284895763962834096813573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65523263842641889397875715 98284895763962834096813573)
    ·
      refine ⟨18428417955743031393152545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98284895763962834096813573 18428417955743031393152545)
      ·
        refine ⟨13821313466807273544864409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18428417955743031393152545 13821313466807273544864409)
        ·
          refine ⟨10365985100105455158648307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13821313466807273544864409 10365985100105455158648307)
          ·
            refine ⟨15548977650158182737972461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10365985100105455158648307 15548977650158182737972461)
            ·
              refine ⟨5830866618809318526739673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15548977650158182737972461 5830866618809318526739673)
              ·
                refine ⟨4373149964106988895054755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5830866618809318526739673 4373149964106988895054755)
                ·
                  refine ⟨6559724946160483342582133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4373149964106988895054755 6559724946160483342582133)
                  ·
                    refine ⟨614974213702545313367075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6559724946160483342582133 614974213702545313367075)
                    ·
                      rfl

theorem cell22_1796487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_1796487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1796487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1796487 prefixEnd_1796487 := by exact prefixLift 1796487
  have htrace : WordTrace (prefixWord ++ tailWord_1796487) baseStart_1796487 baseEnd_1796487 := by
    simpa [prefixWord, tailWord_1796487, baseEnd_1796487] using wordTrace_append hprefix tailTrace_1796487
  have hstable : (prefixWord ++ tailWord_1796487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796487).length < 2 ^ (prefixWord ++ tailWord_1796487).sum := by decide
  have hdescent : baseEnd_1796487 < baseStart_1796487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796506 : List Nat := [3, 1, 1, 4, 1, 2, 4, 2, 4]
def baseStart_1796506 : Nat := 118140960795 + 1796506 * 2 ^ 59
def prefixEnd_1796506 : Nat := 4983230072969 + 3 ^ 40 * 1796506 * 2
def baseEnd_1796506 : Nat := 204993572596945199047339

theorem tailTrace_1796506 : CollatzResearch.WordTrace tailWord_1796506 prefixEnd_1796506 204993572596945199047339 := by
  unfold tailWord_1796506
  simp only [CollatzResearch.WordTrace]
  refine ⟨16380989207393263910704343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43682637886382037095211581 16380989207393263910704343)
  ·
    refine ⟨24571483811089895866056515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16380989207393263910704343 24571483811089895866056515)
    ·
      refine ⟨36857225716634843799084773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24571483811089895866056515 36857225716634843799084773)
      ·
        refine ⟨6910729821869033212328395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36857225716634843799084773 6910729821869033212328395)
        ·
          refine ⟨10366094732803549818492593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6910729821869033212328395 10366094732803549818492593)
          ·
            refine ⟨7774571049602662363869445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10366094732803549818492593 7774571049602662363869445)
            ·
              refine ⟨1457732071800499193225521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7774571049602662363869445 1457732071800499193225521)
              ·
                refine ⟨1093299053850374394919141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1457732071800499193225521 1093299053850374394919141)
                ·
                  refine ⟨204993572596945199047339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1093299053850374394919141 204993572596945199047339)
                  ·
                    rfl

theorem cell22_1796506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 2, 4].length) (baseStart_1796506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1796506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1796506 prefixEnd_1796506 := by exact prefixLift 1796506
  have htrace : WordTrace (prefixWord ++ tailWord_1796506) baseStart_1796506 baseEnd_1796506 := by
    simpa [prefixWord, tailWord_1796506, baseEnd_1796506] using wordTrace_append hprefix tailTrace_1796506
  have hstable : (prefixWord ++ tailWord_1796506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796506).length < 2 ^ (prefixWord ++ tailWord_1796506).sum := by decide
  have hdescent : baseEnd_1796506 < baseStart_1796506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796577 : List Nat := [1, 2, 3, 1, 2, 2, 1, 3, 2, 5]
def baseStart_1796577 : Nat := 118140960795 + 1796577 * 2 ^ 59
def prefixEnd_1796577 : Nat := 4983230072969 + 3 ^ 40 * 1796577 * 2
def baseEnd_1796577 : Nat := 615005022541815078616799

theorem tailTrace_1796577 : CollatzResearch.WordTrace tailWord_1796577 prefixEnd_1796577 615005022541815078616799 := by
  unfold tailWord_1796577
  simp only [CollatzResearch.WordTrace]
  refine ⟨65526546412315834768651985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43684364274877223179101323 65526546412315834768651985)
  ·
    refine ⟨49144909809236876076488989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65526546412315834768651985 49144909809236876076488989)
    ·
      refine ⟨18429341178463828528683371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49144909809236876076488989 18429341178463828528683371)
      ·
        refine ⟨27644011767695742793025057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18429341178463828528683371 27644011767695742793025057)
        ·
          refine ⟨20733008825771807094768793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27644011767695742793025057 20733008825771807094768793)
          ·
            refine ⟨15549756619328855321076595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20733008825771807094768793 15549756619328855321076595)
            ·
              refine ⟨23324634928993282981614893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15549756619328855321076595 23324634928993282981614893)
              ·
                refine ⟨8746738098372481118105585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23324634928993282981614893 8746738098372481118105585)
                ·
                  refine ⟨6560053573779360838579189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8746738098372481118105585 6560053573779360838579189)
                  ·
                    refine ⟨615005022541815078616799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6560053573779360838579189 615005022541815078616799)
                    ·
                      rfl

theorem cell22_1796577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_1796577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1796577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1796577 prefixEnd_1796577 := by exact prefixLift 1796577
  have htrace : WordTrace (prefixWord ++ tailWord_1796577) baseStart_1796577 baseEnd_1796577 := by
    simpa [prefixWord, tailWord_1796577, baseEnd_1796577] using wordTrace_append hprefix tailTrace_1796577
  have hstable : (prefixWord ++ tailWord_1796577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796577).length < 2 ^ (prefixWord ++ tailWord_1796577).sum := by decide
  have hdescent : baseEnd_1796577 < baseStart_1796577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796673 : List Nat := [1, 2, 5, 1, 1, 3, 2, 2, 2, 3]
def baseStart_1796673 : Nat := 118140960795 + 1796673 * 2 ^ 59
def prefixEnd_1796673 : Nat := 4983230072969 + 3 ^ 40 * 1796673 * 2
def baseEnd_1796673 : Nat := 615037885303702828216505

theorem tailTrace_1796673 : CollatzResearch.WordTrace tailWord_1796673 prefixEnd_1796673 615037885303702828216505 := by
  unfold tailWord_1796673
  simp only [CollatzResearch.WordTrace]
  refine ⟨65530047819968043164146673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43686698546645362109431115 65530047819968043164146673)
  ·
    refine ⟨49147535864976032373110005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65530047819968043164146673 49147535864976032373110005)
    ·
      refine ⟨4607581487341503034979063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49147535864976032373110005 4607581487341503034979063)
      ·
        refine ⟨6911372231012254552468595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4607581487341503034979063 6911372231012254552468595)
        ·
          refine ⟨10367058346518381828702893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6911372231012254552468595 10367058346518381828702893)
          ·
            refine ⟨3887646879944393185763585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10367058346518381828702893 3887646879944393185763585)
            ·
              refine ⟨2915735159958294889322689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3887646879944393185763585 2915735159958294889322689)
              ·
                refine ⟨2186801369968721166992017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2915735159958294889322689 2186801369968721166992017)
                ·
                  refine ⟨1640101027476540875244013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2186801369968721166992017 1640101027476540875244013)
                  ·
                    refine ⟨615037885303702828216505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1640101027476540875244013 615037885303702828216505)
                    ·
                      rfl

theorem cell22_1796673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_1796673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1796673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1796673 prefixEnd_1796673 := by exact prefixLift 1796673
  have htrace : WordTrace (prefixWord ++ tailWord_1796673) baseStart_1796673 baseEnd_1796673 := by
    simpa [prefixWord, tailWord_1796673, baseEnd_1796673] using wordTrace_append hprefix tailTrace_1796673
  have hstable : (prefixWord ++ tailWord_1796673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796673).length < 2 ^ (prefixWord ++ tailWord_1796673).sum := by decide
  have hdescent : baseEnd_1796673 < baseStart_1796673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796697 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 11]
def baseStart_1796697 : Nat := 118140960795 + 1796697 * 2 ^ 59
def prefixEnd_1796697 : Nat := 4983230072969 + 3 ^ 40 * 1796697 * 2
def baseEnd_1796697 : Nat := 205015366998058255205477

theorem tailTrace_1796697 : CollatzResearch.WordTrace tailWord_1796697 prefixEnd_1796697 205015366998058255205477 := by
  unfold tailWord_1796697
  simp only [CollatzResearch.WordTrace]
  refine ⟨65530923171881095263020345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43687282114587396842013563 65530923171881095263020345)
  ·
    refine ⟨49148192378910821447265259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65530923171881095263020345 49148192378910821447265259)
    ·
      refine ⟨73722288568366232170897889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49148192378910821447265259 73722288568366232170897889)
      ·
        refine ⟨55291716426274674128173417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73722288568366232170897889 55291716426274674128173417)
        ·
          refine ⟨41468787319706005596130063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55291716426274674128173417 41468787319706005596130063)
          ·
            refine ⟨62203180979559008394195095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41468787319706005596130063 62203180979559008394195095)
            ·
              refine ⟨93304771469338512591292643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62203180979559008394195095 93304771469338512591292643)
              ·
                refine ⟨139957157204007768886938965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93304771469338512591292643 139957157204007768886938965)
                ·
                  refine ⟨205015366998058255205477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 139957157204007768886938965 205015366998058255205477)
                  ·
                    rfl

theorem cell22_1796697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 11].length) (baseStart_1796697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1796697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1796697 prefixEnd_1796697 := by exact prefixLift 1796697
  have htrace : WordTrace (prefixWord ++ tailWord_1796697) baseStart_1796697 baseEnd_1796697 := by
    simpa [prefixWord, tailWord_1796697, baseEnd_1796697] using wordTrace_append hprefix tailTrace_1796697
  have hstable : (prefixWord ++ tailWord_1796697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796697).length < 2 ^ (prefixWord ++ tailWord_1796697).sum := by decide
  have hdescent : baseEnd_1796697 < baseStart_1796697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796714 : List Nat := [3, 1, 3, 2, 1, 1, 2, 2, 7]
def baseStart_1796714 : Nat := 118140960795 + 1796714 * 2 ^ 59
def prefixEnd_1796714 : Nat := 4983230072969 + 3 ^ 40 * 1796714 * 2
def baseEnd_1796714 : Nat := 205017306813864129313793

theorem tailTrace_1796714 : CollatzResearch.WordTrace tailWord_1796714 prefixEnd_1796714 205017306813864129313793 := by
  unfold tailWord_1796714
  simp only [CollatzResearch.WordTrace]
  refine ⟨16382885803204876791597299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43687695475213004777592797 16382885803204876791597299)
  ·
    refine ⟨24574328704807315187395949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16382885803204876791597299 24574328704807315187395949)
    ·
      refine ⟨9215373264302743195273481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24574328704807315187395949 9215373264302743195273481)
      ·
        refine ⟨6911529948227057396455111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9215373264302743195273481 6911529948227057396455111)
        ·
          refine ⟨10367294922340586094682667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6911529948227057396455111 10367294922340586094682667)
          ·
            refine ⟨15550942383510879142024001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10367294922340586094682667 15550942383510879142024001)
            ·
              refine ⟨11663206787633159356518001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15550942383510879142024001 11663206787633159356518001)
              ·
                refine ⟨8747405090724869517388501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11663206787633159356518001 8747405090724869517388501)
                ·
                  refine ⟨205017306813864129313793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8747405090724869517388501 205017306813864129313793)
                  ·
                    rfl

theorem cell22_1796714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 7].length) (baseStart_1796714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1796714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1796714 prefixEnd_1796714 := by exact prefixLift 1796714
  have htrace : WordTrace (prefixWord ++ tailWord_1796714) baseStart_1796714 baseEnd_1796714 := by
    simpa [prefixWord, tailWord_1796714, baseEnd_1796714] using wordTrace_append hprefix tailTrace_1796714
  have hstable : (prefixWord ++ tailWord_1796714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796714).length < 2 ^ (prefixWord ++ tailWord_1796714).sum := by decide
  have hdescent : baseEnd_1796714 < baseStart_1796714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796729 : List Nat := [1, 2, 1, 3, 3, 2, 1, 2, 2, 5]
def baseStart_1796729 : Nat := 118140960795 + 1796729 * 2 ^ 59
def prefixEnd_1796729 : Nat := 4983230072969 + 3 ^ 40 * 1796729 * 2
def baseEnd_1796729 : Nat := 615057055248137348816333

theorem tailTrace_1796729 : CollatzResearch.WordTrace tailWord_1796729 prefixEnd_1796729 615057055248137348816333 := by
  unfold tailWord_1796729
  simp only [CollatzResearch.WordTrace]
  refine ⟨65532090307765164728185241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43688060205176776485456827 65532090307765164728185241)
  ·
    refine ⟨49149067730823873546138931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65532090307765164728185241 49149067730823873546138931)
    ·
      refine ⟨73723601596235810319208397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49149067730823873546138931 73723601596235810319208397)
      ·
        refine ⟨27646350598588428869703149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73723601596235810319208397 27646350598588428869703149)
        ·
          refine ⟨10367381474470660826138681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27646350598588428869703149 10367381474470660826138681)
          ·
            refine ⟨7775536105852995619604011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10367381474470660826138681 7775536105852995619604011)
            ·
              refine ⟨11663304158779493429406017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7775536105852995619604011 11663304158779493429406017)
              ·
                refine ⟨8747478119084620072054513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11663304158779493429406017 8747478119084620072054513)
                ·
                  refine ⟨6560608589313465054040885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8747478119084620072054513 6560608589313465054040885)
                  ·
                    refine ⟨615057055248137348816333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6560608589313465054040885 615057055248137348816333)
                    ·
                      rfl

theorem cell22_1796729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 5].length) (baseStart_1796729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1796729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1796729 prefixEnd_1796729 := by exact prefixLift 1796729
  have htrace : WordTrace (prefixWord ++ tailWord_1796729) baseStart_1796729 baseEnd_1796729 := by
    simpa [prefixWord, tailWord_1796729, baseEnd_1796729] using wordTrace_append hprefix tailTrace_1796729
  have hstable : (prefixWord ++ tailWord_1796729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796729).length < 2 ^ (prefixWord ++ tailWord_1796729).sum := by decide
  have hdescent : baseEnd_1796729 < baseStart_1796729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796759 : List Nat := [1, 1, 3, 3, 2, 1, 1, 4, 6]
def baseStart_1796759 : Nat := 118140960795 + 1796759 * 2 ^ 59
def prefixEnd_1796759 : Nat := 4983230072969 + 3 ^ 40 * 1796759 * 2
def baseEnd_1796759 : Nat := 205022441620409090188747

theorem tailTrace_1796759 : CollatzResearch.WordTrace tailWord_1796759 prefixEnd_1796759 205022441620409090188747 := by
  unfold tailWord_1796759
  simp only [CollatzResearch.WordTrace]
  refine ⟨65533184497656479851777331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43688789665104319901184887 65533184497656479851777331)
  ·
    refine ⟨98299776746484719777665997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65533184497656479851777331 98299776746484719777665997)
    ·
      refine ⟨36862416279931769916624749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98299776746484719777665997 36862416279931769916624749)
      ·
        refine ⟨13823406104974413718734281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36862416279931769916624749 13823406104974413718734281)
        ·
          refine ⟨10367554578730810289050711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13823406104974413718734281 10367554578730810289050711)
          ·
            refine ⟨15551331868096215433576067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10367554578730810289050711 15551331868096215433576067)
            ·
              refine ⟨23326997802144323150364101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15551331868096215433576067 23326997802144323150364101)
              ·
                refine ⟨4373812087902060590693269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23326997802144323150364101 4373812087902060590693269)
                ·
                  refine ⟨205022441620409090188747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4373812087902060590693269 205022441620409090188747)
                  ·
                    rfl

theorem cell22_1796759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 6].length) (baseStart_1796759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1796759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1796759 prefixEnd_1796759 := by exact prefixLift 1796759
  have htrace : WordTrace (prefixWord ++ tailWord_1796759) baseStart_1796759 baseEnd_1796759 := by
    simpa [prefixWord, tailWord_1796759, baseEnd_1796759] using wordTrace_append hprefix tailTrace_1796759
  have hstable : (prefixWord ++ tailWord_1796759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796759).length < 2 ^ (prefixWord ++ tailWord_1796759).sum := by decide
  have hdescent : baseEnd_1796759 < baseStart_1796759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796761 : List Nat := [1, 2, 1, 2, 1, 2, 6, 2, 1, 4]
def baseStart_1796761 : Nat := 118140960795 + 1796761 * 2 ^ 59
def prefixEnd_1796761 : Nat := 4983230072969 + 3 ^ 40 * 1796761 * 2
def baseEnd_1796761 : Nat := 615068009502099932016235

theorem tailTrace_1796761 : CollatzResearch.WordTrace tailWord_1796761 prefixEnd_1796761 615068009502099932016235 := by
  unfold tailWord_1796761
  simp only [CollatzResearch.WordTrace]
  refine ⟨65533257443649234193350137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43688838295766156128900091 65533257443649234193350137)
  ·
    refine ⟨49149943082736925645012603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65533257443649234193350137 49149943082736925645012603)
    ·
      refine ⟨73724914624105388467518905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49149943082736925645012603 73724914624105388467518905)
      ·
        refine ⟨55293685968079041350639179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73724914624105388467518905 55293685968079041350639179)
        ·
          refine ⟨82940528952118562025958769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55293685968079041350639179 82940528952118562025958769)
          ·
            refine ⟨62205396714088921519469077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82940528952118562025958769 62205396714088921519469077)
            ·
              refine ⟨2915877970972918196225113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62205396714088921519469077 2915877970972918196225113)
              ·
                refine ⟨2186908478229688647168835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2915877970972918196225113 2186908478229688647168835)
                ·
                  refine ⟨3280362717344532970753253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2186908478229688647168835 3280362717344532970753253)
                  ·
                    refine ⟨615068009502099932016235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3280362717344532970753253 615068009502099932016235)
                    ·
                      rfl

theorem cell22_1796761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2, 1, 4].length) (baseStart_1796761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1796761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1796761 prefixEnd_1796761 := by exact prefixLift 1796761
  have htrace : WordTrace (prefixWord ++ tailWord_1796761) baseStart_1796761 baseEnd_1796761 := by
    simpa [prefixWord, tailWord_1796761, baseEnd_1796761] using wordTrace_append hprefix tailTrace_1796761
  have hstable : (prefixWord ++ tailWord_1796761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796761).length < 2 ^ (prefixWord ++ tailWord_1796761).sum := by decide
  have hdescent : baseEnd_1796761 < baseStart_1796761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796808 : List Nat := [2, 1, 3, 1, 2, 4, 1, 3, 2, 3]
def baseStart_1796808 : Nat := 118140960795 + 1796808 * 2 ^ 59
def prefixEnd_1796808 : Nat := 4983230072969 + 3 ^ 40 * 1796808 * 2
def baseEnd_1796808 : Nat := 615084098562607476091091

theorem tailTrace_1796808 : CollatzResearch.WordTrace tailWord_1796808 prefixEnd_1796808 615084098562607476091091 := by
  unfold tailWord_1796808
  simp only [CollatzResearch.WordTrace]
  refine ⟨32767485837239480610155539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43689981116319307480207385 32767485837239480610155539)
  ·
    refine ⟨49151228755859220915233309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32767485837239480610155539 49151228755859220915233309)
    ·
      refine ⟨18431710783447207843212491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49151228755859220915233309 18431710783447207843212491)
      ·
        refine ⟨27647566175170811764818737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18431710783447207843212491 27647566175170811764818737)
        ·
          refine ⟨20735674631378108823614053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27647566175170811764818737 20735674631378108823614053)
          ·
            refine ⟨3887938993383395404427635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20735674631378108823614053 3887938993383395404427635)
            ·
              refine ⟨5831908490075093106641453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3887938993383395404427635 5831908490075093106641453)
              ·
                refine ⟨2186965683778159914990545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5831908490075093106641453 2186965683778159914990545)
                ·
                  refine ⟨1640224262833619936242909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2186965683778159914990545 1640224262833619936242909)
                  ·
                    refine ⟨615084098562607476091091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1640224262833619936242909 615084098562607476091091)
                    ·
                      rfl

theorem cell22_1796808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3, 2, 3].length) (baseStart_1796808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1796808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1796808 prefixEnd_1796808 := by exact prefixLift 1796808
  have htrace : WordTrace (prefixWord ++ tailWord_1796808) baseStart_1796808 baseEnd_1796808 := by
    simpa [prefixWord, tailWord_1796808, baseEnd_1796808] using wordTrace_append hprefix tailTrace_1796808
  have hstable : (prefixWord ++ tailWord_1796808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796808).length < 2 ^ (prefixWord ++ tailWord_1796808).sum := by decide
  have hdescent : baseEnd_1796808 < baseStart_1796808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796887 : List Nat := [1, 1, 3, 4, 3, 1, 2, 3, 1, 3]
def baseStart_1796887 : Nat := 118140960795 + 1796887 * 2 ^ 59
def prefixEnd_1796887 : Nat := 4983230072969 + 3 ^ 40 * 1796887 * 2
def baseEnd_1796887 : Nat := 615111141877077603365849

theorem tailTrace_1796887 : CollatzResearch.WordTrace tailWord_1796887 prefixEnd_1796887 615111141877077603365849 := by
  unfold tailWord_1796887
  simp only [CollatzResearch.WordTrace]
  refine ⟨65537853041192757712436915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43691902027461838474957943 65537853041192757712436915)
  ·
    refine ⟨98306779561789136568655373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65537853041192757712436915 98306779561789136568655373)
    ·
      refine ⟨36865042335670926213245765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98306779561789136568655373 36865042335670926213245765)
      ·
        refine ⟨6912195437938298664983581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36865042335670926213245765 6912195437938298664983581)
        ·
          refine ⟨2592073289226861999368843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6912195437938298664983581 2592073289226861999368843)
          ·
            refine ⟨3888109933840292999053265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2592073289226861999368843 3888109933840292999053265)
            ·
              refine ⟨2916082450380219749289949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3888109933840292999053265 2916082450380219749289949)
              ·
                refine ⟨1093530918892582405983731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2916082450380219749289949 1093530918892582405983731)
                ·
                  refine ⟨1640296378338873608975597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1093530918892582405983731 1640296378338873608975597)
                  ·
                    refine ⟨615111141877077603365849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1640296378338873608975597 615111141877077603365849)
                    ·
                      rfl

theorem cell22_1796887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 3, 1, 3].length) (baseStart_1796887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1796887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1796887 prefixEnd_1796887 := by exact prefixLift 1796887
  have htrace : WordTrace (prefixWord ++ tailWord_1796887) baseStart_1796887 baseEnd_1796887 := by
    simpa [prefixWord, tailWord_1796887, baseEnd_1796887] using wordTrace_append hprefix tailTrace_1796887
  have hstable : (prefixWord ++ tailWord_1796887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796887).length < 2 ^ (prefixWord ++ tailWord_1796887).sum := by decide
  have hdescent : baseEnd_1796887 < baseStart_1796887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796900 : List Nat := [2, 3, 1, 3, 3, 2, 1, 2, 5]
def baseStart_1796900 : Nat := 118140960795 + 1796900 * 2 ^ 59
def prefixEnd_1796900 : Nat := 4983230072969 + 3 ^ 40 * 1796900 * 2
def baseEnd_1796900 : Nat := 205038530680916634263603

theorem tailTrace_1796900 : CollatzResearch.WordTrace tailWord_1796900 prefixEnd_1796900 205038530680916634263603 := by
  unfold tailWord_1796900
  simp only [CollatzResearch.WordTrace]
  refine ⟨32769163595072830466330077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43692218126763773955106769 32769163595072830466330077)
  ·
    refine ⟨12288436348152311424873779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32769163595072830466330077 12288436348152311424873779)
    ·
      refine ⟨18432654522228467137310669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12288436348152311424873779 18432654522228467137310669)
      ·
        refine ⟨6912245445835675176491501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18432654522228467137310669 6912245445835675176491501)
        ·
          refine ⟨2592092042188378191184313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6912245445835675176491501 2592092042188378191184313)
          ·
            refine ⟨1944069031641283643388235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2592092042188378191184313 1944069031641283643388235)
            ·
              refine ⟨2916103547461925465082353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1944069031641283643388235 2916103547461925465082353)
              ·
                refine ⟨2187077660596444098811765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2916103547461925465082353 2187077660596444098811765)
                ·
                  refine ⟨205038530680916634263603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2187077660596444098811765 205038530680916634263603)
                  ·
                    rfl

theorem cell22_1796900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 2, 5].length) (baseStart_1796900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1796900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1796900 prefixEnd_1796900 := by exact prefixLift 1796900
  have htrace : WordTrace (prefixWord ++ tailWord_1796900) baseStart_1796900 baseEnd_1796900 := by
    simpa [prefixWord, tailWord_1796900, baseEnd_1796900] using wordTrace_append hprefix tailTrace_1796900
  have hstable : (prefixWord ++ tailWord_1796900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796900).length < 2 ^ (prefixWord ++ tailWord_1796900).sum := by decide
  have hdescent : baseEnd_1796900 < baseStart_1796900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796962 : List Nat := [3, 3, 2, 1, 4, 1, 1, 1, 6]
def baseStart_1796962 : Nat := 118140960795 + 1796962 * 2 ^ 59
def prefixEnd_1796962 : Nat := 4983230072969 + 3 ^ 40 * 1796962 * 2
def baseEnd_1796962 : Nat := 205045605303267469246873

theorem tailTrace_1796962 : CollatzResearch.WordTrace tailWord_1796962 prefixEnd_1796962 205045605303267469246873 := by
  unfold tailWord_1796962
  simp only [CollatzResearch.WordTrace]
  refine ⟨16385147128980261380354285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43693725677280697014278093 16385147128980261380354285)
  ·
    refine ⟨6144430173367598017632857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16385147128980261380354285 6144430173367598017632857)
    ·
      refine ⟨4608322630025698513224643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6144430173367598017632857 4608322630025698513224643)
      ·
        refine ⟨6912483945038547769836965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4608322630025698513224643 6912483945038547769836965)
        ·
          refine ⟨1296090739694727706844431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6912483945038547769836965 1296090739694727706844431)
          ·
            refine ⟨1944136109542091560266647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1296090739694727706844431 1944136109542091560266647)
            ·
              refine ⟨2916204164313137340399971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1944136109542091560266647 2916204164313137340399971)
              ·
                refine ⟨4374306246469706010599957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2916204164313137340399971 4374306246469706010599957)
                ·
                  refine ⟨205045605303267469246873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4374306246469706010599957 205045605303267469246873)
                  ·
                    rfl

theorem cell22_1796962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_1796962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1796962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1796962 prefixEnd_1796962 := by exact prefixLift 1796962
  have htrace : WordTrace (prefixWord ++ tailWord_1796962) baseStart_1796962 baseEnd_1796962 := by
    simpa [prefixWord, tailWord_1796962, baseEnd_1796962] using wordTrace_append hprefix tailTrace_1796962
  have hstable : (prefixWord ++ tailWord_1796962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796962).length < 2 ^ (prefixWord ++ tailWord_1796962).sum := by decide
  have hdescent : baseEnd_1796962 < baseStart_1796962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796977 : List Nat := [1, 2, 2, 2, 1, 6, 2, 1, 2, 3]
def baseStart_1796977 : Nat := 118140960795 + 1796977 * 2 ^ 59
def prefixEnd_1796977 : Nat := 4983230072969 + 3 ^ 40 * 1796977 * 2
def baseEnd_1796977 : Nat := 615141950716347368615573

theorem tailTrace_1796977 : CollatzResearch.WordTrace tailWord_1796977 prefixEnd_1796977 615141950716347368615573 := by
  unfold tailWord_1796977
  simp only [CollatzResearch.WordTrace]
  refine ⟨65541135610866703083213185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43694090407244468722142123 65541135610866703083213185)
  ·
    refine ⟨49155851708150027312409889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65541135610866703083213185 49155851708150027312409889)
    ·
      refine ⟨36866888781112520484307417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49155851708150027312409889 36866888781112520484307417)
      ·
        refine ⟨27650166585834390363230563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36866888781112520484307417 27650166585834390363230563)
        ·
          refine ⟨41475249878751585544845845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27650166585834390363230563 41475249878751585544845845)
          ·
            refine ⟨1944152338066480572414649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41475249878751585544845845 1944152338066480572414649)
            ·
              refine ⟨1458114253549860429310987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1944152338066480572414649 1458114253549860429310987)
              ·
                refine ⟨2187171380324790643966481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1458114253549860429310987 2187171380324790643966481)
                ·
                  refine ⟨1640378535243592982974861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2187171380324790643966481 1640378535243592982974861)
                  ·
                    refine ⟨615141950716347368615573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1640378535243592982974861 615141950716347368615573)
                    ·
                      rfl

theorem cell22_1796977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 1, 2, 3].length) (baseStart_1796977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1796977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1796977 prefixEnd_1796977 := by exact prefixLift 1796977
  have htrace : WordTrace (prefixWord ++ tailWord_1796977) baseStart_1796977 baseEnd_1796977 := by
    simpa [prefixWord, tailWord_1796977, baseEnd_1796977] using wordTrace_append hprefix tailTrace_1796977
  have hstable : (prefixWord ++ tailWord_1796977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796977).length < 2 ^ (prefixWord ++ tailWord_1796977).sum := by decide
  have hdescent : baseEnd_1796977 < baseStart_1796977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796988 : List Nat := [2, 2, 2, 1, 1, 1, 1, 6, 3, 3]
def baseStart_1796988 : Nat := 118140960795 + 1796988 * 2 ^ 59
def prefixEnd_1796988 : Nat := 4983230072969 + 3 ^ 40 * 1796988 * 2
def baseEnd_1796988 : Nat := 615145716241147006590539

theorem tailTrace_1796988 : CollatzResearch.WordTrace tailWord_1796988 prefixEnd_1796988 615145716241147006590539 := by
  unfold tailWord_1796988
  simp only [CollatzResearch.WordTrace]
  refine ⟨32770768406913425980931809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43694357875884567974575745 32770768406913425980931809)
  ·
    refine ⟨24578076305185069485698857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32770768406913425980931809 24578076305185069485698857)
    ·
      refine ⟨18433557228888802114274143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24578076305185069485698857 18433557228888802114274143)
      ·
        refine ⟨27650335843333203171411215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18433557228888802114274143 27650335843333203171411215)
        ·
          refine ⟨41475503764999804757116823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27650335843333203171411215 41475503764999804757116823)
          ·
            refine ⟨62213255647499707135675235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41475503764999804757116823 62213255647499707135675235)
            ·
              refine ⟨93319883471249560703512853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62213255647499707135675235 93319883471249560703512853)
              ·
                refine ⟨4374369537714823157977165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 93319883471249560703512853 4374369537714823157977165)
                ·
                  refine ⟨1640388576643058684241437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4374369537714823157977165 1640388576643058684241437)
                  ·
                    refine ⟨615145716241147006590539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1640388576643058684241437 615145716241147006590539)
                    ·
                      rfl

theorem cell22_1796988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 3, 3].length) (baseStart_1796988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1796988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1796988 prefixEnd_1796988 := by exact prefixLift 1796988
  have htrace : WordTrace (prefixWord ++ tailWord_1796988) baseStart_1796988 baseEnd_1796988 := by
    simpa [prefixWord, tailWord_1796988, baseEnd_1796988] using wordTrace_append hprefix tailTrace_1796988
  have hstable : (prefixWord ++ tailWord_1796988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796988).length < 2 ^ (prefixWord ++ tailWord_1796988).sum := by decide
  have hdescent : baseEnd_1796988 < baseStart_1796988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797048 : List Nat := [2, 1, 2, 1, 2, 4, 2, 1, 3, 4]
def baseStart_1797048 : Nat := 118140960795 + 1797048 * 2 ^ 59
def prefixEnd_1797048 : Nat := 4983230072969 + 3 ^ 40 * 1797048 * 2
def baseEnd_1797048 : Nat := 615166255467326850090355

theorem tailTrace_1797048 : CollatzResearch.WordTrace tailWord_1797048 prefixEnd_1797048 615166255467326850090355 := by
  unfold tailWord_1797048
  simp only [CollatzResearch.WordTrace]
  refine ⟨32771862596804741104523899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43695816795739654806031865 32771862596804741104523899)
  ·
    refine ⟨49157793895207111656785849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32771862596804741104523899 49157793895207111656785849)
    ·
      refine ⟨36868345421405333742589387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49157793895207111656785849 36868345421405333742589387)
      ·
        refine ⟨55302518132108000613884081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36868345421405333742589387 55302518132108000613884081)
        ·
          refine ⟨41476888599081000460413061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55302518132108000613884081 41476888599081000460413061)
          ·
            refine ⟨7776916612327687586327449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41476888599081000460413061 7776916612327687586327449)
            ·
              refine ⟨5832687459245765689745587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7776916612327687586327449 5832687459245765689745587)
              ·
                refine ⟨8749031188868648534618381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5832687459245765689745587 8749031188868648534618381)
                ·
                  refine ⟨3280886695825743200481893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8749031188868648534618381 3280886695825743200481893)
                  ·
                    refine ⟨615166255467326850090355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3280886695825743200481893 615166255467326850090355)
                    ·
                      rfl

theorem cell22_1797048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 3, 4].length) (baseStart_1797048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1797048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1797048 prefixEnd_1797048 := by exact prefixLift 1797048
  have htrace : WordTrace (prefixWord ++ tailWord_1797048) baseStart_1797048 baseEnd_1797048 := by
    simpa [prefixWord, tailWord_1797048, baseEnd_1797048] using wordTrace_append hprefix tailTrace_1797048
  have hstable : (prefixWord ++ tailWord_1797048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797048).length < 2 ^ (prefixWord ++ tailWord_1797048).sum := by decide
  have hdescent : baseEnd_1797048 < baseStart_1797048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797061 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 2, 9]
def baseStart_1797061 : Nat := 118140960795 + 1797061 * 2 ^ 59
def prefixEnd_1797061 : Nat := 4983230072969 + 3 ^ 40 * 1797061 * 2
def baseEnd_1797061 : Nat := 615170705632999149515315

theorem tailTrace_1797061 : CollatzResearch.WordTrace tailWord_1797061 prefixEnd_1797061 615170705632999149515315 := by
  unfold tailWord_1797061
  simp only [CollatzResearch.WordTrace]
  refine ⟨65544199342562385429271037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43696132895041590286180691 65544199342562385429271037)
  ·
    refine ⟨24579074753460894535976639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65544199342562385429271037 24579074753460894535976639)
    ·
      refine ⟨36868612130191341803964959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24579074753460894535976639 36868612130191341803964959)
      ·
        refine ⟨55302918195287012705947439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36868612130191341803964959 55302918195287012705947439)
        ·
          refine ⟨82954377292930519058921159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55302918195287012705947439 82954377292930519058921159)
          ·
            refine ⟨124431565939395778588381739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82954377292930519058921159 124431565939395778588381739)
            ·
              refine ⟨186647348909093667882572609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124431565939395778588381739 186647348909093667882572609)
              ·
                refine ⟨139985511681820250911929457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186647348909093667882572609 139985511681820250911929457)
                ·
                  refine ⟨104989133761365188183947093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139985511681820250911929457 104989133761365188183947093)
                  ·
                    refine ⟨615170705632999149515315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 104989133761365188183947093 615170705632999149515315)
                    ·
                      rfl

theorem cell22_1797061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_1797061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1797061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1797061 prefixEnd_1797061 := by exact prefixLift 1797061
  have htrace : WordTrace (prefixWord ++ tailWord_1797061) baseStart_1797061 baseEnd_1797061 := by
    simpa [prefixWord, tailWord_1797061, baseEnd_1797061] using wordTrace_append hprefix tailTrace_1797061
  have hstable : (prefixWord ++ tailWord_1797061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797061).length < 2 ^ (prefixWord ++ tailWord_1797061).sum := by decide
  have hdescent : baseEnd_1797061 < baseStart_1797061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797069 : List Nat := [1, 6, 3, 1, 1, 1, 1, 1, 7]
def baseStart_1797069 : Nat := 118140960795 + 1797069 * 2 ^ 59
def prefixEnd_1797069 : Nat := 4983230072969 + 3 ^ 40 * 1797069 * 2
def baseEnd_1797069 : Nat := 205057814732163265105097

theorem tailTrace_1797069 : CollatzResearch.WordTrace tailWord_1797069 prefixEnd_1797069 205057814732163265105097 := by
  unfold tailWord_1797069
  simp only [CollatzResearch.WordTrace]
  refine ⟨65544491126533402795562261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43696327417688935197041507 65544491126533402795562261)
  ·
    refine ⟨3072398021556253256041981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 65544491126533402795562261 3072398021556253256041981)
    ·
      refine ⟨1152149258083594971015743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3072398021556253256041981 1152149258083594971015743)
      ·
        refine ⟨1728223887125392456523615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1152149258083594971015743 1728223887125392456523615)
        ·
          refine ⟨2592335830688088684785423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1728223887125392456523615 2592335830688088684785423)
          ·
            refine ⟨3888503746032133027178135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2592335830688088684785423 3888503746032133027178135)
            ·
              refine ⟨5832755619048199540767203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3888503746032133027178135 5832755619048199540767203)
              ·
                refine ⟨8749133428572299311150805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5832755619048199540767203 8749133428572299311150805)
                ·
                  refine ⟨205057814732163265105097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8749133428572299311150805 205057814732163265105097)
                  ·
                    rfl

theorem cell22_1797069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_1797069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1797069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1797069 prefixEnd_1797069 := by exact prefixLift 1797069
  have htrace : WordTrace (prefixWord ++ tailWord_1797069) baseStart_1797069 baseEnd_1797069 := by
    simpa [prefixWord, tailWord_1797069, baseEnd_1797069] using wordTrace_append hprefix tailTrace_1797069
  have hstable : (prefixWord ++ tailWord_1797069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797069).length < 2 ^ (prefixWord ++ tailWord_1797069).sum := by decide
  have hdescent : baseEnd_1797069 < baseStart_1797069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797080 : List Nat := [2, 1, 2, 2, 2, 3, 2, 4, 4]
def baseStart_1797080 : Nat := 118140960795 + 1797080 * 2 ^ 59
def prefixEnd_1797080 : Nat := 4983230072969 + 3 ^ 40 * 1797080 * 2
def baseEnd_1797080 : Nat := 205059069907096477763419

theorem tailTrace_1797080 : CollatzResearch.WordTrace tailWord_1797080 prefixEnd_1797080 205059069907096477763419 := by
  unfold tailWord_1797080
  simp only [CollatzResearch.WordTrace]
  refine ⟨32772446164746775837106347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43696594886329034449475129 32772446164746775837106347)
  ·
    refine ⟨49158669247120163755659521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32772446164746775837106347 49158669247120163755659521)
    ·
      refine ⟨36869001935340122816744641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49158669247120163755659521 36869001935340122816744641)
      ·
        refine ⟨27651751451505092112558481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36869001935340122816744641 27651751451505092112558481)
        ·
          refine ⟨20738813588628819084418861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27651751451505092112558481 20738813588628819084418861)
          ·
            refine ⟨7777055095735807156657073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20738813588628819084418861 7777055095735807156657073)
            ·
              refine ⟨5832791321801855367492805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7777055095735807156657073 5832791321801855367492805)
              ·
                refine ⟨1093648372837847881404901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5832791321801855367492805 1093648372837847881404901)
                ·
                  refine ⟨205059069907096477763419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1093648372837847881404901 205059069907096477763419)
                  ·
                    rfl

theorem cell22_1797080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 4, 4].length) (baseStart_1797080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1797080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1797080 prefixEnd_1797080 := by exact prefixLift 1797080
  have htrace : WordTrace (prefixWord ++ tailWord_1797080) baseStart_1797080 baseEnd_1797080 := by
    simpa [prefixWord, tailWord_1797080, baseEnd_1797080] using wordTrace_append hprefix tailTrace_1797080
  have hstable : (prefixWord ++ tailWord_1797080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797080).length < 2 ^ (prefixWord ++ tailWord_1797080).sum := by decide
  have hdescent : baseEnd_1797080 < baseStart_1797080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797095 : List Nat := [1, 1, 5, 2, 2, 1, 3, 1, 1, 5]
def baseStart_1797095 : Nat := 118140960795 + 1797095 * 2 ^ 59
def prefixEnd_1797095 : Nat := 4983230072969 + 3 ^ 40 * 1797095 * 2
def baseEnd_1797095 : Nat := 615182344527834394165211

theorem tailTrace_1797095 : CollatzResearch.WordTrace tailWord_1797095 prefixEnd_1797095 615182344527834394165211 := by
  unfold tailWord_1797095
  simp only [CollatzResearch.WordTrace]
  refine ⟨65545439424439209236008739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43696959616292806157339159 65545439424439209236008739)
  ·
    refine ⟨98318159136658813854013109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65545439424439209236008739 98318159136658813854013109)
    ·
      refine ⟨9217327419061763798813729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98318159136658813854013109 9217327419061763798813729)
      ·
        refine ⟨6912995564296322849110297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9217327419061763798813729 6912995564296322849110297)
        ·
          refine ⟨5184746673222242136832723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6912995564296322849110297 5184746673222242136832723)
          ·
            refine ⟨7777120009833363205249085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5184746673222242136832723 7777120009833363205249085)
            ·
              refine ⟨2916420003687511201968407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7777120009833363205249085 2916420003687511201968407)
              ·
                refine ⟨4374630005531266802952611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2916420003687511201968407 4374630005531266802952611)
                ·
                  refine ⟨6561945008296900204428917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4374630005531266802952611 6561945008296900204428917)
                  ·
                    refine ⟨615182344527834394165211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6561945008296900204428917 615182344527834394165211)
                    ·
                      rfl

theorem cell22_1797095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_1797095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1797095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1797095 prefixEnd_1797095 := by exact prefixLift 1797095
  have htrace : WordTrace (prefixWord ++ tailWord_1797095) baseStart_1797095 baseEnd_1797095 := by
    simpa [prefixWord, tailWord_1797095, baseEnd_1797095] using wordTrace_append hprefix tailTrace_1797095
  have hstable : (prefixWord ++ tailWord_1797095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797095).length < 2 ^ (prefixWord ++ tailWord_1797095).sum := by decide
  have hdescent : baseEnd_1797095 < baseStart_1797095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797110 : List Nat := [5, 1, 1, 1, 3, 1, 2, 1, 1, 6]
def baseStart_1797110 : Nat := 118140960795 + 1797110 * 2 ^ 59
def prefixEnd_1797110 : Nat := 4983230072969 + 3 ^ 40 * 1797110 * 2
def baseEnd_1797110 : Nat := 615187479334379355040165

theorem tailTrace_1797110 : CollatzResearch.WordTrace tailWord_1797110 prefixEnd_1797110 615187479334379355040165 := by
  unfold tailWord_1797110
  simp only [CollatzResearch.WordTrace]
  refine ⟨4096624157461554174862799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43697324346256577865203189 4096624157461554174862799)
  ·
    refine ⟨6144936236192331262294199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4096624157461554174862799 6144936236192331262294199)
    ·
      refine ⟨9217404354288496893441299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6144936236192331262294199 9217404354288496893441299)
      ·
        refine ⟨13826106531432745340161949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9217404354288496893441299 13826106531432745340161949)
        ·
          refine ⟨5184789949287279502560731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13826106531432745340161949 5184789949287279502560731)
          ·
            refine ⟨7777184923930919253841097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5184789949287279502560731 7777184923930919253841097)
            ·
              refine ⟨5832888692948189440380823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7777184923930919253841097 5832888692948189440380823)
              ·
                refine ⟨8749333039422284160571235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5832888692948189440380823 8749333039422284160571235)
                ·
                  refine ⟨13123999559133426240856853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8749333039422284160571235 13123999559133426240856853)
                  ·
                    refine ⟨615187479334379355040165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13123999559133426240856853 615187479334379355040165)
                    ·
                      rfl

theorem cell22_1797110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_1797110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1797110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1797110 prefixEnd_1797110 := by exact prefixLift 1797110
  have htrace : WordTrace (prefixWord ++ tailWord_1797110) baseStart_1797110 baseEnd_1797110 := by
    simpa [prefixWord, tailWord_1797110, baseEnd_1797110] using wordTrace_append hprefix tailTrace_1797110
  have hstable : (prefixWord ++ tailWord_1797110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797110).length < 2 ^ (prefixWord ++ tailWord_1797110).sum := by decide
  have hdescent : baseEnd_1797110 < baseStart_1797110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797191 : List Nat := [1, 1, 4, 1, 3, 4, 2, 2, 1, 3]
def baseStart_1797191 : Nat := 118140960795 + 1797191 * 2 ^ 59
def prefixEnd_1797191 : Nat := 4983230072969 + 3 ^ 40 * 1797191 * 2
def baseEnd_1797191 : Nat := 615215207289722143764917

theorem tailTrace_1797191 : CollatzResearch.WordTrace tailWord_1797191 prefixEnd_1797191 615215207289722143764917 := by
  unfold tailWord_1797191
  simp only [CollatzResearch.WordTrace]
  refine ⟨65548940832091417631503427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43699293888060945087668951 65548940832091417631503427)
  ·
    refine ⟨98323411248137126447255141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65548940832091417631503427 98323411248137126447255141)
    ·
      refine ⟨18435639609025711208860339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98323411248137126447255141 18435639609025711208860339)
      ·
        refine ⟨27653459413538566813290509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18435639609025711208860339 27653459413538566813290509)
        ·
          refine ⟨10370047280076962554983941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27653459413538566813290509 10370047280076962554983941)
          ·
            refine ⟨1944383865014430479059489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10370047280076962554983941 1944383865014430479059489)
            ·
              refine ⟨1458287898760822859294617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1944383865014430479059489 1458287898760822859294617)
              ·
                refine ⟨1093715924070617144470963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1458287898760822859294617 1093715924070617144470963)
                ·
                  refine ⟨1640573886105925716706445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1093715924070617144470963 1640573886105925716706445)
                  ·
                    refine ⟨615215207289722143764917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1640573886105925716706445 615215207289722143764917)
                    ·
                      rfl

theorem cell22_1797191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 2, 1, 3].length) (baseStart_1797191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1797191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1797191 prefixEnd_1797191 := by exact prefixLift 1797191
  have htrace : WordTrace (prefixWord ++ tailWord_1797191) baseStart_1797191 baseEnd_1797191 := by
    simpa [prefixWord, tailWord_1797191, baseEnd_1797191] using wordTrace_append hprefix tailTrace_1797191
  have hstable : (prefixWord ++ tailWord_1797191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797191).length < 2 ^ (prefixWord ++ tailWord_1797191).sum := by decide
  have hdescent : baseEnd_1797191 < baseStart_1797191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797232 : List Nat := [2, 1, 1, 1, 5, 1, 4, 3, 4]
def baseStart_1797232 : Nat := 118140960795 + 1797232 * 2 ^ 59
def prefixEnd_1797232 : Nat := 4983230072969 + 3 ^ 40 * 1797232 * 2
def baseEnd_1797232 : Nat := 205076414142537234496597

theorem tailTrace_1797232 : CollatzResearch.WordTrace tailWord_1797232 prefixEnd_1797232 205076414142537234496597 := by
  unfold tailWord_1797232
  simp only [CollatzResearch.WordTrace]
  refine ⟨32775218112471440816872975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43700290816628587755830633 32775218112471440816872975)
  ·
    refine ⟨49162827168707161225309463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32775218112471440816872975 49162827168707161225309463)
    ·
      refine ⟨73744240753060741837964195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49162827168707161225309463 73744240753060741837964195)
      ·
        refine ⟨110616361129591112756946293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73744240753060741837964195 110616361129591112756946293)
        ·
          refine ⟨10370283855899166820963715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110616361129591112756946293 10370283855899166820963715)
          ·
            refine ⟨15555425783848750231445573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10370283855899166820963715 15555425783848750231445573)
            ·
              refine ⟨2916642334471640668396045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15555425783848750231445573 2916642334471640668396045)
              ·
                refine ⟨1093740875426865250648517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2916642334471640668396045 1093740875426865250648517)
                ·
                  refine ⟨205076414142537234496597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1093740875426865250648517 205076414142537234496597)
                  ·
                    rfl

theorem cell22_1797232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 3, 4].length) (baseStart_1797232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1797232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1797232 prefixEnd_1797232 := by exact prefixLift 1797232
  have htrace : WordTrace (prefixWord ++ tailWord_1797232) baseStart_1797232 baseEnd_1797232 := by
    simpa [prefixWord, tailWord_1797232, baseEnd_1797232] using wordTrace_append hprefix tailTrace_1797232
  have hstable : (prefixWord ++ tailWord_1797232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797232).length < 2 ^ (prefixWord ++ tailWord_1797232).sum := by decide
  have hdescent : baseEnd_1797232 < baseStart_1797232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797245 : List Nat := [1, 4, 1, 1, 3, 1, 2, 1, 4, 4]
def baseStart_1797245 : Nat := 118140960795 + 1797245 * 2 ^ 59
def prefixEnd_1797245 : Nat := 4983230072969 + 3 ^ 40 * 1797245 * 2
def baseEnd_1797245 : Nat := 615233692593284002914751

theorem tailTrace_1797245 : CollatzResearch.WordTrace tailWord_1797245 prefixEnd_1797245 615233692593284002914751 := by
  unfold tailWord_1797245
  simp only [CollatzResearch.WordTrace]
  refine ⟨65550910373895784853969189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43700606915930523235979459 65550910373895784853969189)
  ·
    refine ⟨12290795695105459660119223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65550910373895784853969189 12290795695105459660119223)
    ·
      refine ⟨18436193542658189490178835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12290795695105459660119223 18436193542658189490178835)
      ·
        refine ⟨27654290313987284235268253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18436193542658189490178835 27654290313987284235268253)
        ·
          refine ⟨10370358867745231588225595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27654290313987284235268253 10370358867745231588225595)
          ·
            refine ⟨15555538301617847382338393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10370358867745231588225595 15555538301617847382338393)
            ·
              refine ⟨11666653726213385536753795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15555538301617847382338393 11666653726213385536753795)
              ·
                refine ⟨17499980589320078305130693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11666653726213385536753795 17499980589320078305130693)
                ·
                  refine ⟨3281246360497514682212005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17499980589320078305130693 3281246360497514682212005)
                  ·
                    refine ⟨615233692593284002914751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3281246360497514682212005 615233692593284002914751)
                    ·
                      rfl

theorem cell22_1797245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_1797245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1797245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1797245 prefixEnd_1797245 := by exact prefixLift 1797245
  have htrace : WordTrace (prefixWord ++ tailWord_1797245) baseStart_1797245 baseEnd_1797245 := by
    simpa [prefixWord, tailWord_1797245, baseEnd_1797245] using wordTrace_append hprefix tailTrace_1797245
  have hstable : (prefixWord ++ tailWord_1797245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797245).length < 2 ^ (prefixWord ++ tailWord_1797245).sum := by decide
  have hdescent : baseEnd_1797245 < baseStart_1797245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797305 : List Nat := [1, 2, 1, 4, 1, 3, 2, 1, 7]
def baseStart_1797305 : Nat := 118140960795 + 1797305 * 2 ^ 59
def prefixEnd_1797305 : Nat := 4983230072969 + 3 ^ 40 * 1797305 * 2
def baseEnd_1797305 : Nat := 205084743939821282138189

theorem tailTrace_1797305 : CollatzResearch.WordTrace tailWord_1797305 prefixEnd_1797305 205084743939821282138189 := by
  unfold tailWord_1797305
  simp only [CollatzResearch.WordTrace]
  refine ⟨65553098753678415101153369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43702065835785610067435579 65553098753678415101153369)
  ·
    refine ⟨49164824065258811325865027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65553098753678415101153369 49164824065258811325865027)
    ·
      refine ⟨73747236097888216988797541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49164824065258811325865027 73747236097888216988797541)
      ·
        refine ⟨13827606768354040685399539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73747236097888216988797541 13827606768354040685399539)
        ·
          refine ⟨20741410152531061028099309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13827606768354040685399539 20741410152531061028099309)
          ·
            refine ⟨7778028807199147885537241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20741410152531061028099309 7778028807199147885537241)
            ·
              refine ⟨5833521605399360914152931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7778028807199147885537241 5833521605399360914152931)
              ·
                refine ⟨8750282408099041371229397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5833521605399360914152931 8750282408099041371229397)
                ·
                  refine ⟨205084743939821282138189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8750282408099041371229397 205084743939821282138189)
                  ·
                    rfl

theorem cell22_1797305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 7].length) (baseStart_1797305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1797305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1797305 prefixEnd_1797305 := by exact prefixLift 1797305
  have htrace : WordTrace (prefixWord ++ tailWord_1797305) baseStart_1797305 baseEnd_1797305 := by
    simpa [prefixWord, tailWord_1797305, baseEnd_1797305] using wordTrace_append hprefix tailTrace_1797305
  have hstable : (prefixWord ++ tailWord_1797305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797305).length < 2 ^ (prefixWord ++ tailWord_1797305).sum := by decide
  have hdescent : baseEnd_1797305 < baseStart_1797305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797309 : List Nat := [1, 4, 1, 2, 1, 1, 2, 6, 1, 3]
def baseStart_1797309 : Nat := 118140960795 + 1797309 * 2 ^ 59
def prefixEnd_1797309 : Nat := 4983230072969 + 3 ^ 40 * 1797309 * 2
def baseEnd_1797309 : Nat := 615255601101209169314555

theorem tailTrace_1797309 : CollatzResearch.WordTrace tailWord_1797309 prefixEnd_1797309 615255601101209169314555 := by
  unfold tailWord_1797309
  simp only [CollatzResearch.WordTrace]
  refine ⟨65553244645663923784298981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43702163097109282522865987 65553244645663923784298981)
  ·
    refine ⟨12291233371061985709556059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65553244645663923784298981 12291233371061985709556059)
    ·
      refine ⟨18436850056592978564334089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12291233371061985709556059 18436850056592978564334089)
      ·
        refine ⟨13827637542444733923250567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18436850056592978564334089 13827637542444733923250567)
        ·
          refine ⟨20741456313667100884875851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13827637542444733923250567 20741456313667100884875851)
          ·
            refine ⟨31112184470500651327313777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20741456313667100884875851 31112184470500651327313777)
            ·
              refine ⟨23334138352875488495485333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31112184470500651327313777 23334138352875488495485333)
              ·
                refine ⟨1093787735291038523225875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23334138352875488495485333 1093787735291038523225875)
                ·
                  refine ⟨1640681602936557784838813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1093787735291038523225875 1640681602936557784838813)
                  ·
                    refine ⟨615255601101209169314555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1640681602936557784838813 615255601101209169314555)
                    ·
                      rfl

theorem cell22_1797309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 6, 1, 3].length) (baseStart_1797309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1797309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1797309 prefixEnd_1797309 := by exact prefixLift 1797309
  have htrace : WordTrace (prefixWord ++ tailWord_1797309) baseStart_1797309 baseEnd_1797309 := by
    simpa [prefixWord, tailWord_1797309, baseEnd_1797309] using wordTrace_append hprefix tailTrace_1797309
  have hstable : (prefixWord ++ tailWord_1797309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797309).length < 2 ^ (prefixWord ++ tailWord_1797309).sum := by decide
  have hdescent : baseEnd_1797309 < baseStart_1797309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797320 : List Nat := [2, 1, 3, 1, 2, 1, 2, 3, 2, 5]
def baseStart_1797320 : Nat := 118140960795 + 1797320 * 2 ^ 59
def prefixEnd_1797320 : Nat := 4983230072969 + 3 ^ 40 * 1797320 * 2
def baseEnd_1797320 : Nat := 615259366626008807289521

theorem tailTrace_1797320 : CollatzResearch.WordTrace tailWord_1797320 prefixEnd_1797320 615259366626008807289521 := by
  unfold tailWord_1797320
  simp only [CollatzResearch.WordTrace]
  refine ⟨32776822924312036331474707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43702430565749381775299609 32776822924312036331474707)
  ·
    refine ⟨49165234386468054497212061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32776822924312036331474707 49165234386468054497212061)
    ·
      refine ⟨18436962894925520436454523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49165234386468054497212061 18436962894925520436454523)
      ·
        refine ⟨27655444342388280654681785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18436962894925520436454523 27655444342388280654681785)
        ·
          refine ⟨20741583256791210491011339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27655444342388280654681785 20741583256791210491011339)
          ·
            refine ⟨31112374885186815736517009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20741583256791210491011339 31112374885186815736517009)
            ·
              refine ⟨23334281163890111802387757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31112374885186815736517009 23334281163890111802387757)
              ·
                refine ⟨8750355436458791925895409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23334281163890111802387757 8750355436458791925895409)
                ·
                  refine ⟨6562766577344093944421557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8750355436458791925895409 6562766577344093944421557)
                  ·
                    refine ⟨615259366626008807289521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6562766577344093944421557 615259366626008807289521)
                    ·
                      rfl

theorem cell22_1797320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_1797320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1797320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1797320 prefixEnd_1797320 := by exact prefixLift 1797320
  have htrace : WordTrace (prefixWord ++ tailWord_1797320) baseStart_1797320 baseEnd_1797320 := by
    simpa [prefixWord, tailWord_1797320, baseEnd_1797320] using wordTrace_append hprefix tailTrace_1797320
  have hstable : (prefixWord ++ tailWord_1797320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797320).length < 2 ^ (prefixWord ++ tailWord_1797320).sum := by decide
  have hdescent : baseEnd_1797320 < baseStart_1797320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797322 : List Nat := [3, 1, 2, 1, 3, 3, 1, 3, 5]
def baseStart_1797322 : Nat := 118140960795 + 1797322 * 2 ^ 59
def prefixEnd_1797322 : Nat := 4983230072969 + 3 ^ 40 * 1797322 * 2
def baseEnd_1797322 : Nat := 205086683755627156246505

theorem tailTrace_1797322 : CollatzResearch.WordTrace tailWord_1797322 prefixEnd_1797322 205086683755627156246505 := by
  unfold tailWord_1797322
  simp only [CollatzResearch.WordTrace]
  refine ⟨16388429698654206751130555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43702479196411218003014813 16388429698654206751130555)
  ·
    refine ⟨24582644547981310126695833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16388429698654206751130555 24582644547981310126695833)
    ·
      refine ⟨18436983410985982595021875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24582644547981310126695833 18436983410985982595021875)
      ·
        refine ⟨27655475116478973892532813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18436983410985982595021875 27655475116478973892532813)
        ·
          refine ⟨10370803168679615209699805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27655475116478973892532813 10370803168679615209699805)
          ·
            refine ⟨3889051188254855703637427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10370803168679615209699805 3889051188254855703637427)
            ·
              refine ⟨5833576782382283555456141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3889051188254855703637427 5833576782382283555456141)
              ·
                refine ⟨2187591293393356333296053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5833576782382283555456141 2187591293393356333296053)
                ·
                  refine ⟨205086683755627156246505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2187591293393356333296053 205086683755627156246505)
                  ·
                    rfl

theorem cell22_1797322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3, 5].length) (baseStart_1797322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1797322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1797322 prefixEnd_1797322 := by exact prefixLift 1797322
  have htrace : WordTrace (prefixWord ++ tailWord_1797322) baseStart_1797322 baseEnd_1797322 := by
    simpa [prefixWord, tailWord_1797322, baseEnd_1797322] using wordTrace_append hprefix tailTrace_1797322
  have hstable : (prefixWord ++ tailWord_1797322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797322).length < 2 ^ (prefixWord ++ tailWord_1797322).sum := by decide
  have hdescent : baseEnd_1797322 < baseStart_1797322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797367 : List Nat := [1, 1, 3, 1, 1, 1, 2, 8, 4]
def baseStart_1797367 : Nat := 118140960795 + 1797367 * 2 ^ 59
def prefixEnd_1797367 : Nat := 4983230072969 + 3 ^ 40 * 1797367 * 2
def baseEnd_1797367 : Nat := 205091818562172117121459

theorem tailTrace_1797367 : CollatzResearch.WordTrace tailWord_1797367 prefixEnd_1797367 205091818562172117121459 := by
  unfold tailWord_1797367
  simp only [CollatzResearch.WordTrace]
  refine ⟨65555360079453799689910355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43703573386302533126606903 65555360079453799689910355)
  ·
    refine ⟨98333040119180699534865533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65555360079453799689910355 98333040119180699534865533)
    ·
      refine ⟨36874890044692762325574575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98333040119180699534865533 36874890044692762325574575)
      ·
        refine ⟨55312335067039143488361863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36874890044692762325574575 55312335067039143488361863)
        ·
          refine ⟨82968502600558715232542795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55312335067039143488361863 82968502600558715232542795)
          ·
            refine ⟨124452753900838072848814193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82968502600558715232542795 124452753900838072848814193)
            ·
              refine ⟨93339565425628554636610645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124452753900838072848814193 93339565425628554636610645)
              ·
                refine ⟨1093823032331584624647781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 93339565425628554636610645 1093823032331584624647781)
                ·
                  refine ⟨205091818562172117121459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1093823032331584624647781 205091818562172117121459)
                  ·
                    rfl

theorem cell22_1797367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 8, 4].length) (baseStart_1797367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1797367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1797367 prefixEnd_1797367 := by exact prefixLift 1797367
  have htrace : WordTrace (prefixWord ++ tailWord_1797367) baseStart_1797367 baseEnd_1797367 := by
    simpa [prefixWord, tailWord_1797367, baseEnd_1797367] using wordTrace_append hprefix tailTrace_1797367
  have hstable : (prefixWord ++ tailWord_1797367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797367).length < 2 ^ (prefixWord ++ tailWord_1797367).sum := by decide
  have hdescent : baseEnd_1797367 < baseStart_1797367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797416 : List Nat := [2, 1, 5, 1, 2, 1, 3, 2, 2, 3]
def baseStart_1797416 : Nat := 118140960795 + 1797416 * 2 ^ 59
def prefixEnd_1797416 : Nat := 4983230072969 + 3 ^ 40 * 1797416 * 2
def baseEnd_1797416 : Nat := 615292229387896556889227

theorem tailTrace_1797416 : CollatzResearch.WordTrace tailWord_1797416 prefixEnd_1797416 615292229387896556889227 := by
  unfold tailWord_1797416
  simp only [CollatzResearch.WordTrace]
  refine ⟨32778573628138140529222051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43704764837517520705629401 32778573628138140529222051)
  ·
    refine ⟨49167860442207210793833077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32778573628138140529222051 49167860442207210793833077)
    ·
      refine ⟨4609486916456926011921851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49167860442207210793833077 4609486916456926011921851)
      ·
        refine ⟨6914230374685389017882777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4609486916456926011921851 6914230374685389017882777)
        ·
          refine ⟨5185672781014041763412083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6914230374685389017882777 5185672781014041763412083)
          ·
            refine ⟨7778509171521062645118125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5185672781014041763412083 7778509171521062645118125)
            ·
              refine ⟨2916940939320398491919297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7778509171521062645118125 2916940939320398491919297)
              ·
                refine ⟨2187705704490298868939473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2916940939320398491919297 2187705704490298868939473)
                ·
                  refine ⟨1640779278367724151704605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2187705704490298868939473 1640779278367724151704605)
                  ·
                    refine ⟨615292229387896556889227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1640779278367724151704605 615292229387896556889227)
                    ·
                      rfl

theorem cell22_1797416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_1797416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1797416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1797416 prefixEnd_1797416 := by exact prefixLift 1797416
  have htrace : WordTrace (prefixWord ++ tailWord_1797416) baseStart_1797416 baseEnd_1797416 := by
    simpa [prefixWord, tailWord_1797416, baseEnd_1797416] using wordTrace_append hprefix tailTrace_1797416
  have hstable : (prefixWord ++ tailWord_1797416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797416).length < 2 ^ (prefixWord ++ tailWord_1797416).sum := by decide
  have hdescent : baseEnd_1797416 < baseStart_1797416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797433 : List Nat := [1, 2, 1, 6, 2, 1, 3, 1, 2, 3]
def baseStart_1797433 : Nat := 118140960795 + 1797433 * 2 ^ 59
def prefixEnd_1797433 : Nat := 4983230072969 + 3 ^ 40 * 1797433 * 2
def baseEnd_1797433 : Nat := 615298048835314179214175

theorem tailTrace_1797433 : CollatzResearch.WordTrace tailWord_1797433 prefixEnd_1797433 615298048835314179214175 := by
  unfold tailWord_1797433
  simp only [CollatzResearch.WordTrace]
  refine ⟨65557767297214692961812953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43705178198143128641208635 65557767297214692961812953)
  ·
    refine ⟨49168325472911019721359715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65557767297214692961812953 49168325472911019721359715)
    ·
      refine ⟨73752488209366529582039573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49168325472911019721359715 73752488209366529582039573)
      ·
        refine ⟨3457147884814056074158105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 73752488209366529582039573 3457147884814056074158105)
        ·
          refine ⟨2592860913610542055618579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3457147884814056074158105 2592860913610542055618579)
          ·
            refine ⟨3889291370415813083427869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2592860913610542055618579 3889291370415813083427869)
            ·
              refine ⟨1458484263905929906285451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3889291370415813083427869 1458484263905929906285451)
              ·
                refine ⟨2187726395858894859428177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1458484263905929906285451 2187726395858894859428177)
                ·
                  refine ⟨1640794796894171144571133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2187726395858894859428177 1640794796894171144571133)
                  ·
                    refine ⟨615298048835314179214175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1640794796894171144571133 615298048835314179214175)
                    ·
                      rfl

theorem cell22_1797433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 1, 2, 3].length) (baseStart_1797433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1797433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1797433 prefixEnd_1797433 := by exact prefixLift 1797433
  have htrace : WordTrace (prefixWord ++ tailWord_1797433) baseStart_1797433 baseEnd_1797433 := by
    simpa [prefixWord, tailWord_1797433, baseEnd_1797433] using wordTrace_append hprefix tailTrace_1797433
  have hstable : (prefixWord ++ tailWord_1797433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797433).length < 2 ^ (prefixWord ++ tailWord_1797433).sum := by decide
  have hdescent : baseEnd_1797433 < baseStart_1797433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797474 : List Nat := [3, 3, 2, 1, 1, 1, 2, 4, 5]
def baseStart_1797474 : Nat := 118140960795 + 1797474 * 2 ^ 59
def prefixEnd_1797474 : Nat := 4983230072969 + 3 ^ 40 * 1797474 * 2
def baseEnd_1797474 : Nat := 205104027991067912979683

theorem tailTrace_1797474 : CollatzResearch.WordTrace tailWord_1797474 prefixEnd_1797474 205104027991067912979683 := by
  unfold tailWord_1797474
  simp only [CollatzResearch.WordTrace]
  refine ⟨16389815672516539241013869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43706175126710771309370317 16389815672516539241013869)
  ·
    refine ⟨6146180877193702215380201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16389815672516539241013869 6146180877193702215380201)
    ·
      refine ⟨4609635657895276661535151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6146180877193702215380201 4609635657895276661535151)
      ·
        refine ⟨6914453486842914992302727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4609635657895276661535151 6914453486842914992302727)
        ·
          refine ⟨10371680230264372488454091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6914453486842914992302727 10371680230264372488454091)
          ·
            refine ⟨15557520345396558732681137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10371680230264372488454091 15557520345396558732681137)
            ·
              refine ⟨11668140259047419049510853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15557520345396558732681137 11668140259047419049510853)
              ·
                refine ⟨2187776298571391071783285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11668140259047419049510853 2187776298571391071783285)
                ·
                  refine ⟨205104027991067912979683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2187776298571391071783285 205104027991067912979683)
                  ·
                    rfl

theorem cell22_1797474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_1797474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1797474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1797474 prefixEnd_1797474 := by exact prefixLift 1797474
  have htrace : WordTrace (prefixWord ++ tailWord_1797474) baseStart_1797474 baseEnd_1797474 := by
    simpa [prefixWord, tailWord_1797474, baseEnd_1797474] using wordTrace_append hprefix tailTrace_1797474
  have hstable : (prefixWord ++ tailWord_1797474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797474).length < 2 ^ (prefixWord ++ tailWord_1797474).sum := by decide
  have hdescent : baseEnd_1797474 < baseStart_1797474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797487 : List Nat := [1, 1, 2, 1, 3, 1, 4, 2, 3, 4]
def baseStart_1797487 : Nat := 118140960795 + 1797487 * 2 ^ 59
def prefixEnd_1797487 : Nat := 4983230072969 + 3 ^ 40 * 1797487 * 2
def baseEnd_1797487 : Nat := 615316534138876038364009

theorem tailTrace_1797487 : CollatzResearch.WordTrace tailWord_1797487 prefixEnd_1797487 615316534138876038364009 := by
  unfold tailWord_1797487
  simp only [CollatzResearch.WordTrace]
  refine ⟨65559736839019060184278715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43706491226012706789519143 65559736839019060184278715)
  ·
    refine ⟨98339605258528590276418073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65559736839019060184278715 98339605258528590276418073)
    ·
      refine ⟨73754703943896442707313555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98339605258528590276418073 73754703943896442707313555)
      ·
        refine ⟨110632055915844664060970333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73754703943896442707313555 110632055915844664060970333)
        ·
          refine ⟨41487020968441749022863875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110632055915844664060970333 41487020968441749022863875)
          ·
            refine ⟨62230531452662623534295813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41487020968441749022863875 62230531452662623534295813)
            ·
              refine ⟨11668224647374241912680465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62230531452662623534295813 11668224647374241912680465)
              ·
                refine ⟨8751168485530681434510349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11668224647374241912680465 8751168485530681434510349)
                ·
                  refine ⟨3281688182074005537941381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8751168485530681434510349 3281688182074005537941381)
                  ·
                    refine ⟨615316534138876038364009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3281688182074005537941381 615316534138876038364009)
                    ·
                      rfl

theorem cell22_1797487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 4].length) (baseStart_1797487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1797487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1797487 prefixEnd_1797487 := by exact prefixLift 1797487
  have htrace : WordTrace (prefixWord ++ tailWord_1797487) baseStart_1797487 baseEnd_1797487 := by
    simpa [prefixWord, tailWord_1797487, baseEnd_1797487] using wordTrace_append hprefix tailTrace_1797487
  have hstable : (prefixWord ++ tailWord_1797487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797487).length < 2 ^ (prefixWord ++ tailWord_1797487).sum := by decide
  have hdescent : baseEnd_1797487 < baseStart_1797487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797669 : List Nat := [1, 3, 1, 2, 2, 1, 1, 5, 1, 5]
def baseStart_1797669 : Nat := 118140960795 + 1797669 * 2 ^ 59
def prefixEnd_1797669 : Nat := 4983230072969 + 3 ^ 40 * 1797669 * 2
def baseEnd_1797669 : Nat := 615378836458288230313451

theorem tailTrace_1797669 : CollatzResearch.WordTrace tailWord_1797669 prefixEnd_1797669 615378836458288230313451 := by
  unfold tailWord_1797669
  simp only [CollatzResearch.WordTrace]
  refine ⟨65566374924359705267404061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43710916616239803511602707 65566374924359705267404061)
  ·
    refine ⟨24587390596634889475276523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65566374924359705267404061 24587390596634889475276523)
    ·
      refine ⟨36881085894952334212914785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24587390596634889475276523 36881085894952334212914785)
      ·
        refine ⟨27660814421214250659686089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36881085894952334212914785 27660814421214250659686089)
        ·
          refine ⟨20745610815910687994764567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27660814421214250659686089 20745610815910687994764567)
          ·
            refine ⟨31118416223866031992146851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20745610815910687994764567 31118416223866031992146851)
            ·
              refine ⟨46677624335799047988220277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31118416223866031992146851 46677624335799047988220277)
              ·
                refine ⟨4376027281481160748895651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46677624335799047988220277 4376027281481160748895651)
                ·
                  refine ⟨6564040922221741123343477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4376027281481160748895651 6564040922221741123343477)
                  ·
                    refine ⟨615378836458288230313451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6564040922221741123343477 615378836458288230313451)
                    ·
                      rfl

theorem cell22_1797669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 5].length) (baseStart_1797669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1797669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1797669 prefixEnd_1797669 := by exact prefixLift 1797669
  have htrace : WordTrace (prefixWord ++ tailWord_1797669) baseStart_1797669 baseEnd_1797669 := by
    simpa [prefixWord, tailWord_1797669, baseEnd_1797669] using wordTrace_append hprefix tailTrace_1797669
  have hstable : (prefixWord ++ tailWord_1797669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797669).length < 2 ^ (prefixWord ++ tailWord_1797669).sum := by decide
  have hdescent : baseEnd_1797669 < baseStart_1797669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797729 : List Nat := [1, 2, 3, 1, 1, 3, 1, 2, 2, 6]
def baseStart_1797729 : Nat := 118140960795 + 1797729 * 2 ^ 59
def prefixEnd_1797729 : Nat := 4983230072969 + 3 ^ 40 * 1797729 * 2
def baseEnd_1797729 : Nat := 615399375684468073813267

theorem tailTrace_1797729 : CollatzResearch.WordTrace tailWord_1797729 prefixEnd_1797729 615399375684468073813267 := by
  unfold tailWord_1797729
  simp only [CollatzResearch.WordTrace]
  refine ⟨65568563304142335514588241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43712375536094890343058827 65568563304142335514588241)
  ·
    refine ⟨49176422478106751635941181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65568563304142335514588241 49176422478106751635941181)
    ·
      refine ⟨18441158429290031863477943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49176422478106751635941181 18441158429290031863477943)
      ·
        refine ⟨27661737643935047795216915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18441158429290031863477943 27661737643935047795216915)
        ·
          refine ⟨41492606465902571692825373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27661737643935047795216915 41492606465902571692825373)
          ·
            refine ⟨15559727424713464384809515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41492606465902571692825373 15559727424713464384809515)
            ·
              refine ⟨23339591137070196577214273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15559727424713464384809515 23339591137070196577214273)
              ·
                refine ⟨17504693352802647432910705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23339591137070196577214273 17504693352802647432910705)
                ·
                  refine ⟨13128520014601985574683029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17504693352802647432910705 13128520014601985574683029)
                  ·
                    refine ⟨615399375684468073813267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13128520014601985574683029 615399375684468073813267)
                    ·
                      rfl

theorem cell22_1797729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_1797729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1797729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1797729 prefixEnd_1797729 := by exact prefixLift 1797729
  have htrace : WordTrace (prefixWord ++ tailWord_1797729) baseStart_1797729 baseEnd_1797729 := by
    simpa [prefixWord, tailWord_1797729, baseEnd_1797729] using wordTrace_append hprefix tailTrace_1797729
  have hstable : (prefixWord ++ tailWord_1797729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797729).length < 2 ^ (prefixWord ++ tailWord_1797729).sum := by decide
  have hdescent : baseEnd_1797729 < baseStart_1797729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797731 : List Nat := [1, 1, 1, 5, 1, 3, 1, 1, 5, 3]
def baseStart_1797731 : Nat := 118140960795 + 1797731 * 2 ^ 59
def prefixEnd_1797731 : Nat := 4983230072969 + 3 ^ 40 * 1797731 * 2
def baseEnd_1797731 : Nat := 615400060325340735263261

theorem tailTrace_1797731 : CollatzResearch.WordTrace tailWord_1797731 prefixEnd_1797731 615400060325340735263261 := by
  unfold tailWord_1797731
  simp only [CollatzResearch.WordTrace]
  refine ⟨65568636250135089856161047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43712424166756726570774031 65568636250135089856161047)
  ·
    refine ⟨98352954375202634784241571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65568636250135089856161047 98352954375202634784241571)
    ·
      refine ⟨147529431562803952176362357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98352954375202634784241571 147529431562803952176362357)
      ·
        refine ⟨13830884209012870516533971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 147529431562803952176362357 13830884209012870516533971)
        ·
          refine ⟨20746326313519305774800957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13830884209012870516533971 20746326313519305774800957)
          ·
            refine ⟨7779872367569739665550359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20746326313519305774800957 7779872367569739665550359)
            ·
              refine ⟨11669808551354609498325539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7779872367569739665550359 11669808551354609498325539)
              ·
                refine ⟨17504712827031914247488309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11669808551354609498325539 17504712827031914247488309)
                ·
                  refine ⟨1641066827534241960702029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17504712827031914247488309 1641066827534241960702029)
                  ·
                    refine ⟨615400060325340735263261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1641066827534241960702029 615400060325340735263261)
                    ·
                      rfl

theorem cell22_1797731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 5, 3].length) (baseStart_1797731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1797731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1797731 prefixEnd_1797731 := by exact prefixLift 1797731
  have htrace : WordTrace (prefixWord ++ tailWord_1797731) baseStart_1797731 baseEnd_1797731 := by
    simpa [prefixWord, tailWord_1797731, baseEnd_1797731] using wordTrace_append hprefix tailTrace_1797731
  have hstable : (prefixWord ++ tailWord_1797731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797731).length < 2 ^ (prefixWord ++ tailWord_1797731).sum := by decide
  have hdescent : baseEnd_1797731 < baseStart_1797731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797761 : List Nat := [1, 2, 4, 2, 1, 3, 1, 1, 7]
def baseStart_1797761 : Nat := 118140960795 + 1797761 * 2 ^ 59
def prefixEnd_1797761 : Nat := 4983230072969 + 3 ^ 40 * 1797761 * 2
def baseEnd_1797761 : Nat := 205136776646143552337723

theorem tailTrace_1797761 : CollatzResearch.WordTrace tailWord_1797761 prefixEnd_1797761 205136776646143552337723 := by
  unfold tailWord_1797761
  simp only [CollatzResearch.WordTrace]
  refine ⟨65569730440026404979753137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43713153626684269986502091 65569730440026404979753137)
  ·
    refine ⟨49177297830019803734814853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65569730440026404979753137 49177297830019803734814853)
    ·
      refine ⟨9220743343128713200277785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49177297830019803734814853 9220743343128713200277785)
      ·
        refine ⟨6915557507346534900208339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9220743343128713200277785 6915557507346534900208339)
        ·
          refine ⟨10373336261019802350312509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6915557507346534900208339 10373336261019802350312509)
          ·
            refine ⟨3890001097882425881367191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10373336261019802350312509 3890001097882425881367191)
            ·
              refine ⟨5835001646823638822050787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3890001097882425881367191 5835001646823638822050787)
              ·
                refine ⟨8752502470235458233076181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5835001646823638822050787 8752502470235458233076181)
                ·
                  refine ⟨205136776646143552337723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8752502470235458233076181 205136776646143552337723)
                  ·
                    rfl

theorem cell22_1797761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 7].length) (baseStart_1797761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1797761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1797761 prefixEnd_1797761 := by exact prefixLift 1797761
  have htrace : WordTrace (prefixWord ++ tailWord_1797761) baseStart_1797761 baseEnd_1797761 := by
    simpa [prefixWord, tailWord_1797761, baseEnd_1797761] using wordTrace_append hprefix tailTrace_1797761
  have hstable : (prefixWord ++ tailWord_1797761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797761).length < 2 ^ (prefixWord ++ tailWord_1797761).sum := by decide
  have hdescent : baseEnd_1797761 < baseStart_1797761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797928 : List Nat := [2, 1, 5, 1, 1, 2, 1, 2, 2, 5]
def baseStart_1797928 : Nat := 118140960795 + 1797928 * 2 ^ 59
def prefixEnd_1797928 : Nat := 4983230072969 + 3 ^ 40 * 1797928 * 2
def baseEnd_1797928 : Nat := 615467497451297888087657

theorem tailTrace_1797928 : CollatzResearch.WordTrace tailWord_1797928 prefixEnd_1797928 615467497451297888087657 := by
  unfold tailWord_1797928
  simp only [CollatzResearch.WordTrace]
  refine ⟨32787910715210696250541219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43717214286947595000721625 32787910715210696250541219)
  ·
    refine ⟨49181866072816044375811829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32787910715210696250541219 49181866072816044375811829)
    ·
      refine ⟨4610799944326504160232359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49181866072816044375811829 4610799944326504160232359)
      ·
        refine ⟨6916199916489756240348539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4610799944326504160232359 6916199916489756240348539)
        ·
          refine ⟨10374299874734634360522809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6916199916489756240348539 10374299874734634360522809)
          ·
            refine ⟨7780724906050975770392107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10374299874734634360522809 7780724906050975770392107)
            ·
              refine ⟨11671087359076463655588161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7780724906050975770392107 11671087359076463655588161)
              ·
                refine ⟨8753315519307347741691121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11671087359076463655588161 8753315519307347741691121)
                ·
                  refine ⟨6564986639480510806268341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8753315519307347741691121 6564986639480510806268341)
                  ·
                    refine ⟨615467497451297888087657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6564986639480510806268341 615467497451297888087657)
                    ·
                      rfl

theorem cell22_1797928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_1797928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1797928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1797928 prefixEnd_1797928 := by exact prefixLift 1797928
  have htrace : WordTrace (prefixWord ++ tailWord_1797928) baseStart_1797928 baseEnd_1797928 := by
    simpa [prefixWord, tailWord_1797928, baseEnd_1797928] using wordTrace_append hprefix tailTrace_1797928
  have hstable : (prefixWord ++ tailWord_1797928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797928).length < 2 ^ (prefixWord ++ tailWord_1797928).sum := by decide
  have hdescent : baseEnd_1797928 < baseStart_1797928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797960 : List Nat := [2, 1, 3, 1, 1, 5, 2, 2, 1, 4]
def baseStart_1797960 : Nat := 118140960795 + 1797960 * 2 ^ 59
def prefixEnd_1797960 : Nat := 4983230072969 + 3 ^ 40 * 1797960 * 2
def baseEnd_1797960 : Nat := 615478451705260471287559

theorem tailTrace_1797960 : CollatzResearch.WordTrace tailWord_1797960 prefixEnd_1797960 615478451705260471287559 := by
  unfold tailWord_1797960
  simp only [CollatzResearch.WordTrace]
  refine ⟨32788494283152730983123667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43717992377536974644164889 32788494283152730983123667)
  ·
    refine ⟨49182741424729096474685501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32788494283152730983123667 49182741424729096474685501)
    ·
      refine ⟨18443528034273411178007063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49182741424729096474685501 18443528034273411178007063)
      ·
        refine ⟨27665292051410116767010595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18443528034273411178007063 27665292051410116767010595)
        ·
          refine ⟨41497938077115175150515893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27665292051410116767010595 41497938077115175150515893)
          ·
            refine ⟨3890431694729547670360865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41497938077115175150515893 3890431694729547670360865)
            ·
              refine ⟨2917823771047160752770649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3890431694729547670360865 2917823771047160752770649)
              ·
                refine ⟨2188367828285370564577987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2917823771047160752770649 2188367828285370564577987)
                ·
                  refine ⟨3282551742428055846866981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2188367828285370564577987 3282551742428055846866981)
                  ·
                    refine ⟨615478451705260471287559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3282551742428055846866981 615478451705260471287559)
                    ·
                      rfl

theorem cell22_1797960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_1797960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1797960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1797960 prefixEnd_1797960 := by exact prefixLift 1797960
  have htrace : WordTrace (prefixWord ++ tailWord_1797960) baseStart_1797960 baseEnd_1797960 := by
    simpa [prefixWord, tailWord_1797960, baseEnd_1797960] using wordTrace_append hprefix tailTrace_1797960
  have hstable : (prefixWord ++ tailWord_1797960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797960).length < 2 ^ (prefixWord ++ tailWord_1797960).sum := by decide
  have hdescent : baseEnd_1797960 < baseStart_1797960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797992 : List Nat := [2, 1, 4, 2, 1, 1, 5, 2, 4]
def baseStart_1797992 : Nat := 118140960795 + 1797992 * 2 ^ 59
def prefixEnd_1797992 : Nat := 4983230072969 + 3 ^ 40 * 1797992 * 2
def baseEnd_1797992 : Nat := 205163135319741018162487

theorem tailTrace_1797992 : CollatzResearch.WordTrace tailWord_1797992 prefixEnd_1797992 205163135319741018162487 := by
  unfold tailWord_1797992
  simp only [CollatzResearch.WordTrace]
  refine ⟨32789077851094765715706115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43718770468126354287608153 32789077851094765715706115)
  ·
    refine ⟨49183616776642148573559173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32789077851094765715706115 49183616776642148573559173)
    ·
      refine ⟨9221928145620402857542345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49183616776642148573559173 9221928145620402857542345)
      ·
        refine ⟨6916446109215302143156759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9221928145620402857542345 6916446109215302143156759)
        ·
          refine ⟨10374669163822953214735139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6916446109215302143156759 10374669163822953214735139)
          ·
            refine ⟨15562003745734429822102709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10374669163822953214735139 15562003745734429822102709)
            ·
              refine ⟨1458937851162602795822129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15562003745734429822102709 1458937851162602795822129)
              ·
                refine ⟨1094203388371952096866597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1458937851162602795822129 1094203388371952096866597)
                ·
                  refine ⟨205163135319741018162487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1094203388371952096866597 205163135319741018162487)
                  ·
                    rfl

theorem cell22_1797992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 2, 4].length) (baseStart_1797992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1797992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1797992 prefixEnd_1797992 := by exact prefixLift 1797992
  have htrace : WordTrace (prefixWord ++ tailWord_1797992) baseStart_1797992 baseEnd_1797992 := by
    simpa [prefixWord, tailWord_1797992, baseEnd_1797992] using wordTrace_append hprefix tailTrace_1797992
  have hstable : (prefixWord ++ tailWord_1797992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797992).length < 2 ^ (prefixWord ++ tailWord_1797992).sum := by decide
  have hdescent : baseEnd_1797992 < baseStart_1797992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798063 : List Nat := [1, 1, 2, 1, 2, 2, 5, 1, 2, 5]
def baseStart_1798063 : Nat := 118140960795 + 1798063 * 2 ^ 59
def prefixEnd_1798063 : Nat := 4983230072969 + 3 ^ 40 * 1798063 * 2
def baseEnd_1798063 : Nat := 615513710710202535962243

theorem tailTrace_1798063 : CollatzResearch.WordTrace tailWord_1798063 prefixEnd_1798063 615513710710202535962243 := by
  unfold tailWord_1798063
  simp only [CollatzResearch.WordTrace]
  refine ⟨65580745284932310557246843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43720496856621540371497895 65580745284932310557246843)
  ·
    refine ⟨98371117927398465835870265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65580745284932310557246843 98371117927398465835870265)
    ·
      refine ⟨73778338445548849376902699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98371117927398465835870265 73778338445548849376902699)
      ·
        refine ⟨110667507668323274065354049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73778338445548849376902699 110667507668323274065354049)
        ·
          refine ⟨83000630751242455549015537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110667507668323274065354049 83000630751242455549015537)
          ·
            refine ⟨62250473063431841661761653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83000630751242455549015537 62250473063431841661761653)
            ·
              refine ⟨5835981849696735155790155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62250473063431841661761653 5835981849696735155790155)
              ·
                refine ⟨8753972774545102733685233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5835981849696735155790155 8753972774545102733685233)
                ·
                  refine ⟨6565479580908827050263925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8753972774545102733685233 6565479580908827050263925)
                  ·
                    refine ⟨615513710710202535962243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6565479580908827050263925 615513710710202535962243)
                    ·
                      rfl

theorem cell22_1798063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 5].length) (baseStart_1798063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1798063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1798063 prefixEnd_1798063 := by exact prefixLift 1798063
  have htrace : WordTrace (prefixWord ++ tailWord_1798063) baseStart_1798063 baseEnd_1798063 := by
    simpa [prefixWord, tailWord_1798063, baseEnd_1798063] using wordTrace_append hprefix tailTrace_1798063
  have hstable : (prefixWord ++ tailWord_1798063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798063).length < 2 ^ (prefixWord ++ tailWord_1798063).sum := by decide
  have hdescent : baseEnd_1798063 < baseStart_1798063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798065 : List Nat := [1, 2, 2, 4, 2, 1, 2, 3, 5]
def baseStart_1798065 : Nat := 118140960795 + 1798065 * 2 ^ 59
def prefixEnd_1798065 : Nat := 4983230072969 + 3 ^ 40 * 1798065 * 2
def baseEnd_1798065 : Nat := 205171465117025065804079

theorem tailTrace_1798065 : CollatzResearch.WordTrace tailWord_1798065 prefixEnd_1798065 205171465117025065804079 := by
  unfold tailWord_1798065
  simp only [CollatzResearch.WordTrace]
  refine ⟨65580818230925064898819649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43720545487283376599213099 65580818230925064898819649)
  ·
    refine ⟨49185613673193798674114737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65580818230925064898819649 49185613673193798674114737)
    ·
      refine ⟨36889210254895349005586053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49185613673193798674114737 36889210254895349005586053)
      ·
        refine ⟨6916726922792877938547385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36889210254895349005586053 6916726922792877938547385)
        ·
          refine ⟨5187545192094658453910539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6916726922792877938547385 5187545192094658453910539)
          ·
            refine ⟨7781317788141987680865809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5187545192094658453910539 7781317788141987680865809)
            ·
              refine ⟨5835988341106490760649357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7781317788141987680865809 5835988341106490760649357)
              ·
                refine ⟨2188495627914934035243509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5835988341106490760649357 2188495627914934035243509)
                ·
                  refine ⟨205171465117025065804079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2188495627914934035243509 205171465117025065804079)
                  ·
                    rfl

theorem cell22_1798065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3, 5].length) (baseStart_1798065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1798065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1798065 prefixEnd_1798065 := by exact prefixLift 1798065
  have htrace : WordTrace (prefixWord ++ tailWord_1798065) baseStart_1798065 baseEnd_1798065 := by
    simpa [prefixWord, tailWord_1798065, baseEnd_1798065] using wordTrace_append hprefix tailTrace_1798065
  have hstable : (prefixWord ++ tailWord_1798065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798065).length < 2 ^ (prefixWord ++ tailWord_1798065).sum := by decide
  have hdescent : baseEnd_1798065 < baseStart_1798065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798095 : List Nat := [1, 1, 2, 1, 1, 5, 3, 3, 1, 4]
def baseStart_1798095 : Nat := 118140960795 + 1798095 * 2 ^ 59
def prefixEnd_1798095 : Nat := 4983230072969 + 3 ^ 40 * 1798095 * 2
def baseEnd_1798095 : Nat := 615524664964165119162145

theorem tailTrace_1798095 : CollatzResearch.WordTrace tailWord_1798095 prefixEnd_1798095 615524664964165119162145 := by
  unfold tailWord_1798095
  simp only [CollatzResearch.WordTrace]
  refine ⟨65581912420816380022411739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43721274947210920014941159 65581912420816380022411739)
  ·
    refine ⟨98372868631224570033617609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65581912420816380022411739 98372868631224570033617609)
    ·
      refine ⟨73779651473418427525213207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98372868631224570033617609 73779651473418427525213207)
      ·
        refine ⟨110669477210127641287819811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73779651473418427525213207 110669477210127641287819811)
        ·
          refine ⟨166004215815191461931729717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110669477210127641287819811 166004215815191461931729717)
          ·
            refine ⟨15562895232674199556099661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 166004215815191461931729717 15562895232674199556099661)
            ·
              refine ⟨5836085712252824833537373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15562895232674199556099661 5836085712252824833537373)
              ·
                refine ⟨2188532142094809312576515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5836085712252824833537373 2188532142094809312576515)
                ·
                  refine ⟨3282798213142213968864773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2188532142094809312576515 3282798213142213968864773)
                  ·
                    refine ⟨615524664964165119162145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3282798213142213968864773 615524664964165119162145)
                    ·
                      rfl

theorem cell22_1798095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3, 1, 4].length) (baseStart_1798095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1798095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1798095 prefixEnd_1798095 := by exact prefixLift 1798095
  have htrace : WordTrace (prefixWord ++ tailWord_1798095) baseStart_1798095 baseEnd_1798095 := by
    simpa [prefixWord, tailWord_1798095, baseEnd_1798095] using wordTrace_append hprefix tailTrace_1798095
  have hstable : (prefixWord ++ tailWord_1798095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798095).length < 2 ^ (prefixWord ++ tailWord_1798095).sum := by decide
  have hdescent : baseEnd_1798095 < baseStart_1798095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798140 : List Nat := [2, 2, 2, 1, 2, 2, 2, 3, 2, 4]
def baseStart_1798140 : Nat := 118140960795 + 1798140 * 2 ^ 59
def prefixEnd_1798140 : Nat := 4983230072969 + 3 ^ 40 * 1798140 * 2
def baseEnd_1798140 : Nat := 615540069383800001787007

theorem tailTrace_1798140 : CollatzResearch.WordTrace tailWord_1798140 prefixEnd_1798140 615540069383800001787007 := by
  unfold tailWord_1798140
  simp only [CollatzResearch.WordTrace]
  refine ⟨32791776852826676353899937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43722369137102235138533249 32791776852826676353899937)
  ·
    refine ⟨24593832639620007265424953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32791776852826676353899937 24593832639620007265424953)
    ·
      refine ⟨18445374479715005449068715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24593832639620007265424953 18445374479715005449068715)
      ·
        refine ⟨27668061719572508173603073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18445374479715005449068715 27668061719572508173603073)
        ·
          refine ⟨20751046289679381130202305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27668061719572508173603073 20751046289679381130202305)
          ·
            refine ⟨15563284717259535847651729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20751046289679381130202305 15563284717259535847651729)
            ·
              refine ⟨11672463537944651885738797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15563284717259535847651729 11672463537944651885738797)
              ·
                refine ⟨4377173826729244457152049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11672463537944651885738797 4377173826729244457152049)
                ·
                  refine ⟨3282880370046933342864037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4377173826729244457152049 3282880370046933342864037)
                  ·
                    refine ⟨615540069383800001787007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3282880370046933342864037 615540069383800001787007)
                    ·
                      rfl

theorem cell22_1798140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_1798140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1798140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1798140 prefixEnd_1798140 := by exact prefixLift 1798140
  have htrace : WordTrace (prefixWord ++ tailWord_1798140) baseStart_1798140 baseEnd_1798140 := by
    simpa [prefixWord, tailWord_1798140, baseEnd_1798140] using wordTrace_append hprefix tailTrace_1798140
  have hstable : (prefixWord ++ tailWord_1798140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798140).length < 2 ^ (prefixWord ++ tailWord_1798140).sum := by decide
  have hdescent : baseEnd_1798140 < baseStart_1798140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798204 : List Nat := [2, 2, 2, 2, 2, 1, 2, 5, 1, 3]
def baseStart_1798204 : Nat := 118140960795 + 1798204 * 2 ^ 59
def prefixEnd_1798204 : Nat := 4983230072969 + 3 ^ 40 * 1798204 * 2
def baseEnd_1798204 : Nat := 615561977891725168186811

theorem tailTrace_1798204 : CollatzResearch.WordTrace tailWord_1798204 prefixEnd_1798204 615561977891725168186811 := by
  unfold tailWord_1798204
  simp only [CollatzResearch.WordTrace]
  refine ⟨32792943988710745819064833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43723925318280994425419777 32792943988710745819064833)
  ·
    refine ⟨24594707991533059364298625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32792943988710745819064833 24594707991533059364298625)
    ·
      refine ⟨18446030993649794523223969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24594707991533059364298625 18446030993649794523223969)
      ·
        refine ⟨13834523245237345892417977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18446030993649794523223969 13834523245237345892417977)
        ·
          refine ⟨10375892433928009419313483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13834523245237345892417977 10375892433928009419313483)
          ·
            refine ⟨15563838650892014128970225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10375892433928009419313483 15563838650892014128970225)
            ·
              refine ⟨11672878988169010596727669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15563838650892014128970225 11672878988169010596727669)
              ·
                refine ⟨1094332405140844743443219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11672878988169010596727669 1094332405140844743443219)
                ·
                  refine ⟨1641498607711267115164829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1094332405140844743443219 1641498607711267115164829)
                  ·
                    refine ⟨615561977891725168186811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1641498607711267115164829 615561977891725168186811)
                    ·
                      rfl

theorem cell22_1798204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 5, 1, 3].length) (baseStart_1798204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1798204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1798204 prefixEnd_1798204 := by exact prefixLift 1798204
  have htrace : WordTrace (prefixWord ++ tailWord_1798204) baseStart_1798204 baseEnd_1798204 := by
    simpa [prefixWord, tailWord_1798204, baseEnd_1798204] using wordTrace_append hprefix tailTrace_1798204
  have hstable : (prefixWord ++ tailWord_1798204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798204).length < 2 ^ (prefixWord ++ tailWord_1798204).sum := by decide
  have hdescent : baseEnd_1798204 < baseStart_1798204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798215 : List Nat := [1, 1, 4, 1, 3, 1, 2, 2, 2, 5]
def baseStart_1798215 : Nat := 118140960795 + 1798215 * 2 ^ 59
def prefixEnd_1798215 : Nat := 4983230072969 + 3 ^ 40 * 1798215 * 2
def baseEnd_1798215 : Nat := 615565743416524806161777

theorem tailTrace_1798215 : CollatzResearch.WordTrace tailWord_1798215 prefixEnd_1798215 615565743416524806161777 := by
  unfold tailWord_1798215
  simp only [CollatzResearch.WordTrace]
  refine ⟨65586289180381640516780099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43724192786921093677853399 65586289180381640516780099)
  ·
    refine ⟨98379433770572460775170149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65586289180381640516780099 98379433770572460775170149)
    ·
      refine ⟨18446143831982336395344403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98379433770572460775170149 18446143831982336395344403)
      ·
        refine ⟨27669215747973504593016605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18446143831982336395344403 27669215747973504593016605)
        ·
          refine ⟨10375955905490064222381227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27669215747973504593016605 10375955905490064222381227)
          ·
            refine ⟨15563933858235096333571841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10375955905490064222381227 15563933858235096333571841)
            ·
              refine ⟨11672950393676322250178881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15563933858235096333571841 11672950393676322250178881)
              ·
                refine ⟨8754712795257241687634161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11672950393676322250178881 8754712795257241687634161)
                ·
                  refine ⟨6566034596442931265725621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8754712795257241687634161 6566034596442931265725621)
                  ·
                    refine ⟨615565743416524806161777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6566034596442931265725621 615565743416524806161777)
                    ·
                      rfl

theorem cell22_1798215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_1798215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1798215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1798215 prefixEnd_1798215 := by exact prefixLift 1798215
  have htrace : WordTrace (prefixWord ++ tailWord_1798215) baseStart_1798215 baseEnd_1798215 := by
    simpa [prefixWord, tailWord_1798215, baseEnd_1798215] using wordTrace_append hprefix tailTrace_1798215
  have hstable : (prefixWord ++ tailWord_1798215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798215).length < 2 ^ (prefixWord ++ tailWord_1798215).sum := by decide
  have hdescent : baseEnd_1798215 < baseStart_1798215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798221 : List Nat := [1, 6, 1, 1, 1, 1, 3, 4, 1, 3]
def baseStart_1798221 : Nat := 118140960795 + 1798221 * 2 ^ 59
def prefixEnd_1798221 : Nat := 4983230072969 + 3 ^ 40 * 1798221 * 2
def baseEnd_1798221 : Nat := 615567797339142790511759

theorem tailTrace_1798221 : CollatzResearch.WordTrace tailWord_1798221 prefixEnd_1798221 615567797339142790511759 := by
  unfold tailWord_1798221
  simp only [CollatzResearch.WordTrace]
  refine ⟨65586508018359903541498517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43724338678906602360999011 65586508018359903541498517)
  ·
    refine ⟨3074367563360620478507743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 65586508018359903541498517 3074367563360620478507743)
    ·
      refine ⟨4611551345040930717761615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3074367563360620478507743 4611551345040930717761615)
      ·
        refine ⟨6917327017561396076642423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4611551345040930717761615 6917327017561396076642423)
        ·
          refine ⟨10375990526342094114963635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6917327017561396076642423 10375990526342094114963635)
          ·
            refine ⟨15563985789513141172445453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10375990526342094114963635 15563985789513141172445453)
            ·
              refine ⟨5836494671067427939667045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15563985789513141172445453 5836494671067427939667045)
              ·
                refine ⟨1094342750825142738687571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5836494671067427939667045 1094342750825142738687571)
                ·
                  refine ⟨1641514126237714108031357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1094342750825142738687571 1641514126237714108031357)
                  ·
                    refine ⟨615567797339142790511759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1641514126237714108031357 615567797339142790511759)
                    ·
                      rfl

theorem cell22_1798221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_1798221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1798221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1798221 prefixEnd_1798221 := by exact prefixLift 1798221
  have htrace : WordTrace (prefixWord ++ tailWord_1798221) baseStart_1798221 baseEnd_1798221 := by
    simpa [prefixWord, tailWord_1798221, baseEnd_1798221] using wordTrace_append hprefix tailTrace_1798221
  have hstable : (prefixWord ++ tailWord_1798221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798221).length < 2 ^ (prefixWord ++ tailWord_1798221).sum := by decide
  have hdescent : baseEnd_1798221 < baseStart_1798221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798238 : List Nat := [4, 4, 1, 1, 2, 1, 1, 2, 3, 3]
def baseStart_1798238 : Nat := 118140960795 + 1798238 * 2 ^ 59
def prefixEnd_1798238 : Nat := 4983230072969 + 3 ^ 40 * 1798238 * 2
def baseEnd_1798238 : Nat := 615573616786560412836707

theorem tailTrace_1798238 : CollatzResearch.WordTrace tailWord_1798238 prefixEnd_1798238 615573616786560412836707 := by
  unfold tailWord_1798238
  simp only [CollatzResearch.WordTrace]
  refine ⟨8198391007412289430608421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43724752039532210296578245 8198391007412289430608421)
  ·
    refine ⟨1537198313889804268239079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8198391007412289430608421 1537198313889804268239079)
    ·
      refine ⟨2305797470834706402358619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1537198313889804268239079 2305797470834706402358619)
      ·
        refine ⟨3458696206252059603537929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2305797470834706402358619 3458696206252059603537929)
        ·
          refine ⟨2594022154689044702653447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3458696206252059603537929 2594022154689044702653447)
          ·
            refine ⟨3891033232033567053980171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2594022154689044702653447 3891033232033567053980171)
            ·
              refine ⟨5836549848050350580970257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3891033232033567053980171 5836549848050350580970257)
              ·
                refine ⟨4377412386037762935727693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5836549848050350580970257 4377412386037762935727693)
                ·
                  refine ⟨1641529644764161100897885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4377412386037762935727693 1641529644764161100897885)
                  ·
                    refine ⟨615573616786560412836707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1641529644764161100897885 615573616786560412836707)
                    ·
                      rfl

theorem cell22_1798238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_1798238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1798238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1798238 prefixEnd_1798238 := by exact prefixLift 1798238
  have htrace : WordTrace (prefixWord ++ tailWord_1798238) baseStart_1798238 baseEnd_1798238 := by
    simpa [prefixWord, tailWord_1798238, baseEnd_1798238] using wordTrace_append hprefix tailTrace_1798238
  have hstable : (prefixWord ++ tailWord_1798238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798238).length < 2 ^ (prefixWord ++ tailWord_1798238).sum := by decide
  have hdescent : baseEnd_1798238 < baseStart_1798238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798245 : List Nat := [1, 3, 1, 3, 2, 2, 1, 1, 8]
def baseStart_1798245 : Nat := 118140960795 + 1798245 * 2 ^ 59
def prefixEnd_1798245 : Nat := 4983230072969 + 3 ^ 40 * 1798245 * 2
def baseEnd_1798245 : Nat := 205192004343204909303895

theorem tailTrace_1798245 : CollatzResearch.WordTrace tailWord_1798245 prefixEnd_1798245 205192004343204909303895 := by
  unfold tailWord_1798245
  simp only [CollatzResearch.WordTrace]
  refine ⟨65587383370272955640372189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43724922246848637093581459 65587383370272955640372189)
  ·
    refine ⟨24595268763852358365139571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65587383370272955640372189 24595268763852358365139571)
    ·
      refine ⟨36892903145778537547709357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24595268763852358365139571 36892903145778537547709357)
      ·
        refine ⟨13834838679666951580391009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36892903145778537547709357 13834838679666951580391009)
        ·
          refine ⟨10376129009750213685293257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13834838679666951580391009 10376129009750213685293257)
          ·
            refine ⟨7782096757312660263969943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10376129009750213685293257 7782096757312660263969943)
            ·
              refine ⟨11673145135968990395954915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7782096757312660263969943 11673145135968990395954915)
              ·
                refine ⟨17509717703953485593932373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11673145135968990395954915 17509717703953485593932373)
                ·
                  refine ⟨205192004343204909303895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17509717703953485593932373 205192004343204909303895)
                  ·
                    rfl

theorem cell22_1798245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 8].length) (baseStart_1798245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1798245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1798245 prefixEnd_1798245 := by exact prefixLift 1798245
  have htrace : WordTrace (prefixWord ++ tailWord_1798245) baseStart_1798245 baseEnd_1798245 := by
    simpa [prefixWord, tailWord_1798245, baseEnd_1798245] using wordTrace_append hprefix tailTrace_1798245
  have hstable : (prefixWord ++ tailWord_1798245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798245).length < 2 ^ (prefixWord ++ tailWord_1798245).sum := by decide
  have hdescent : baseEnd_1798245 < baseStart_1798245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798247 : List Nat := [1, 1, 5, 1, 1, 2, 2, 4, 1, 4]
def baseStart_1798247 : Nat := 118140960795 + 1798247 * 2 ^ 59
def prefixEnd_1798247 : Nat := 4983230072969 + 3 ^ 40 * 1798247 * 2
def baseEnd_1798247 : Nat := 615576697670487389361679

theorem tailTrace_1798247 : CollatzResearch.WordTrace tailWord_1798247 prefixEnd_1798247 615576697670487389361679 := by
  unfold tailWord_1798247
  simp only [CollatzResearch.WordTrace]
  refine ⟨65587456316265709981944995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43724970877510473321296663 65587456316265709981944995)
  ·
    refine ⟨98381184474398564972917493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65587456316265709981944995 98381184474398564972917493)
    ·
      refine ⟨9223236044474865466211015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98381184474398564972917493 9223236044474865466211015)
      ·
        refine ⟨13834854066712298199316523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9223236044474865466211015 13834854066712298199316523)
        ·
          refine ⟨20752281100068447298974785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13834854066712298199316523 20752281100068447298974785)
          ·
            refine ⟨15564210825051335474231089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20752281100068447298974785 15564210825051335474231089)
            ·
              refine ⟨11673158118788501605673317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15564210825051335474231089 11673158118788501605673317)
              ·
                refine ⟨2188717147272844051063747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11673158118788501605673317 2188717147272844051063747)
                ·
                  refine ⟨3283075720909266076595621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2188717147272844051063747 3283075720909266076595621)
                  ·
                    refine ⟨615576697670487389361679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3283075720909266076595621 615576697670487389361679)
                    ·
                      rfl

theorem cell22_1798247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_1798247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1798247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1798247 prefixEnd_1798247 := by exact prefixLift 1798247
  have htrace : WordTrace (prefixWord ++ tailWord_1798247) baseStart_1798247 baseEnd_1798247 := by
    simpa [prefixWord, tailWord_1798247, baseEnd_1798247] using wordTrace_append hprefix tailTrace_1798247
  have hstable : (prefixWord ++ tailWord_1798247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798247).length < 2 ^ (prefixWord ++ tailWord_1798247).sum := by decide
  have hdescent : baseEnd_1798247 < baseStart_1798247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798431 : List Nat := [1, 1, 2, 4, 3, 2, 2, 3, 4]
def baseStart_1798431 : Nat := 118140960795 + 1798431 * 2 ^ 59
def prefixEnd_1798431 : Nat := 4983230072969 + 3 ^ 40 * 1798431 * 2
def baseEnd_1798431 : Nat := 205213228210257414253705

theorem tailTrace_1798431 : CollatzResearch.WordTrace tailWord_1798431 prefixEnd_1798431 205213228210257414253705 := by
  unfold tailWord_1798431
  simp only [CollatzResearch.WordTrace]
  refine ⟨65594167347599109406643147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43729444898399406271095431 65594167347599109406643147)
  ·
    refine ⟨98391251021398664109964721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65594167347599109406643147 98391251021398664109964721)
    ·
      refine ⟨73793438266048998082473541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98391251021398664109964721 73793438266048998082473541)
      ·
        refine ⟨13836269674884187140463789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73793438266048998082473541 13836269674884187140463789)
        ·
          refine ⟨5188601128081570177673921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13836269674884187140463789 5188601128081570177673921)
          ·
            refine ⟨3891450846061177633255441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5188601128081570177673921 3891450846061177633255441)
            ·
              refine ⟨2918588134545883224941581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3891450846061177633255441 2918588134545883224941581)
              ·
                refine ⟨1094470550454706209353093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2918588134545883224941581 1094470550454706209353093)
                ·
                  refine ⟨205213228210257414253705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1094470550454706209353093 205213228210257414253705)
                  ·
                    rfl

theorem cell22_1798431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 3, 4].length) (baseStart_1798431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1798431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1798431 prefixEnd_1798431 := by exact prefixLift 1798431
  have htrace : WordTrace (prefixWord ++ tailWord_1798431) baseStart_1798431 baseEnd_1798431 := by
    simpa [prefixWord, tailWord_1798431, baseEnd_1798431] using wordTrace_append hprefix tailTrace_1798431
  have hstable : (prefixWord ++ tailWord_1798431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798431).length < 2 ^ (prefixWord ++ tailWord_1798431).sum := by decide
  have hdescent : baseEnd_1798431 < baseStart_1798431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798472 : List Nat := [2, 1, 3, 1, 1, 2, 2, 2, 2, 6]
def baseStart_1798472 : Nat := 118140960795 + 1798472 * 2 ^ 59
def prefixEnd_1798472 : Nat := 4983230072969 + 3 ^ 40 * 1798472 * 2
def baseEnd_1798472 : Nat := 615653719768661802485989

theorem tailTrace_1798472 : CollatzResearch.WordTrace tailWord_1798472 prefixEnd_1798472 615653719768661802485989 := by
  unfold tailWord_1798472
  simp only [CollatzResearch.WordTrace]
  refine ⟨32797831370225286704442835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43730441826967048939257113 32797831370225286704442835)
  ·
    refine ⟨49196747055337930056664253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32797831370225286704442835 49196747055337930056664253)
    ·
      refine ⟨18448780145751723771249095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49196747055337930056664253 18448780145751723771249095)
      ·
        refine ⟨27673170218627585656873643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18448780145751723771249095 27673170218627585656873643)
        ·
          refine ⟨41509755327941378485310465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27673170218627585656873643 41509755327941378485310465)
          ·
            refine ⟨31132316495956033863982849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41509755327941378485310465 31132316495956033863982849)
            ·
              refine ⟨23349237371967025397987137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31132316495956033863982849 23349237371967025397987137)
              ·
                refine ⟨17511928028975269048490353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23349237371967025397987137 17511928028975269048490353)
                ·
                  refine ⟨13133946021731451786367765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17511928028975269048490353 13133946021731451786367765)
                  ·
                    refine ⟨615653719768661802485989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13133946021731451786367765 615653719768661802485989)
                    ·
                      rfl

theorem cell22_1798472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_1798472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1798472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1798472 prefixEnd_1798472 := by exact prefixLift 1798472
  have htrace : WordTrace (prefixWord ++ tailWord_1798472) baseStart_1798472 baseEnd_1798472 := by
    simpa [prefixWord, tailWord_1798472, baseEnd_1798472] using wordTrace_append hprefix tailTrace_1798472
  have hstable : (prefixWord ++ tailWord_1798472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798472).length < 2 ^ (prefixWord ++ tailWord_1798472).sum := by decide
  have hdescent : baseEnd_1798472 < baseStart_1798472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798487 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 9]
def baseStart_1798487 : Nat := 118140960795 + 1798487 * 2 ^ 59
def prefixEnd_1798487 : Nat := 4983230072969 + 3 ^ 40 * 1798487 * 2
def baseEnd_1798487 : Nat := 205219618191735587786981

theorem tailTrace_1798487 : CollatzResearch.WordTrace tailWord_1798487 prefixEnd_1798487 205219618191735587786981 := by
  unfold tailWord_1798487
  simp only [CollatzResearch.WordTrace]
  refine ⟨65596209835396230970681715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43730806556930820647121143 65596209835396230970681715)
  ·
    refine ⟨98394314753094346456022573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65596209835396230970681715 98394314753094346456022573)
    ·
      refine ⟨36897868032410379921008465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98394314753094346456022573 36897868032410379921008465)
      ·
        refine ⟨27673401024307784940756349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36897868032410379921008465 27673401024307784940756349)
        ·
          refine ⟨10377525384115419352783631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27673401024307784940756349 10377525384115419352783631)
          ·
            refine ⟨15566288076173129029175447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10377525384115419352783631 15566288076173129029175447)
            ·
              refine ⟨23349432114259693543763171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15566288076173129029175447 23349432114259693543763171)
              ·
                refine ⟨35024148171389540315644757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23349432114259693543763171 35024148171389540315644757)
                ·
                  refine ⟨205219618191735587786981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 35024148171389540315644757 205219618191735587786981)
                  ·
                    rfl

theorem cell22_1798487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 9].length) (baseStart_1798487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1798487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1798487 prefixEnd_1798487 := by exact prefixLift 1798487
  have htrace : WordTrace (prefixWord ++ tailWord_1798487) baseStart_1798487 baseEnd_1798487 := by
    simpa [prefixWord, tailWord_1798487, baseEnd_1798487] using wordTrace_append hprefix tailTrace_1798487
  have hstable : (prefixWord ++ tailWord_1798487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798487).length < 2 ^ (prefixWord ++ tailWord_1798487).sum := by decide
  have hdescent : baseEnd_1798487 < baseStart_1798487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798504 : List Nat := [2, 1, 4, 2, 2, 1, 2, 1, 7]
def baseStart_1798504 : Nat := 118140960795 + 1798504 * 2 ^ 59
def prefixEnd_1798504 : Nat := 4983230072969 + 3 ^ 40 * 1798504 * 2
def baseEnd_1798504 : Nat := 205221558007541461895297

theorem tailTrace_1798504 : CollatzResearch.WordTrace tailWord_1798504 prefixEnd_1798504 205221558007541461895297 := by
  unfold tailWord_1798504
  simp only [CollatzResearch.WordTrace]
  refine ⟨32798414938167321437025283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43731219917556428582700377 32798414938167321437025283)
  ·
    refine ⟨49197622407250982155537925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32798414938167321437025283 49197622407250982155537925)
    ·
      refine ⟨9224554201359559154163361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49197622407250982155537925 9224554201359559154163361)
      ·
        refine ⟨6918415651019669365622521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9224554201359559154163361 6918415651019669365622521)
        ·
          refine ⟨5188811738264752024216891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6918415651019669365622521 5188811738264752024216891)
          ·
            refine ⟨7783217607397128036325337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5188811738264752024216891 7783217607397128036325337)
            ·
              refine ⟨5837413205547846027244003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7783217607397128036325337 5837413205547846027244003)
              ·
                refine ⟨8756119808321769040866005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5837413205547846027244003 8756119808321769040866005)
                ·
                  refine ⟨205221558007541461895297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8756119808321769040866005 205221558007541461895297)
                  ·
                    rfl

theorem cell22_1798504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 7].length) (baseStart_1798504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1798504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1798504 prefixEnd_1798504 := by exact prefixLift 1798504
  have htrace : WordTrace (prefixWord ++ tailWord_1798504) baseStart_1798504 baseEnd_1798504 := by
    simpa [prefixWord, tailWord_1798504, baseEnd_1798504] using wordTrace_append hprefix tailTrace_1798504
  have hstable : (prefixWord ++ tailWord_1798504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798504).length < 2 ^ (prefixWord ++ tailWord_1798504).sum := by decide
  have hdescent : baseEnd_1798504 < baseStart_1798504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798508 : List Nat := [2, 2, 1, 1, 6, 2, 1, 1, 3, 3]
def baseStart_1798508 : Nat := 118140960795 + 1798508 * 2 ^ 59
def prefixEnd_1798508 : Nat := 4983230072969 + 3 ^ 40 * 1798508 * 2
def baseEnd_1798508 : Nat := 615666043304369708585879

theorem tailTrace_1798508 : CollatzResearch.WordTrace tailWord_1798508 prefixEnd_1798508 615666043304369708585879 := by
  unfold tailWord_1798508
  simp only [CollatzResearch.WordTrace]
  refine ⟨32798487884160075778598089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43731317178880101038130785 32798487884160075778598089)
  ·
    refine ⟨24598865913120056833948567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32798487884160075778598089 24598865913120056833948567)
    ·
      refine ⟨36898298869680085250922851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24598865913120056833948567 36898298869680085250922851)
      ·
        refine ⟨55347448304520127876384277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36898298869680085250922851 55347448304520127876384277)
        ·
          refine ⟨2594411639274380994205513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 55347448304520127876384277 2594411639274380994205513)
          ·
            refine ⟨1945808729455785745654135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2594411639274380994205513 1945808729455785745654135)
            ·
              refine ⟨2918713094183678618481203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1945808729455785745654135 2918713094183678618481203)
              ·
                refine ⟨4378069641275517927721805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2918713094183678618481203 4378069641275517927721805)
                ·
                  refine ⟨1641776115478319222895677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4378069641275517927721805 1641776115478319222895677)
                  ·
                    refine ⟨615666043304369708585879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1641776115478319222895677 615666043304369708585879)
                    ·
                      rfl

theorem cell22_1798508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 3].length) (baseStart_1798508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1798508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1798508 prefixEnd_1798508 := by exact prefixLift 1798508
  have htrace : WordTrace (prefixWord ++ tailWord_1798508) baseStart_1798508 baseEnd_1798508 := by
    simpa [prefixWord, tailWord_1798508, baseEnd_1798508] using wordTrace_append hprefix tailTrace_1798508
  have hstable : (prefixWord ++ tailWord_1798508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798508).length < 2 ^ (prefixWord ++ tailWord_1798508).sum := by decide
  have hdescent : baseEnd_1798508 < baseStart_1798508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798570 : List Nat := [3, 1, 6, 1, 1, 1, 1, 1, 2, 5]
def baseStart_1798570 : Nat := 118140960795 + 1798570 * 2 ^ 59
def prefixEnd_1798570 : Nat := 4983230072969 + 3 ^ 40 * 1798570 * 2
def baseEnd_1798570 : Nat := 615687267171422213535689

theorem tailTrace_1798570 : CollatzResearch.WordTrace tailWord_1798570 prefixEnd_1798570 615687267171422213535689 := by
  unfold tailWord_1798570
  simp only [CollatzResearch.WordTrace]
  refine ⟨16399809273523884036488291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43732824729397024097302109 16399809273523884036488291)
  ·
    refine ⟨24599713910285826054732437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16399809273523884036488291 24599713910285826054732437)
    ·
      refine ⟨1153111589544648096315583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24599713910285826054732437 1153111589544648096315583)
      ·
        refine ⟨1729667384316972144473375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1153111589544648096315583 1729667384316972144473375)
        ·
          refine ⟨2594501076475458216710063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1729667384316972144473375 2594501076475458216710063)
          ·
            refine ⟨3891751614713187325065095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2594501076475458216710063 3891751614713187325065095)
            ·
              refine ⟨5837627422069780987597643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3891751614713187325065095 5837627422069780987597643)
              ·
                refine ⟨8756441133104671481396465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5837627422069780987597643 8756441133104671481396465)
                ·
                  refine ⟨6567330849828503611047349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8756441133104671481396465 6567330849828503611047349)
                  ·
                    refine ⟨615687267171422213535689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6567330849828503611047349 615687267171422213535689)
                    ·
                      rfl

theorem cell22_1798570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_1798570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1798570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1798570 prefixEnd_1798570 := by exact prefixLift 1798570
  have htrace : WordTrace (prefixWord ++ tailWord_1798570) baseStart_1798570 baseEnd_1798570 := by
    simpa [prefixWord, tailWord_1798570, baseEnd_1798570] using wordTrace_append hprefix tailTrace_1798570
  have hstable : (prefixWord ++ tailWord_1798570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798570).length < 2 ^ (prefixWord ++ tailWord_1798570).sum := by decide
  have hdescent : baseEnd_1798570 < baseStart_1798570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798645 : List Nat := [1, 3, 5, 1, 2, 2, 2, 6]
def baseStart_1798645 : Nat := 118140960795 + 1798645 * 2 ^ 59
def prefixEnd_1798645 : Nat := 4983230072969 + 3 ^ 40 * 1798645 * 2
def baseEnd_1798645 : Nat := 68412549022683001990051

theorem tailTrace_1798645 : CollatzResearch.WordTrace tailWord_1798645 prefixEnd_1798645 68412549022683001990051 := by
  unfold tailWord_1798645
  simp only [CollatzResearch.WordTrace]
  refine ⟨65601972568823823954933389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43734648379215882636622259 65601972568823823954933389)
  ·
    refine ⟨24600739713308933983100021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65601972568823823954933389 24600739713308933983100021)
    ·
      refine ⟨2306319348122712560915627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24600739713308933983100021 2306319348122712560915627)
      ·
        refine ⟨3459479022184068841373441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2306319348122712560915627 3459479022184068841373441)
        ·
          refine ⟨2594609266638051631030081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3459479022184068841373441 2594609266638051631030081)
          ·
            refine ⟨1945956949978538723272561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2594609266638051631030081 1945956949978538723272561)
            ·
              refine ⟨1459467712483904042454421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1945956949978538723272561 1459467712483904042454421)
              ·
                refine ⟨68412549022683001990051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1459467712483904042454421 68412549022683001990051)
                ·
                  rfl

theorem cell22_1798645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 6].length) (baseStart_1798645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1798645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1798645 prefixEnd_1798645 := by exact prefixLift 1798645
  have htrace : WordTrace (prefixWord ++ tailWord_1798645) baseStart_1798645 baseEnd_1798645 := by
    simpa [prefixWord, tailWord_1798645, baseEnd_1798645] using wordTrace_append hprefix tailTrace_1798645
  have hstable : (prefixWord ++ tailWord_1798645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798645).length < 2 ^ (prefixWord ++ tailWord_1798645).sum := by decide
  have hdescent : baseEnd_1798645 < baseStart_1798645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798699 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 5, 5]
def baseStart_1798699 : Nat := 118140960795 + 1798699 * 2 ^ 59
def prefixEnd_1798699 : Nat := 4983230072969 + 3 ^ 40 * 1798699 * 2
def baseEnd_1798699 : Nat := 615731426507708877060293

theorem tailTrace_1798699 : CollatzResearch.WordTrace tailWord_1798699 prefixEnd_1798699 615731426507708877060293 := by
  unfold tailWord_1798699
  simp only [CollatzResearch.WordTrace]
  refine ⟨65603942110628191177399151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43735961407085460784932767 65603942110628191177399151)
  ·
    refine ⟨98405913165942286766098727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65603942110628191177399151 98405913165942286766098727)
    ·
      refine ⟨147608869748913430149148091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98405913165942286766098727 147608869748913430149148091)
      ·
        refine ⟨221413304623370145223722137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147608869748913430149148091 221413304623370145223722137)
        ·
          refine ⟨166059978467527608917791603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221413304623370145223722137 166059978467527608917791603)
          ·
            refine ⟨249089967701291413376687405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166059978467527608917791603 249089967701291413376687405)
            ·
              refine ⟨93408737887984280016257777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 249089967701291413376687405 93408737887984280016257777)
              ·
                refine ⟨70056553415988210012193333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93408737887984280016257777 70056553415988210012193333)
                ·
                  refine ⟨6567801882748894688643125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70056553415988210012193333 6567801882748894688643125)
                  ·
                    refine ⟨615731426507708877060293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6567801882748894688643125 615731426507708877060293)
                    ·
                      rfl

theorem cell22_1798699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 5].length) (baseStart_1798699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1798699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1798699 prefixEnd_1798699 := by exact prefixLift 1798699
  have htrace : WordTrace (prefixWord ++ tailWord_1798699) baseStart_1798699 baseEnd_1798699 := by
    simpa [prefixWord, tailWord_1798699, baseEnd_1798699] using wordTrace_append hprefix tailTrace_1798699
  have hstable : (prefixWord ++ tailWord_1798699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798699).length < 2 ^ (prefixWord ++ tailWord_1798699).sum := by decide
  have hdescent : baseEnd_1798699 < baseStart_1798699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798716 : List Nat := [2, 2, 2, 2, 3, 1, 1, 1, 3, 5]
def baseStart_1798716 : Nat := 118140960795 + 1798716 * 2 ^ 59
def prefixEnd_1798716 : Nat := 4983230072969 + 3 ^ 40 * 1798716 * 2
def baseEnd_1798716 : Nat := 615737245955126499385241

theorem tailTrace_1798716 : CollatzResearch.WordTrace tailWord_1798716 prefixEnd_1798716 615737245955126499385241 := by
  unfold tailWord_1798716
  simp only [CollatzResearch.WordTrace]
  refine ⟨32802281075783301540384001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43736374767711068720512001 32802281075783301540384001)
  ·
    refine ⟨24601710806837476155288001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32802281075783301540384001 24601710806837476155288001)
    ·
      refine ⟨18451283105128107116466001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24601710806837476155288001 18451283105128107116466001)
      ·
        refine ⟨13838462328846080337349501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18451283105128107116466001 13838462328846080337349501)
        ·
          refine ⟨5189423373317280126506063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13838462328846080337349501 5189423373317280126506063)
          ·
            refine ⟨7784135059975920189759095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5189423373317280126506063 7784135059975920189759095)
            ·
              refine ⟨11676202589963880284638643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7784135059975920189759095 11676202589963880284638643)
              ·
                refine ⟨17514303884945820426957965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11676202589963880284638643 17514303884945820426957965)
                ·
                  refine ⟨6567863956854682660109237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17514303884945820426957965 6567863956854682660109237)
                  ·
                    refine ⟨615737245955126499385241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6567863956854682660109237 615737245955126499385241)
                    ·
                      rfl

theorem cell22_1798716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_1798716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1798716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1798716 prefixEnd_1798716 := by exact prefixLift 1798716
  have htrace : WordTrace (prefixWord ++ tailWord_1798716) baseStart_1798716 baseEnd_1798716 := by
    simpa [prefixWord, tailWord_1798716, baseEnd_1798716] using wordTrace_append hprefix tailTrace_1798716
  have hstable : (prefixWord ++ tailWord_1798716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798716).length < 2 ^ (prefixWord ++ tailWord_1798716).sum := by decide
  have hdescent : baseEnd_1798716 < baseStart_1798716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798731 : List Nat := [1, 1, 1, 1, 3, 1, 6, 2, 2, 4]
def baseStart_1798731 : Nat := 118140960795 + 1798731 * 2 ^ 59
def prefixEnd_1798731 : Nat := 4983230072969 + 3 ^ 40 * 1798731 * 2
def baseEnd_1798731 : Nat := 615742380761671460260195

theorem tailTrace_1798731 : CollatzResearch.WordTrace tailWord_1798731 prefixEnd_1798731 615742380761671460260195 := by
  unfold tailWord_1798731
  simp only [CollatzResearch.WordTrace]
  refine ⟨65605109246512260642564047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43736739497674840428376031 65605109246512260642564047)
  ·
    refine ⟨98407663869768390963846071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65605109246512260642564047 98407663869768390963846071)
    ·
      refine ⟨147611495804652586445769107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98407663869768390963846071 147611495804652586445769107)
      ·
        refine ⟨221417243706978879668653661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147611495804652586445769107 221417243706978879668653661)
        ·
          refine ⟨83031466390117079875745123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221417243706978879668653661 83031466390117079875745123)
          ·
            refine ⟨124547199585175619813617685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83031466390117079875745123 124547199585175619813617685)
            ·
              refine ⟨5838149980555107178763329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 124547199585175619813617685 5838149980555107178763329)
              ·
                refine ⟨4378612485416330384072497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5838149980555107178763329 4378612485416330384072497)
                ·
                  refine ⟨3283959364062247788054373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4378612485416330384072497 3283959364062247788054373)
                  ·
                    refine ⟨615742380761671460260195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3283959364062247788054373 615742380761671460260195)
                    ·
                      rfl

theorem cell22_1798731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2, 4].length) (baseStart_1798731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1798731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1798731 prefixEnd_1798731 := by exact prefixLift 1798731
  have htrace : WordTrace (prefixWord ++ tailWord_1798731) baseStart_1798731 baseEnd_1798731 := by
    simpa [prefixWord, tailWord_1798731, baseEnd_1798731] using wordTrace_append hprefix tailTrace_1798731
  have hstable : (prefixWord ++ tailWord_1798731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798731).length < 2 ^ (prefixWord ++ tailWord_1798731).sum := by decide
  have hdescent : baseEnd_1798731 < baseStart_1798731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798765 : List Nat := [1, 5, 1, 1, 3, 3, 1, 1, 2, 4]
def baseStart_1798765 : Nat := 118140960795 + 1798765 * 2 ^ 59
def prefixEnd_1798765 : Nat := 4983230072969 + 3 ^ 40 * 1798765 * 2
def baseEnd_1798765 : Nat := 615754019656506704910091

theorem tailTrace_1798765 : CollatzResearch.WordTrace tailWord_1798765 prefixEnd_1798765 615754019656506704910091 := by
  unfold tailWord_1798765
  simp only [CollatzResearch.WordTrace]
  refine ⟨65606349328389084449301749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43737566218926056299534499 65606349328389084449301749)
  ·
    refine ⟨6150595249536476667122039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65606349328389084449301749 6150595249536476667122039)
    ·
      refine ⟨9225892874304715000683059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6150595249536476667122039 9225892874304715000683059)
      ·
        refine ⟨13838839311457072501024589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9225892874304715000683059 13838839311457072501024589)
        ·
          refine ⟨5189564741796402187884221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13838839311457072501024589 5189564741796402187884221)
          ·
            refine ⟨1946086778173650820456583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5189564741796402187884221 1946086778173650820456583)
            ·
              refine ⟨2919130167260476230684875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1946086778173650820456583 2919130167260476230684875)
              ·
                refine ⟨4378695250890714346027313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2919130167260476230684875 4378695250890714346027313)
                ·
                  refine ⟨3284021438168035759520485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4378695250890714346027313 3284021438168035759520485)
                  ·
                    refine ⟨615754019656506704910091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3284021438168035759520485 615754019656506704910091)
                    ·
                      rfl

theorem cell22_1798765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_1798765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1798765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1798765 prefixEnd_1798765 := by exact prefixLift 1798765
  have htrace : WordTrace (prefixWord ++ tailWord_1798765) baseStart_1798765 baseEnd_1798765 := by
    simpa [prefixWord, tailWord_1798765, baseEnd_1798765] using wordTrace_append hprefix tailTrace_1798765
  have hstable : (prefixWord ++ tailWord_1798765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798765).length < 2 ^ (prefixWord ++ tailWord_1798765).sum := by decide
  have hdescent : baseEnd_1798765 < baseStart_1798765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798791 : List Nat := [1, 1, 4, 2, 1, 2, 3, 1, 7]
def baseStart_1798791 : Nat := 118140960795 + 1798791 * 2 ^ 59
def prefixEnd_1798791 : Nat := 4983230072969 + 3 ^ 40 * 1798791 * 2
def baseEnd_1798791 : Nat := 205254306662617101253337

theorem tailTrace_1798791 : CollatzResearch.WordTrace tailWord_1798791 prefixEnd_1798791 205254306662617101253337 := by
  unfold tailWord_1798791
  simp only [CollatzResearch.WordTrace]
  refine ⟨65607297626294890889748227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43738198417529927259832151 65607297626294890889748227)
  ·
    refine ⟨98410946439442336334622341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65607297626294890889748227 98410946439442336334622341)
    ·
      refine ⟨18452052457395438062741689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98410946439442336334622341 18452052457395438062741689)
      ·
        refine ⟨13839039343046578547056267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18452052457395438062741689 13839039343046578547056267)
        ·
          refine ⟨20758559014569867820584401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13839039343046578547056267 20758559014569867820584401)
          ·
            refine ⟨15568919260927400865438301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20758559014569867820584401 15568919260927400865438301)
            ·
              refine ⟨5838344722847775324539363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15568919260927400865438301 5838344722847775324539363)
              ·
                refine ⟨8757517084271662986809045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5838344722847775324539363 8757517084271662986809045)
                ·
                  refine ⟨205254306662617101253337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8757517084271662986809045 205254306662617101253337)
                  ·
                    rfl

theorem cell22_1798791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 7].length) (baseStart_1798791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1798791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1798791 prefixEnd_1798791 := by exact prefixLift 1798791
  have htrace : WordTrace (prefixWord ++ tailWord_1798791) baseStart_1798791 baseEnd_1798791 := by
    simpa [prefixWord, tailWord_1798791, baseEnd_1798791] using wordTrace_append hprefix tailTrace_1798791
  have hstable : (prefixWord ++ tailWord_1798791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798791).length < 2 ^ (prefixWord ++ tailWord_1798791).sum := by decide
  have hdescent : baseEnd_1798791 < baseStart_1798791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798829 : List Nat := [1, 5, 2, 1, 1, 4, 1, 3, 1, 3]
def baseStart_1798829 : Nat := 118140960795 + 1798829 * 2 ^ 59
def prefixEnd_1798829 : Nat := 4983230072969 + 3 ^ 40 * 1798829 * 2
def baseEnd_1798829 : Nat := 615775928164431871309895

theorem tailTrace_1798829 : CollatzResearch.WordTrace tailWord_1798829 prefixEnd_1798829 615775928164431871309895 := by
  unfold tailWord_1798829
  simp only [CollatzResearch.WordTrace]
  refine ⟨65608683600157223379631541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43739122400104815586421027 65608683600157223379631541)
  ·
    refine ⟨6150814087514739691840457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65608683600157223379631541 6150814087514739691840457)
    ·
      refine ⟨4613110565636054768880343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6150814087514739691840457 4613110565636054768880343)
      ·
        refine ⟨6919665848454082153320515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4613110565636054768880343 6919665848454082153320515)
        ·
          refine ⟨10379498772681123229980773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6919665848454082153320515 10379498772681123229980773)
          ·
            refine ⟨1946156019877710605621395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10379498772681123229980773 1946156019877710605621395)
            ·
              refine ⟨2919234029816565908432093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1946156019877710605621395 2919234029816565908432093)
              ·
                refine ⟨1094712761181212215662035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2919234029816565908432093 1094712761181212215662035)
                ·
                  refine ⟨1642069141771818323493053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1094712761181212215662035 1642069141771818323493053)
                  ·
                    refine ⟨615775928164431871309895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1642069141771818323493053 615775928164431871309895)
                    ·
                      rfl

theorem cell22_1798829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_1798829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1798829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1798829 prefixEnd_1798829 := by exact prefixLift 1798829
  have htrace : WordTrace (prefixWord ++ tailWord_1798829) baseStart_1798829 baseEnd_1798829 := by
    simpa [prefixWord, tailWord_1798829, baseEnd_1798829] using wordTrace_append hprefix tailTrace_1798829
  have hstable : (prefixWord ++ tailWord_1798829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798829).length < 2 ^ (prefixWord ++ tailWord_1798829).sum := by decide
  have hdescent : baseEnd_1798829 < baseStart_1798829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798902 : List Nat := [5, 1, 1, 1, 1, 2, 4, 2, 2, 3]
def baseStart_1798902 : Nat := 118140960795 + 1798902 * 2 ^ 59
def prefixEnd_1798902 : Nat := 4983230072969 + 3 ^ 40 * 1798902 * 2
def baseEnd_1798902 : Nat := 615800917556284014234671

theorem tailTrace_1798902 : CollatzResearch.WordTrace tailWord_1798902 prefixEnd_1798902 615800917556284014234671 := by
  unfold tailWord_1798902
  simp only [CollatzResearch.WordTrace]
  refine ⟨4100709133055797302939935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43740897419261837898025973 4100709133055797302939935)
  ·
    refine ⟨6151063699583695954409903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4100709133055797302939935 6151063699583695954409903)
    ·
      refine ⟨9226595549375543931614855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6151063699583695954409903 9226595549375543931614855)
      ·
        refine ⟨13839893324063315897422283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9226595549375543931614855 13839893324063315897422283)
        ·
          refine ⟨20759839986094973846133425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13839893324063315897422283 20759839986094973846133425)
          ·
            refine ⟨15569879989571230384600069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20759839986094973846133425 15569879989571230384600069)
            ·
              refine ⟨2919352498044605697112513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15569879989571230384600069 2919352498044605697112513)
              ·
                refine ⟨2189514373533454272834385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2919352498044605697112513 2189514373533454272834385)
                ·
                  refine ⟨1642135780150090704625789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2189514373533454272834385 1642135780150090704625789)
                  ·
                    refine ⟨615800917556284014234671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1642135780150090704625789 615800917556284014234671)
                    ·
                      rfl

theorem cell22_1798902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_1798902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1798902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1798902 prefixEnd_1798902 := by exact prefixLift 1798902
  have htrace : WordTrace (prefixWord ++ tailWord_1798902) baseStart_1798902 baseEnd_1798902 := by
    simpa [prefixWord, tailWord_1798902, baseEnd_1798902] using wordTrace_append hprefix tailTrace_1798902
  have hstable : (prefixWord ++ tailWord_1798902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798902).length < 2 ^ (prefixWord ++ tailWord_1798902).sum := by decide
  have hdescent : baseEnd_1798902 < baseStart_1798902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798964 : List Nat := [2, 5, 1, 1, 3, 1, 2, 1, 3, 3]
def baseStart_1798964 : Nat := 118140960795 + 1798964 * 2 ^ 59
def prefixEnd_1798964 : Nat := 4983230072969 + 3 ^ 40 * 1798964 * 2
def baseEnd_1798964 : Nat := 615822141423336519184481

theorem tailTrace_1798964 : CollatzResearch.WordTrace tailWord_1798964 prefixEnd_1798964 615822141423336519184481 := by
  unfold tailWord_1798964
  simp only [CollatzResearch.WordTrace]
  refine ⟨32806803727334070717897973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43742404969778760957197297 32806803727334070717897973)
  ·
    refine ⟨3075637849437569129802935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32806803727334070717897973 3075637849437569129802935)
    ·
      refine ⟨4613456774156353694704403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3075637849437569129802935 4613456774156353694704403)
      ·
        refine ⟨6920185161234530542056605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4613456774156353694704403 6920185161234530542056605)
        ·
          refine ⟨2595069435462948953271227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6920185161234530542056605 2595069435462948953271227)
          ·
            refine ⟨3892604153194423429906841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2595069435462948953271227 3892604153194423429906841)
            ·
              refine ⟨2919453114895817572430131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3892604153194423429906841 2919453114895817572430131)
              ·
                refine ⟨4379179672343726358645197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2919453114895817572430131 4379179672343726358645197)
                ·
                  refine ⟨1642192377128897384491949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4379179672343726358645197 1642192377128897384491949)
                  ·
                    refine ⟨615822141423336519184481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1642192377128897384491949 615822141423336519184481)
                    ·
                      rfl

theorem cell22_1798964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_1798964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1798964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1798964 prefixEnd_1798964 := by exact prefixLift 1798964
  have htrace : WordTrace (prefixWord ++ tailWord_1798964) baseStart_1798964 baseEnd_1798964 := by
    simpa [prefixWord, tailWord_1798964, baseEnd_1798964] using wordTrace_append hprefix tailTrace_1798964
  have hstable : (prefixWord ++ tailWord_1798964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798964).length < 2 ^ (prefixWord ++ tailWord_1798964).sum := by decide
  have hdescent : baseEnd_1798964 < baseStart_1798964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799020 : List Nat := [2, 2, 1, 1, 4, 1, 1, 3, 4, 3]
def baseStart_1799020 : Nat := 118140960795 + 1799020 * 2 ^ 59
def prefixEnd_1799020 : Nat := 4983230072969 + 3 ^ 40 * 1799020 * 2
def baseEnd_1799020 : Nat := 615841311367771039784309

theorem tailTrace_1799020 : CollatzResearch.WordTrace tailWord_1799020 prefixEnd_1799020 615841311367771039784309 := by
  unfold tailWord_1799020
  simp only [CollatzResearch.WordTrace]
  refine ⟨32807824971232631499917257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43743766628310175333223009 32807824971232631499917257)
  ·
    refine ⟨24605868728424473624937943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32807824971232631499917257 24605868728424473624937943)
    ·
      refine ⟨36908803092636710437406915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24605868728424473624937943 36908803092636710437406915)
      ·
        refine ⟨55363204638955065656110373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36908803092636710437406915 55363204638955065656110373)
        ·
          refine ⟨10380600869804074810520695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55363204638955065656110373 10380600869804074810520695)
          ·
            refine ⟨15570901304706112215781043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10380600869804074810520695 15570901304706112215781043)
            ·
              refine ⟨23356351957059168323671565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15570901304706112215781043 23356351957059168323671565)
              ·
                refine ⟨8758631983897188121376837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23356351957059168323671565 8758631983897188121376837)
                ·
                  refine ⟨1642243496980722772758157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8758631983897188121376837 1642243496980722772758157)
                  ·
                    refine ⟨615841311367771039784309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1642243496980722772758157 615841311367771039784309)
                    ·
                      rfl

theorem cell22_1799020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 3].length) (baseStart_1799020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1799020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1799020 prefixEnd_1799020 := by exact prefixLift 1799020
  have htrace : WordTrace (prefixWord ++ tailWord_1799020) baseStart_1799020 baseEnd_1799020 := by
    simpa [prefixWord, tailWord_1799020, baseEnd_1799020] using wordTrace_append hprefix tailTrace_1799020
  have hstable : (prefixWord ++ tailWord_1799020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799020).length < 2 ^ (prefixWord ++ tailWord_1799020).sum := by decide
  have hdescent : baseEnd_1799020 < baseStart_1799020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799033 : List Nat := [1, 2, 1, 3, 2, 3, 1, 9]
def baseStart_1799033 : Nat := 118140960795 + 1799033 * 2 ^ 59
def prefixEnd_1799033 : Nat := 4983230072969 + 3 ^ 40 * 1799033 * 2
def baseEnd_1799033 : Nat := 68427306837049259912141

theorem tailTrace_1799033 : CollatzResearch.WordTrace tailWord_1799033 prefixEnd_1799033 68427306837049259912141 := by
  unfold tailWord_1799033
  simp only [CollatzResearch.WordTrace]
  refine ⟨65616124091418166220057753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43744082727612110813371835 65616124091418166220057753)
  ·
    refine ⟨49212093068563624665043315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65616124091418166220057753 49212093068563624665043315)
    ·
      refine ⟨73818139602845436997564973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49212093068563624665043315 73818139602845436997564973)
      ·
        refine ⟨27681802351067038874086865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73818139602845436997564973 27681802351067038874086865)
        ·
          refine ⟨20761351763300279155565149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27681802351067038874086865 20761351763300279155565149)
          ·
            refine ⟨7785506911237604683336931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20761351763300279155565149 7785506911237604683336931)
            ·
              refine ⟨11678260366856407025005397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7785506911237604683336931 11678260366856407025005397)
              ·
                refine ⟨68427306837049259912141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11678260366856407025005397 68427306837049259912141)
                ·
                  rfl

theorem cell22_1799033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 9].length) (baseStart_1799033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1799033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1799033 prefixEnd_1799033 := by exact prefixLift 1799033
  have htrace : WordTrace (prefixWord ++ tailWord_1799033) baseStart_1799033 baseEnd_1799033 := by
    simpa [prefixWord, tailWord_1799033, baseEnd_1799033] using wordTrace_append hprefix tailTrace_1799033
  have hstable : (prefixWord ++ tailWord_1799033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799033).length < 2 ^ (prefixWord ++ tailWord_1799033).sum := by decide
  have hdescent : baseEnd_1799033 < baseStart_1799033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799050 : List Nat := [3, 1, 2, 4, 1, 1, 2, 8]
def baseStart_1799050 : Nat := 118140960795 + 1799050 * 2 ^ 59
def prefixEnd_1799050 : Nat := 4983230072969 + 3 ^ 40 * 1799050 * 2
def baseEnd_1799050 : Nat := 68427953442317884614913

theorem tailTrace_1799050 : CollatzResearch.WordTrace tailWord_1799050 prefixEnd_1799050 68427953442317884614913 := by
  unfold tailWord_1799050
  simp only [CollatzResearch.WordTrace]
  refine ⟨16404186033089144530856651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43744496088237718748951069 16404186033089144530856651)
  ·
    refine ⟨24606279049633716796284977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16404186033089144530856651 24606279049633716796284977)
    ·
      refine ⟨18454709287225287597213733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24606279049633716796284977 18454709287225287597213733)
      ·
        refine ⟨3460257991354741424477575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18454709287225287597213733 3460257991354741424477575)
        ·
          refine ⟨5190386987032112136716363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3460257991354741424477575 5190386987032112136716363)
          ·
            refine ⟨7785580480548168205074545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5190386987032112136716363 7785580480548168205074545)
            ·
              refine ⟨5839185360411126153805909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7785580480548168205074545 5839185360411126153805909)
              ·
                refine ⟨68427953442317884614913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5839185360411126153805909 68427953442317884614913)
                ·
                  rfl

theorem cell22_1799050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 8].length) (baseStart_1799050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1799050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1799050 prefixEnd_1799050 := by exact prefixLift 1799050
  have htrace : WordTrace (prefixWord ++ tailWord_1799050) baseStart_1799050 baseEnd_1799050 := by
    simpa [prefixWord, tailWord_1799050, baseEnd_1799050] using wordTrace_append hprefix tailTrace_1799050
  have hstable : (prefixWord ++ tailWord_1799050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799050).length < 2 ^ (prefixWord ++ tailWord_1799050).sum := by decide
  have hdescent : baseEnd_1799050 < baseStart_1799050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799095 : List Nat := [1, 1, 3, 1, 3, 1, 4, 3, 5]
def baseStart_1799095 : Nat := 118140960795 + 1799095 * 2 ^ 59
def prefixEnd_1799095 : Nat := 4983230072969 + 3 ^ 40 * 1799095 * 2
def baseEnd_1799095 : Nat := 205288995133498614719693

theorem tailTrace_1799095 : CollatzResearch.WordTrace tailWord_1799095 prefixEnd_1799095 205288995133498614719693 := by
  unfold tailWord_1799095
  simp only [CollatzResearch.WordTrace]
  refine ⟨65618385417193550808814739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43745590278129033872543159 65618385417193550808814739)
  ·
    refine ⟨98427578125790326213222109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65618385417193550808814739 98427578125790326213222109)
    ·
      refine ⟨36910341797171372329958291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98427578125790326213222109 36910341797171372329958291)
      ·
        refine ⟨55365512695757058494937437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36910341797171372329958291 55365512695757058494937437)
        ·
          refine ⟨20762067260908896935601539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55365512695757058494937437 20762067260908896935601539)
          ·
            refine ⟨31143100891363345403402309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20762067260908896935601539 31143100891363345403402309)
            ·
              refine ⟨5839331417130627263137933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31143100891363345403402309 5839331417130627263137933)
              ·
                refine ⟨2189749281423985223676725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5839331417130627263137933 2189749281423985223676725)
                ·
                  refine ⟨205288995133498614719693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2189749281423985223676725 205288995133498614719693)
                  ·
                    rfl

theorem cell22_1799095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3, 5].length) (baseStart_1799095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1799095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1799095 prefixEnd_1799095 := by exact prefixLift 1799095
  have htrace : WordTrace (prefixWord ++ tailWord_1799095) baseStart_1799095 baseEnd_1799095 := by
    simpa [prefixWord, tailWord_1799095, baseEnd_1799095] using wordTrace_append hprefix tailTrace_1799095
  have hstable : (prefixWord ++ tailWord_1799095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799095).length < 2 ^ (prefixWord ++ tailWord_1799095).sum := by decide
  have hdescent : baseEnd_1799095 < baseStart_1799095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799191 : List Nat := [1, 1, 3, 5, 1, 2, 3, 2, 4]
def baseStart_1799191 : Nat := 118140960795 + 1799191 * 2 ^ 59
def prefixEnd_1799191 : Nat := 4983230072969 + 3 ^ 40 * 1799191 * 2
def baseEnd_1799191 : Nat := 205299949387461197919595

theorem tailTrace_1799191 : CollatzResearch.WordTrace tailWord_1799191 prefixEnd_1799191 205299949387461197919595 := by
  unfold tailWord_1799191
  simp only [CollatzResearch.WordTrace]
  refine ⟨65621886824845759204309427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43747924549897172802872951 65621886824845759204309427)
  ·
    refine ⟨98432830237268638806464141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65621886824845759204309427 98432830237268638806464141)
    ·
      refine ⟨36912311338975739552424053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98432830237268638806464141 36912311338975739552424053)
      ·
        refine ⟨3460529188028975583039755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36912311338975739552424053 3460529188028975583039755)
        ·
          refine ⟨5190793782043463374559633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3460529188028975583039755 5190793782043463374559633)
          ·
            refine ⟨3893095336532597530919725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5190793782043463374559633 3893095336532597530919725)
            ·
              refine ⟨1459910751199724074094897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3893095336532597530919725 1459910751199724074094897)
              ·
                refine ⟨1094933063399793055571173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1459910751199724074094897 1094933063399793055571173)
                ·
                  refine ⟨205299949387461197919595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1094933063399793055571173 205299949387461197919595)
                  ·
                    rfl

theorem cell22_1799191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 2, 4].length) (baseStart_1799191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1799191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1799191 prefixEnd_1799191 := by exact prefixLift 1799191
  have htrace : WordTrace (prefixWord ++ tailWord_1799191) baseStart_1799191 baseEnd_1799191 := by
    simpa [prefixWord, tailWord_1799191, baseEnd_1799191] using wordTrace_append hprefix tailTrace_1799191
  have hstable : (prefixWord ++ tailWord_1799191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799191).length < 2 ^ (prefixWord ++ tailWord_1799191).sum := by decide
  have hdescent : baseEnd_1799191 < baseStart_1799191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799202 : List Nat := [3, 3, 1, 1, 1, 4, 2, 7]
def baseStart_1799202 : Nat := 118140960795 + 1799202 * 2 ^ 59
def prefixEnd_1799202 : Nat := 4983230072969 + 3 ^ 40 * 1799202 * 2
def baseEnd_1799202 : Nat := 68433734854131470192639

theorem tailTrace_1799202 : CollatzResearch.WordTrace tailWord_1799202 prefixEnd_1799202 68433734854131470192639 := by
  unfold tailWord_1799202
  simp only [CollatzResearch.WordTrace]
  refine ⟨16405572006951477020739965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43748192018537272055306573 16405572006951477020739965)
  ·
    refine ⟨6152089502606803882777487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16405572006951477020739965 6152089502606803882777487)
    ·
      refine ⟨9228134253910205824166231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6152089502606803882777487 9228134253910205824166231)
      ·
        refine ⟨13842201380865308736249347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9228134253910205824166231 13842201380865308736249347)
        ·
          refine ⟨20763302071297963104374021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13842201380865308736249347 20763302071297963104374021)
          ·
            refine ⟨3893119138368368082070129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20763302071297963104374021 3893119138368368082070129)
            ·
              refine ⟨2919839353776276061552597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3893119138368368082070129 2919839353776276061552597)
              ·
                refine ⟨68433734854131470192639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2919839353776276061552597 68433734854131470192639)
                ·
                  rfl

theorem cell22_1799202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 7].length) (baseStart_1799202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1799202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1799202 prefixEnd_1799202 := by exact prefixLift 1799202
  have htrace : WordTrace (prefixWord ++ tailWord_1799202) baseStart_1799202 baseEnd_1799202 := by
    simpa [prefixWord, tailWord_1799202, baseEnd_1799202] using wordTrace_append hprefix tailTrace_1799202
  have hstable : (prefixWord ++ tailWord_1799202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799202).length < 2 ^ (prefixWord ++ tailWord_1799202).sum := by decide
  have hdescent : baseEnd_1799202 < baseStart_1799202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799217 : List Nat := [1, 2, 2, 3, 1, 2, 2, 1, 5, 3]
def baseStart_1799217 : Nat := 118140960795 + 1799217 * 2 ^ 59
def prefixEnd_1799217 : Nat := 4983230072969 + 3 ^ 40 * 1799217 * 2
def baseEnd_1799217 : Nat := 615908748493728192608705

theorem tailTrace_1799217 : CollatzResearch.WordTrace tailWord_1799217 prefixEnd_1799217 615908748493728192608705 := by
  unfold tailWord_1799217
  simp only [CollatzResearch.WordTrace]
  refine ⟨65622835122751565644755905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43748556748501043763170603 65622835122751565644755905)
  ·
    refine ⟨49217126342063674233566929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65622835122751565644755905 49217126342063674233566929)
    ·
      refine ⟨36912844756547755675175197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49217126342063674233566929 36912844756547755675175197)
      ·
        refine ⟨13842316783705408378190699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36912844756547755675175197 13842316783705408378190699)
        ·
          refine ⟨20763475175558112567286049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13842316783705408378190699 20763475175558112567286049)
          ·
            refine ⟨15572606381668584425464537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20763475175558112567286049 15572606381668584425464537)
            ·
              refine ⟨11679454786251438319098403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15572606381668584425464537 11679454786251438319098403)
              ·
                refine ⟨17519182179377157478647605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11679454786251438319098403 17519182179377157478647605)
                ·
                  refine ⟨1642423329316608513623213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17519182179377157478647605 1642423329316608513623213)
                  ·
                    refine ⟨615908748493728192608705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1642423329316608513623213 615908748493728192608705)
                    ·
                      rfl

theorem cell22_1799217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 5, 3].length) (baseStart_1799217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1799217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1799217 prefixEnd_1799217 := by exact prefixLift 1799217
  have htrace : WordTrace (prefixWord ++ tailWord_1799217) baseStart_1799217 baseEnd_1799217 := by
    simpa [prefixWord, tailWord_1799217, baseEnd_1799217] using wordTrace_append hprefix tailTrace_1799217
  have hstable : (prefixWord ++ tailWord_1799217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799217).length < 2 ^ (prefixWord ++ tailWord_1799217).sum := by decide
  have hdescent : baseEnd_1799217 < baseStart_1799217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799285 : List Nat := [1, 3, 4, 3, 1, 1, 2, 3, 1, 3]
def baseStart_1799285 : Nat := 118140960795 + 1799285 * 2 ^ 59
def prefixEnd_1799285 : Nat := 4983230072969 + 3 ^ 40 * 1799285 * 2
def baseEnd_1799285 : Nat := 615932026283398681908497

theorem tailTrace_1799285 : CollatzResearch.WordTrace tailWord_1799285 prefixEnd_1799285 615932026283398681908497 := by
  unfold tailWord_1799285
  simp only [CollatzResearch.WordTrace]
  refine ⟨65625315286505213258231309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43750210191003475505487539 65625315286505213258231309)
  ·
    refine ⟨24609493232439454971836741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65625315286505213258231309 24609493232439454971836741)
    ·
      refine ⟨4614279981082397807219389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24609493232439454971836741 4614279981082397807219389)
      ·
        refine ⟨1730354992905899177707271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4614279981082397807219389 1730354992905899177707271)
        ·
          refine ⟨2595532489358848766560907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1730354992905899177707271 2595532489358848766560907)
          ·
            refine ⟨3893298734038273149841361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2595532489358848766560907 3893298734038273149841361)
            ·
              refine ⟨2919974050528704862381021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3893298734038273149841361 2919974050528704862381021)
              ·
                refine ⟨1094990268948264323392883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2919974050528704862381021 1094990268948264323392883)
                ·
                  refine ⟨1642485403422396485089325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1094990268948264323392883 1642485403422396485089325)
                  ·
                    refine ⟨615932026283398681908497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1642485403422396485089325 615932026283398681908497)
                    ·
                      rfl

theorem cell22_1799285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_1799285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1799285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1799285 prefixEnd_1799285 := by exact prefixLift 1799285
  have htrace : WordTrace (prefixWord ++ tailWord_1799285) baseStart_1799285 baseEnd_1799285 := by
    simpa [prefixWord, tailWord_1799285, baseEnd_1799285] using wordTrace_append hprefix tailTrace_1799285
  have hstable : (prefixWord ++ tailWord_1799285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799285).length < 2 ^ (prefixWord ++ tailWord_1799285).sum := by decide
  have hdescent : baseEnd_1799285 < baseStart_1799285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799324 : List Nat := [2, 2, 3, 2, 1, 2, 3, 1, 1, 5]
def baseStart_1799324 : Nat := 118140960795 + 1799324 * 2 ^ 59
def prefixEnd_1799324 : Nat := 4983230072969 + 3 ^ 40 * 1799324 * 2
def baseEnd_1799324 : Nat := 615945376780415580183377

theorem tailTrace_1799324 : CollatzResearch.WordTrace tailWord_1799324 prefixEnd_1799324 615945376780415580183377 := by
  unfold tailWord_1799324
  simp only [CollatzResearch.WordTrace]
  refine ⟨32813368866681961459450513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43751158488909281945934017 32813368866681961459450513)
  ·
    refine ⟨24610026650011471094587885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32813368866681961459450513 24610026650011471094587885)
    ·
      refine ⟨9228759993754301660470457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24610026650011471094587885 9228759993754301660470457)
      ·
        refine ⟨6921569995315726245352843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9228759993754301660470457 6921569995315726245352843)
        ·
          refine ⟨10382354992973589368029265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6921569995315726245352843 10382354992973589368029265)
          ·
            refine ⟨7786766244730192026021949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10382354992973589368029265 7786766244730192026021949)
            ·
              refine ⟨2920037341773822009758231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7786766244730192026021949 2920037341773822009758231)
              ·
                refine ⟨4380056012660733014637347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2920037341773822009758231 4380056012660733014637347)
                ·
                  refine ⟨6570084018991099521956021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4380056012660733014637347 6570084018991099521956021)
                  ·
                    refine ⟨615945376780415580183377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6570084018991099521956021 615945376780415580183377)
                    ·
                      rfl

theorem cell22_1799324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_1799324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1799324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1799324 prefixEnd_1799324 := by exact prefixLift 1799324
  have htrace : WordTrace (prefixWord ++ tailWord_1799324) baseStart_1799324 baseEnd_1799324 := by
    simpa [prefixWord, tailWord_1799324, baseEnd_1799324] using wordTrace_append hprefix tailTrace_1799324
  have hstable : (prefixWord ++ tailWord_1799324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799324).length < 2 ^ (prefixWord ++ tailWord_1799324).sum := by decide
  have hdescent : baseEnd_1799324 < baseStart_1799324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799414 : List Nat := [5, 1, 1, 1, 1, 1, 1, 4, 2, 5]
def baseStart_1799414 : Nat := 118140960795 + 1799414 * 2 ^ 59
def prefixEnd_1799414 : Nat := 4983230072969 + 3 ^ 40 * 1799414 * 2
def baseEnd_1799414 : Nat := 615976185619685345433101

theorem tailTrace_1799414 : CollatzResearch.WordTrace tailWord_1799414 prefixEnd_1799414 615976185619685345433101 := by
  unfold tailWord_1799414
  simp only [CollatzResearch.WordTrace]
  refine ⟨4101876268939866768104831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43753346868691912193118197 4101876268939866768104831)
  ·
    refine ⟨6152814403409800152157247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4101876268939866768104831 6152814403409800152157247)
    ·
      refine ⟨9229221605114700228235871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6152814403409800152157247 9229221605114700228235871)
      ·
        refine ⟨13843832407672050342353807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9229221605114700228235871 13843832407672050342353807)
        ·
          refine ⟨20765748611508075513530711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13843832407672050342353807 20765748611508075513530711)
          ·
            refine ⟨31148622917262113270296067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20765748611508075513530711 31148622917262113270296067)
            ·
              refine ⟨46722934375893169905444101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31148622917262113270296067 46722934375893169905444101)
              ·
                refine ⟨8760550195479969357270769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46722934375893169905444101 8760550195479969357270769)
                ·
                  refine ⟨6570412646609977017953077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8760550195479969357270769 6570412646609977017953077)
                  ·
                    refine ⟨615976185619685345433101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6570412646609977017953077 615976185619685345433101)
                    ·
                      rfl

theorem cell22_1799414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_1799414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1799414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1799414 prefixEnd_1799414 := by exact prefixLift 1799414
  have htrace : WordTrace (prefixWord ++ tailWord_1799414) baseStart_1799414 baseEnd_1799414 := by
    simpa [prefixWord, tailWord_1799414, baseEnd_1799414] using wordTrace_append hprefix tailTrace_1799414
  have hstable : (prefixWord ++ tailWord_1799414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799414).length < 2 ^ (prefixWord ++ tailWord_1799414).sum := by decide
  have hdescent : baseEnd_1799414 < baseStart_1799414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799459 : List Nat := [1, 1, 1, 4, 2, 3, 2, 2, 1, 5]
def baseStart_1799459 : Nat := 118140960795 + 1799459 * 2 ^ 59
def prefixEnd_1799459 : Nat := 4983230072969 + 3 ^ 40 * 1799459 * 2
def baseEnd_1799459 : Nat := 615991590039320228057963

theorem tailTrace_1799459 : CollatzResearch.WordTrace tailWord_1799459 prefixEnd_1799459 615991590039320228057963 := by
  unfold tailWord_1799459
  simp only [CollatzResearch.WordTrace]
  refine ⟨65631661587874840975065431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43754441058583227316710287 65631661587874840975065431)
  ·
    refine ⟨98447492381812261462598147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65631661587874840975065431 98447492381812261462598147)
    ·
      refine ⟨147671238572718392193897221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98447492381812261462598147 147671238572718392193897221)
      ·
        refine ⟨27688357232384698536355729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147671238572718392193897221 27688357232384698536355729)
        ·
          refine ⟨20766267924288523902266797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27688357232384698536355729 20766267924288523902266797)
          ·
            refine ⟨7787350471608196463350049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20766267924288523902266797 7787350471608196463350049)
            ·
              refine ⟨5840512853706147347512537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7787350471608196463350049 5840512853706147347512537)
              ·
                refine ⟨4380384640279610510634403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5840512853706147347512537 4380384640279610510634403)
                ·
                  refine ⟨6570576960419415765951605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4380384640279610510634403 6570576960419415765951605)
                  ·
                    refine ⟨615991590039320228057963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6570576960419415765951605 615991590039320228057963)
                    ·
                      rfl

theorem cell22_1799459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 5].length) (baseStart_1799459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1799459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1799459 prefixEnd_1799459 := by exact prefixLift 1799459
  have htrace : WordTrace (prefixWord ++ tailWord_1799459) baseStart_1799459 baseEnd_1799459 := by
    simpa [prefixWord, tailWord_1799459, baseEnd_1799459] using wordTrace_append hprefix tailTrace_1799459
  have hstable : (prefixWord ++ tailWord_1799459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799459).length < 2 ^ (prefixWord ++ tailWord_1799459).sum := by decide
  have hdescent : baseEnd_1799459 < baseStart_1799459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799461 : List Nat := [1, 3, 1, 2, 4, 1, 1, 5, 4]
def baseStart_1799461 : Nat := 118140960795 + 1799461 * 2 ^ 59
def prefixEnd_1799461 : Nat := 4983230072969 + 3 ^ 40 * 1799461 * 2
def baseEnd_1799461 : Nat := 205330758226730963169319

theorem tailTrace_1799461 : CollatzResearch.WordTrace tailWord_1799461 prefixEnd_1799461 205330758226730963169319 := by
  unfold tailWord_1799461
  simp only [CollatzResearch.WordTrace]
  refine ⟨65631734533867595316638237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43754489689245063544425491 65631734533867595316638237)
  ·
    refine ⟨24611900450200348243739339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65631734533867595316638237 24611900450200348243739339)
    ·
      refine ⟨36917850675300522365609009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24611900450200348243739339 36917850675300522365609009)
      ·
        refine ⟨27688388006475391774206757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36917850675300522365609009 27688388006475391774206757)
        ·
          refine ⟨5191572751214135957663767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27688388006475391774206757 5191572751214135957663767)
          ·
            refine ⟨7787359126821203936495651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5191572751214135957663767 7787359126821203936495651)
            ·
              refine ⟨11681038690231805904743477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7787359126821203936495651 11681038690231805904743477)
              ·
                refine ⟨1095097377209231803569701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11681038690231805904743477 1095097377209231803569701)
                ·
                  refine ⟨205330758226730963169319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1095097377209231803569701 205330758226730963169319)
                  ·
                    rfl

theorem cell22_1799461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 5, 4].length) (baseStart_1799461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1799461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1799461 prefixEnd_1799461 := by exact prefixLift 1799461
  have htrace : WordTrace (prefixWord ++ tailWord_1799461) baseStart_1799461 baseEnd_1799461 := by
    simpa [prefixWord, tailWord_1799461, baseEnd_1799461] using wordTrace_append hprefix tailTrace_1799461
  have hstable : (prefixWord ++ tailWord_1799461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799461).length < 2 ^ (prefixWord ++ tailWord_1799461).sum := by decide
  have hdescent : baseEnd_1799461 < baseStart_1799461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799472 : List Nat := [2, 1, 1, 1, 2, 2, 13]
def baseStart_1799472 : Nat := 118140960795 + 1799472 * 2 ^ 59
def prefixEnd_1799472 : Nat := 4983230072969 + 3 ^ 40 * 1799472 * 2
def baseEnd_1799472 : Nat := 22814668155740463980849

theorem tailTrace_1799472 : CollatzResearch.WordTrace tailWord_1799472 prefixEnd_1799472 22814668155740463980849 := by
  unfold tailWord_1799472
  simp only [CollatzResearch.WordTrace]
  refine ⟨32816067868413872097644335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43754757157885162796859113 32816067868413872097644335)
  ·
    refine ⟨49224101802620808146466503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32816067868413872097644335 49224101802620808146466503)
    ·
      refine ⟨73836152703931212219699755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49224101802620808146466503 73836152703931212219699755)
      ·
        refine ⟨110754229055896818329549633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73836152703931212219699755 110754229055896818329549633)
        ·
          refine ⟨83065671791922613747162225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110754229055896818329549633 83065671791922613747162225)
          ·
            refine ⟨62299253843941960310371669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83065671791922613747162225 62299253843941960310371669)
            ·
              refine ⟨22814668155740463980849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 62299253843941960310371669 22814668155740463980849)
              ·
                rfl

theorem cell22_1799472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 13].length) (baseStart_1799472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1799472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1799472 prefixEnd_1799472 := by exact prefixLift 1799472
  have htrace : WordTrace (prefixWord ++ tailWord_1799472) baseStart_1799472 baseEnd_1799472 := by
    simpa [prefixWord, tailWord_1799472, baseEnd_1799472] using wordTrace_append hprefix tailTrace_1799472
  have hstable : (prefixWord ++ tailWord_1799472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799472).length < 2 ^ (prefixWord ++ tailWord_1799472).sum := by decide
  have hdescent : baseEnd_1799472 < baseStart_1799472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799549 : List Nat := [1, 4, 1, 1, 2, 2, 2, 1, 1, 7]
def baseStart_1799549 : Nat := 118140960795 + 1799549 * 2 ^ 59
def prefixEnd_1799549 : Nat := 4983230072969 + 3 ^ 40 * 1799549 * 2
def baseEnd_1799549 : Nat := 616022398878589993307687

theorem tailTrace_1799549 : CollatzResearch.WordTrace tailWord_1799549 prefixEnd_1799549 616022398878589993307687 := by
  unfold tailWord_1799549
  simp only [CollatzResearch.WordTrace]
  refine ⟨65634944157548786345841701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43756629438365857563894467 65634944157548786345841701)
  ·
    refine ⟨12306552029540397439845319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65634944157548786345841701 12306552029540397439845319)
    ·
      refine ⟨18459828044310596159767979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12306552029540397439845319 18459828044310596159767979)
      ·
        refine ⟨27689742066465894239651969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18459828044310596159767979 27689742066465894239651969)
        ·
          refine ⟨20767306549849420679738977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27689742066465894239651969 20767306549849420679738977)
          ·
            refine ⟨15575479912387065509804233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20767306549849420679738977 15575479912387065509804233)
            ·
              refine ⟨11681609934290299132353175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15575479912387065509804233 11681609934290299132353175)
              ·
                refine ⟨17522414901435448698529763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11681609934290299132353175 17522414901435448698529763)
                ·
                  refine ⟨26283622352153173047794645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17522414901435448698529763 26283622352153173047794645)
                  ·
                    refine ⟨616022398878589993307687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26283622352153173047794645 616022398878589993307687)
                    ·
                      rfl

theorem cell22_1799549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_1799549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1799549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1799549 prefixEnd_1799549 := by exact prefixLift 1799549
  have htrace : WordTrace (prefixWord ++ tailWord_1799549) baseStart_1799549 baseEnd_1799549 := by
    simpa [prefixWord, tailWord_1799549, baseEnd_1799549] using wordTrace_append hprefix tailTrace_1799549
  have hstable : (prefixWord ++ tailWord_1799549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799549).length < 2 ^ (prefixWord ++ tailWord_1799549).sum := by decide
  have hdescent : baseEnd_1799549 < baseStart_1799549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799626 : List Nat := [3, 1, 2, 1, 2, 4, 1, 1, 1, 6]
def baseStart_1799626 : Nat := 118140960795 + 1799626 * 2 ^ 59
def prefixEnd_1799626 : Nat := 4983230072969 + 3 ^ 40 * 1799626 * 2
def baseEnd_1799626 : Nat := 616048757552187459132451

theorem tailTrace_1799626 : CollatzResearch.WordTrace tailWord_1799626 prefixEnd_1799626 616048757552187459132451 := by
  unfold tailWord_1799626
  simp only [CollatzResearch.WordTrace]
  refine ⟨16409438144567457124098683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43758501718846552330929821 16409438144567457124098683)
  ·
    refine ⟨24614157216851185686148025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16409438144567457124098683 24614157216851185686148025)
    ·
      refine ⟨18460617912638389264611019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24614157216851185686148025 18460617912638389264611019)
      ·
        refine ⟨27690926868957583896916529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18460617912638389264611019 27690926868957583896916529)
        ·
          refine ⟨20768195151718187922687397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27690926868957583896916529 20768195151718187922687397)
          ·
            refine ⟨3894036590947160235503887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20768195151718187922687397 3894036590947160235503887)
            ·
              refine ⟨5841054886420740353255831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3894036590947160235503887 5841054886420740353255831)
              ·
                refine ⟨8761582329631110529883747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5841054886420740353255831 8761582329631110529883747)
                ·
                  refine ⟨13142373494446665794825621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8761582329631110529883747 13142373494446665794825621)
                  ·
                    refine ⟨616048757552187459132451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13142373494446665794825621 616048757552187459132451)
                    ·
                      rfl

theorem cell22_1799626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_1799626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1799626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1799626 prefixEnd_1799626 := by exact prefixLift 1799626
  have htrace : WordTrace (prefixWord ++ tailWord_1799626) baseStart_1799626 baseEnd_1799626 := by
    simpa [prefixWord, tailWord_1799626, baseEnd_1799626] using wordTrace_append hprefix tailTrace_1799626
  have hstable : (prefixWord ++ tailWord_1799626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799626).length < 2 ^ (prefixWord ++ tailWord_1799626).sum := by decide
  have hdescent : baseEnd_1799626 < baseStart_1799626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799639 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 1, 9]
def baseStart_1799639 : Nat := 118140960795 + 1799639 * 2 ^ 59
def prefixEnd_1799639 : Nat := 4983230072969 + 3 ^ 40 * 1799639 * 2
def baseEnd_1799639 : Nat := 616053207717859758557411

theorem tailTrace_1799639 : CollatzResearch.WordTrace tailWord_1799639 prefixEnd_1799639 616053207717859758557411 := by
  unfold tailWord_1799639
  simp only [CollatzResearch.WordTrace]
  refine ⟨65638226727222731716617971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43758817818148487811078647 65638226727222731716617971)
  ·
    refine ⟨98457340090834097574926957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65638226727222731716617971 98457340090834097574926957)
    ·
      refine ⟨36921502534062786590597609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98457340090834097574926957 36921502534062786590597609)
      ·
        refine ⟨27691126900547089942948207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36921502534062786590597609 27691126900547089942948207)
        ·
          refine ⟨41536690350820634914422311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27691126900547089942948207 41536690350820634914422311)
          ·
            refine ⟨62305035526230952371633467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41536690350820634914422311 62305035526230952371633467)
            ·
              refine ⟨93457553289346428557450201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62305035526230952371633467 93457553289346428557450201)
              ·
                refine ⟨70093164967009821418087651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93457553289346428557450201 70093164967009821418087651)
                ·
                  refine ⟨105139747450514732127131477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70093164967009821418087651 105139747450514732127131477)
                  ·
                    refine ⟨616053207717859758557411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 105139747450514732127131477 616053207717859758557411)
                    ·
                      rfl

theorem cell22_1799639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_1799639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1799639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1799639 prefixEnd_1799639 := by exact prefixLift 1799639
  have htrace : WordTrace (prefixWord ++ tailWord_1799639) baseStart_1799639 baseEnd_1799639 := by
    simpa [prefixWord, tailWord_1799639, baseEnd_1799639] using wordTrace_append hprefix tailTrace_1799639
  have hstable : (prefixWord ++ tailWord_1799639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799639).length < 2 ^ (prefixWord ++ tailWord_1799639).sum := by decide
  have hdescent : baseEnd_1799639 < baseStart_1799639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799645 : List Nat := [1, 4, 3, 1, 1, 2, 3, 2, 2, 3]
def baseStart_1799645 : Nat := 118140960795 + 1799645 * 2 ^ 59
def prefixEnd_1799645 : Nat := 4983230072969 + 3 ^ 40 * 1799645 * 2
def baseEnd_1799645 : Nat := 616055261640477742907393

theorem tailTrace_1799645 : CollatzResearch.WordTrace tailWord_1799645 prefixEnd_1799645 616055261640477742907393 := by
  unfold tailWord_1799645
  simp only [CollatzResearch.WordTrace]
  refine ⟨65638445565200994741336389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43758963710133996494224259 65638445565200994741336389)
  ·
    refine ⟨12307208543475186514000573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65638445565200994741336389 12307208543475186514000573)
    ·
      refine ⟨4615203203803194942750215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12307208543475186514000573 4615203203803194942750215)
      ·
        refine ⟨6922804805704792414125323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4615203203803194942750215 6922804805704792414125323)
        ·
          refine ⟨10384207208557188621187985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6922804805704792414125323 10384207208557188621187985)
          ·
            refine ⟨7788155406417891465890989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10384207208557188621187985 7788155406417891465890989)
            ·
              refine ⟨2920558277406709299709121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7788155406417891465890989 2920558277406709299709121)
              ·
                refine ⟨2190418708055031974781841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2920558277406709299709121 2190418708055031974781841)
                ·
                  refine ⟨1642814031041273981086381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2190418708055031974781841 1642814031041273981086381)
                  ·
                    refine ⟨616055261640477742907393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1642814031041273981086381 616055261640477742907393)
                    ·
                      rfl

theorem cell22_1799645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_1799645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1799645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1799645 prefixEnd_1799645 := by exact prefixLift 1799645
  have htrace : WordTrace (prefixWord ++ tailWord_1799645) baseStart_1799645 baseEnd_1799645 := by
    simpa [prefixWord, tailWord_1799645, baseEnd_1799645] using wordTrace_append hprefix tailTrace_1799645
  have hstable : (prefixWord ++ tailWord_1799645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799645).length < 2 ^ (prefixWord ++ tailWord_1799645).sum := by decide
  have hdescent : baseEnd_1799645 < baseStart_1799645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799720 : List Nat := [2, 1, 5, 2, 2, 1, 1, 3, 5]
def baseStart_1799720 : Nat := 118140960795 + 1799720 * 2 ^ 59
def prefixEnd_1799720 : Nat := 4983230072969 + 3 ^ 40 * 1799720 * 2
def baseEnd_1799720 : Nat := 205360311891067515760721

theorem tailTrace_1799720 : CollatzResearch.WordTrace tailWord_1799720 prefixEnd_1799720 205360311891067515760721 := by
  unfold tailWord_1799720
  simp only [CollatzResearch.WordTrace]
  refine ⟨32820590519964641275158307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43760787359952855033544409 32820590519964641275158307)
  ·
    refine ⟨49230885779946961912737461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32820590519964641275158307 49230885779946961912737461)
    ·
      refine ⟨4615395541870027679319137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49230885779946961912737461 4615395541870027679319137)
      ·
        refine ⟨3461546656402520759489353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4615395541870027679319137 3461546656402520759489353)
        ·
          refine ⟨2596159992301890569617015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3461546656402520759489353 2596159992301890569617015)
          ·
            refine ⟨3894239988452835854425523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2596159992301890569617015 3894239988452835854425523)
            ·
              refine ⟨5841359982679253781638285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3894239988452835854425523 5841359982679253781638285)
              ·
                refine ⟨2190509993504720168114357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5841359982679253781638285 2190509993504720168114357)
                ·
                  refine ⟨205360311891067515760721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2190509993504720168114357 205360311891067515760721)
                  ·
                    rfl

theorem cell22_1799720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3, 5].length) (baseStart_1799720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1799720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1799720 prefixEnd_1799720 := by exact prefixLift 1799720
  have htrace : WordTrace (prefixWord ++ tailWord_1799720) baseStart_1799720 baseEnd_1799720 := by
    simpa [prefixWord, tailWord_1799720, baseEnd_1799720] using wordTrace_append hprefix tailTrace_1799720
  have hstable : (prefixWord ++ tailWord_1799720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799720).length < 2 ^ (prefixWord ++ tailWord_1799720).sum := by decide
  have hdescent : baseEnd_1799720 < baseStart_1799720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799733 : List Nat := [1, 3, 3, 1, 1, 4, 1, 1, 3, 4]
def baseStart_1799733 : Nat := 118140960795 + 1799733 * 2 ^ 59
def prefixEnd_1799733 : Nat := 4983230072969 + 3 ^ 40 * 1799733 * 2
def baseEnd_1799733 : Nat := 616085385838874846707123

theorem tailTrace_1799733 : CollatzResearch.WordTrace tailWord_1799733 prefixEnd_1799733 616085385838874846707123 := by
  unfold tailWord_1799733
  simp only [CollatzResearch.WordTrace]
  refine ⟨65641655188882185770539853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43761103459254790513693235 65641655188882185770539853)
  ·
    refine ⟨24615620695830819663952445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65641655188882185770539853 24615620695830819663952445)
    ·
      refine ⟨9230857760936557373982167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24615620695830819663952445 9230857760936557373982167)
      ·
        refine ⟨13846286641404836060973251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9230857760936557373982167 13846286641404836060973251)
        ·
          refine ⟨20769429962107254091459877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13846286641404836060973251 20769429962107254091459877)
          ·
            refine ⟨3894268117895110142148727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20769429962107254091459877 3894268117895110142148727)
            ·
              refine ⟨5841402176842665213223091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3894268117895110142148727 5841402176842665213223091)
              ·
                refine ⟨8762103265263997819834637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5841402176842665213223091 8762103265263997819834637)
                ·
                  refine ⟨3285788724473999182437989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8762103265263997819834637 3285788724473999182437989)
                  ·
                    refine ⟨616085385838874846707123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3285788724473999182437989 616085385838874846707123)
                    ·
                      rfl

theorem cell22_1799733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_1799733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1799733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1799733 prefixEnd_1799733 := by exact prefixLift 1799733
  have htrace : WordTrace (prefixWord ++ tailWord_1799733) baseStart_1799733 baseEnd_1799733 := by
    simpa [prefixWord, tailWord_1799733, baseEnd_1799733] using wordTrace_append hprefix tailTrace_1799733
  have hstable : (prefixWord ++ tailWord_1799733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799733).length < 2 ^ (prefixWord ++ tailWord_1799733).sum := by decide
  have hdescent : baseEnd_1799733 < baseStart_1799733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799780 : List Nat := [2, 3, 1, 1, 2, 3, 2, 3, 2, 3]
def baseStart_1799780 : Nat := 118140960795 + 1799780 * 2 ^ 59
def prefixEnd_1799780 : Nat := 4983230072969 + 3 ^ 40 * 1799780 * 2
def baseEnd_1799780 : Nat := 616101474899382390781979

theorem tailTrace_1799780 : CollatzResearch.WordTrace tailWord_1799780 prefixEnd_1799780 616101474899382390781979 := by
  unfold tailWord_1799780
  simp only [CollatzResearch.WordTrace]
  refine ⟨32821684709855956398750397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43762246279807941865000529 32821684709855956398750397)
  ·
    refine ⟨12308131766195983649531399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32821684709855956398750397 12308131766195983649531399)
    ·
      refine ⟨18462197649293975474297099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12308131766195983649531399 18462197649293975474297099)
      ·
        refine ⟨27693296473940963211445649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18462197649293975474297099 27693296473940963211445649)
        ·
          refine ⟨20769972355455722408584237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27693296473940963211445649 20769972355455722408584237)
          ·
            refine ⟨7788739633295895903219089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20769972355455722408584237 7788739633295895903219089)
            ·
              refine ⟨5841554724971921927414317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7788739633295895903219089 5841554724971921927414317)
              ·
                refine ⟨2190583021864470722780369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5841554724971921927414317 2190583021864470722780369)
                ·
                  refine ⟨1642937266398353042085277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2190583021864470722780369 1642937266398353042085277)
                  ·
                    refine ⟨616101474899382390781979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1642937266398353042085277 616101474899382390781979)
                    ·
                      rfl

theorem cell22_1799780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3, 2, 3].length) (baseStart_1799780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1799780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1799780 prefixEnd_1799780 := by exact prefixLift 1799780
  have htrace : WordTrace (prefixWord ++ tailWord_1799780) baseStart_1799780 baseEnd_1799780 := by
    simpa [prefixWord, tailWord_1799780, baseEnd_1799780] using wordTrace_append hprefix tailTrace_1799780
  have hstable : (prefixWord ++ tailWord_1799780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799780).length < 2 ^ (prefixWord ++ tailWord_1799780).sum := by decide
  have hdescent : baseEnd_1799780 < baseStart_1799780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799808 : List Nat := [2, 1, 1, 2, 1, 4, 1, 2, 5, 3]
def baseStart_1799808 : Nat := 118140960795 + 1799808 * 2 ^ 59
def prefixEnd_1799808 : Nat := 4983230072969 + 3 ^ 40 * 1799808 * 2
def baseEnd_1799808 : Nat := 616111059871599651081893

theorem tailTrace_1799808 : CollatzResearch.WordTrace tailWord_1799808 prefixEnd_1799808 616111059871599651081893 := by
  unfold tailWord_1799808
  simp only [CollatzResearch.WordTrace]
  refine ⟨32822195331805236789760039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43762927109073649053013385 32822195331805236789760039)
  ·
    refine ⟨49233292997707855184640059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32822195331805236789760039 49233292997707855184640059)
    ·
      refine ⟨73849939496561782776960089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49233292997707855184640059 73849939496561782776960089)
      ·
        refine ⟨55387454622421337082720067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73849939496561782776960089 55387454622421337082720067)
        ·
          refine ⟨83081181933632005624080101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55387454622421337082720067 83081181933632005624080101)
          ·
            refine ⟨15577721612556001054515019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83081181933632005624080101 15577721612556001054515019)
            ·
              refine ⟨23366582418834001581772529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15577721612556001054515019 23366582418834001581772529)
              ·
                refine ⟨17524936814125501186329397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23366582418834001581772529 17524936814125501186329397)
                ·
                  refine ⟨1642962826324265736218381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17524936814125501186329397 1642962826324265736218381)
                  ·
                    refine ⟨616111059871599651081893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1642962826324265736218381 616111059871599651081893)
                    ·
                      rfl

theorem cell22_1799808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 5, 3].length) (baseStart_1799808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1799808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1799808 prefixEnd_1799808 := by exact prefixLift 1799808
  have htrace : WordTrace (prefixWord ++ tailWord_1799808) baseStart_1799808 baseEnd_1799808 := by
    simpa [prefixWord, tailWord_1799808, baseEnd_1799808] using wordTrace_append hprefix tailTrace_1799808
  have hstable : (prefixWord ++ tailWord_1799808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799808).length < 2 ^ (prefixWord ++ tailWord_1799808).sum := by decide
  have hdescent : baseEnd_1799808 < baseStart_1799808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799932 : List Nat := [2, 2, 2, 1, 3, 1, 4, 2, 2, 3]
def baseStart_1799932 : Nat := 118140960795 + 1799932 * 2 ^ 59
def prefixEnd_1799932 : Nat := 4983230072969 + 3 ^ 40 * 1799932 * 2
def baseEnd_1799932 : Nat := 616153507605704660981513

theorem tailTrace_1799932 : CollatzResearch.WordTrace tailWord_1799932 prefixEnd_1799932 616153507605704660981513 := by
  unfold tailWord_1799932
  simp only [CollatzResearch.WordTrace]
  refine ⟨32824456657580621378517025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43765942210107495171356033 32824456657580621378517025)
  ·
    refine ⟨24618342493185466033887769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32824456657580621378517025 24618342493185466033887769)
    ·
      refine ⟨18463756869889099525415827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24618342493185466033887769 18463756869889099525415827)
      ·
        refine ⟨27695635304833649288123741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18463756869889099525415827 27695635304833649288123741)
        ·
          refine ⟨10385863239312618483046403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27695635304833649288123741 10385863239312618483046403)
          ·
            refine ⟨15578794858968927724569605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10385863239312618483046403 15578794858968927724569605)
            ·
              refine ⟨2921024036056673948356801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15578794858968927724569605 2921024036056673948356801)
              ·
                refine ⟨2190768027042505461267601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2921024036056673948356801 2190768027042505461267601)
                ·
                  refine ⟨1643076020281879095950701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2190768027042505461267601 1643076020281879095950701)
                  ·
                    refine ⟨616153507605704660981513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1643076020281879095950701 616153507605704660981513)
                    ·
                      rfl

theorem cell22_1799932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2, 2, 3].length) (baseStart_1799932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1799932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1799932 prefixEnd_1799932 := by exact prefixLift 1799932
  have htrace : WordTrace (prefixWord ++ tailWord_1799932) baseStart_1799932 baseEnd_1799932 := by
    simpa [prefixWord, tailWord_1799932, baseEnd_1799932] using wordTrace_append hprefix tailTrace_1799932
  have hstable : (prefixWord ++ tailWord_1799932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799932).length < 2 ^ (prefixWord ++ tailWord_1799932).sum := by decide
  have hdescent : baseEnd_1799932 < baseStart_1799932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799934 : List Nat := [4, 2, 2, 1, 3, 1, 1, 4, 4]
def baseStart_1799934 : Nat := 118140960795 + 1799934 * 2 ^ 59
def prefixEnd_1799934 : Nat := 4983230072969 + 3 ^ 40 * 1799934 * 2
def baseEnd_1799934 : Nat := 205384730748859107477169

theorem tailTrace_1799934 : CollatzResearch.WordTrace tailWord_1799934 prefixEnd_1799934 205384730748859107477169 := by
  unfold tailWord_1799934
  simp only [CollatzResearch.WordTrace]
  refine ⟨8206123282644249637325857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43765990840769331399071237 8206123282644249637325857)
  ·
    refine ⟨6154592461983187227994393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8206123282644249637325857 6154592461983187227994393)
    ·
      refine ⟨4615944346487390420995795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6154592461983187227994393 4615944346487390420995795)
      ·
        refine ⟨6923916519731085631493693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4615944346487390420995795 6923916519731085631493693)
        ·
          refine ⟨2596468694899157111810135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6923916519731085631493693 2596468694899157111810135)
          ·
            refine ⟨3894703042348735667715203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2596468694899157111810135 3894703042348735667715203)
            ·
              refine ⟨5842054563523103501572805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3894703042348735667715203 5842054563523103501572805)
              ·
                refine ⟨1095385230660581906544901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5842054563523103501572805 1095385230660581906544901)
                ·
                  refine ⟨205384730748859107477169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1095385230660581906544901 205384730748859107477169)
                  ·
                    rfl

theorem cell22_1799934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_1799934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1799934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1799934 prefixEnd_1799934 := by exact prefixLift 1799934
  have htrace : WordTrace (prefixWord ++ tailWord_1799934) baseStart_1799934 baseEnd_1799934 := by
    simpa [prefixWord, tailWord_1799934, baseEnd_1799934] using wordTrace_append hprefix tailTrace_1799934
  have hstable : (prefixWord ++ tailWord_1799934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799934).length < 2 ^ (prefixWord ++ tailWord_1799934).sum := by decide
  have hdescent : baseEnd_1799934 < baseStart_1799934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799960 : List Nat := [2, 1, 2, 3, 1, 1, 3, 1, 5, 3]
def baseStart_1799960 : Nat := 118140960795 + 1799960 * 2 ^ 59
def prefixEnd_1799960 : Nat := 4983230072969 + 3 ^ 40 * 1799960 * 2
def baseEnd_1799960 : Nat := 616163092577921921281427

theorem tailTrace_1799960 : CollatzResearch.WordTrace tailWord_1799960 prefixEnd_1799960 616163092577921921281427 := by
  unfold tailWord_1799960
  simp only [CollatzResearch.WordTrace]
  refine ⟨32824967279529901769526667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43766623039373202359368889 32824967279529901769526667)
  ·
    refine ⟨49237450919294852654290001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32824967279529901769526667 49237450919294852654290001)
    ·
      refine ⟨36928088189471139490717501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49237450919294852654290001 36928088189471139490717501)
      ·
        refine ⟨13848033071051677309019063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36928088189471139490717501 13848033071051677309019063)
        ·
          refine ⟨20772049606577515963528595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13848033071051677309019063 20772049606577515963528595)
          ·
            refine ⟨31158074409866273945292893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20772049606577515963528595 31158074409866273945292893)
            ·
              refine ⟨11684277903699852729484835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31158074409866273945292893 11684277903699852729484835)
              ·
                refine ⟨17526416855549779094227253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11684277903699852729484835 17526416855549779094227253)
                ·
                  refine ⟨1643101580207791790083805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17526416855549779094227253 1643101580207791790083805)
                  ·
                    refine ⟨616163092577921921281427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1643101580207791790083805 616163092577921921281427)
                    ·
                      rfl

theorem cell22_1799960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 5, 3].length) (baseStart_1799960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1799960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1799960 prefixEnd_1799960 := by exact prefixLift 1799960
  have htrace : WordTrace (prefixWord ++ tailWord_1799960) baseStart_1799960 baseEnd_1799960 := by
    simpa [prefixWord, tailWord_1799960, baseEnd_1799960] using wordTrace_append hprefix tailTrace_1799960
  have hstable : (prefixWord ++ tailWord_1799960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799960).length < 2 ^ (prefixWord ++ tailWord_1799960).sum := by decide
  have hdescent : baseEnd_1799960 < baseStart_1799960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799994 : List Nat := [3, 1, 1, 1, 5, 1, 2, 4, 1, 3]
def baseStart_1799994 : Nat := 118140960795 + 1799994 * 2 ^ 59
def prefixEnd_1799994 : Nat := 4983230072969 + 3 ^ 40 * 1799994 * 2
def baseEnd_1799994 : Nat := 616174731472757165931323

theorem tailTrace_1799994 : CollatzResearch.WordTrace tailWord_1799994 prefixEnd_1799994 616174731472757165931323 := by
  unfold tailWord_1799994
  simp only [CollatzResearch.WordTrace]
  refine ⟨16412793660234156836447759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43767449760624418230527357 16412793660234156836447759)
  ·
    refine ⟨24619190490351235254671639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16412793660234156836447759 24619190490351235254671639)
    ·
      refine ⟨36928785735526852882007459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24619190490351235254671639 36928785735526852882007459)
      ·
        refine ⟨55393178603290279323011189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36928785735526852882007459 55393178603290279323011189)
        ·
          refine ⟨5193110494058463686532299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55393178603290279323011189 5193110494058463686532299)
          ·
            refine ⟨7789665741087695529798449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5193110494058463686532299 7789665741087695529798449)
            ·
              refine ⟨5842249305815771647348837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7789665741087695529798449 5842249305815771647348837)
              ·
                refine ⟨1095421744840457183877907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5842249305815771647348837 1095421744840457183877907)
                ·
                  refine ⟨1643132617260685775816861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1095421744840457183877907 1643132617260685775816861)
                  ·
                    refine ⟨616174731472757165931323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1643132617260685775816861 616174731472757165931323)
                    ·
                      rfl

theorem cell22_1799994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 4, 1, 3].length) (baseStart_1799994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1799994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1799994 prefixEnd_1799994 := by exact prefixLift 1799994
  have htrace : WordTrace (prefixWord ++ tailWord_1799994) baseStart_1799994 baseEnd_1799994 := by
    simpa [prefixWord, tailWord_1799994, baseEnd_1799994] using wordTrace_append hprefix tailTrace_1799994
  have hstable : (prefixWord ++ tailWord_1799994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799994).length < 2 ^ (prefixWord ++ tailWord_1799994).sum := by decide
  have hdescent : baseEnd_1799994 < baseStart_1799994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800028 : List Nat := [2, 2, 4, 2, 2, 2, 1, 3, 1, 3]
def baseStart_1800028 : Nat := 118140960795 + 1800028 * 2 ^ 59
def prefixEnd_1800028 : Nat := 4983230072969 + 3 ^ 40 * 1800028 * 2
def baseEnd_1800028 : Nat := 616186370367592410581219

theorem tailTrace_1800028 : CollatzResearch.WordTrace tailWord_1800028 prefixEnd_1800028 616186370367592410581219 := by
  unfold tailWord_1800028
  simp only [CollatzResearch.WordTrace]
  refine ⟨32826207361406725576264369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43768276481875634101685825 32826207361406725576264369)
  ·
    refine ⟨24619655521055044182198277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32826207361406725576264369 24619655521055044182198277)
    ·
      refine ⟨4616185410197820784162177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24619655521055044182198277 4616185410197820784162177)
      ·
        refine ⟨3462139057648365588121633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4616185410197820784162177 3462139057648365588121633)
        ·
          refine ⟨2596604293236274191091225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3462139057648365588121633 2596604293236274191091225)
          ·
            refine ⟨1947453219927205643318419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2596604293236274191091225 1947453219927205643318419)
            ·
              refine ⟨2921179829890808464977629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1947453219927205643318419 2921179829890808464977629)
              ·
                refine ⟨1095442436209053174366611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2921179829890808464977629 1095442436209053174366611)
                ·
                  refine ⟨1643163654313579761549917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1095442436209053174366611 1643163654313579761549917)
                  ·
                    refine ⟨616186370367592410581219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1643163654313579761549917 616186370367592410581219)
                    ·
                      rfl

theorem cell22_1800028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_1800028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1800028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1800028 prefixEnd_1800028 := by exact prefixLift 1800028
  have htrace : WordTrace (prefixWord ++ tailWord_1800028) baseStart_1800028 baseEnd_1800028 := by
    simpa [prefixWord, tailWord_1800028, baseEnd_1800028] using wordTrace_append hprefix tailTrace_1800028
  have hstable : (prefixWord ++ tailWord_1800028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800028).length < 2 ^ (prefixWord ++ tailWord_1800028).sum := by decide
  have hdescent : baseEnd_1800028 < baseStart_1800028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800071 : List Nat := [1, 1, 4, 2, 5, 1, 1, 2, 1, 4]
def baseStart_1800071 : Nat := 118140960795 + 1800071 * 2 ^ 59
def prefixEnd_1800071 : Nat := 4983230072969 + 3 ^ 40 * 1800071 * 2
def baseEnd_1800071 : Nat := 616201090146354631756087

theorem tailTrace_1800071 : CollatzResearch.WordTrace tailWord_1800071 prefixEnd_1800071 616201090146354631756087 := by
  unfold tailWord_1800071
  simp only [CollatzResearch.WordTrace]
  refine ⟨65653983061657669496344067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43769322041105112997562711 65653983061657669496344067)
  ·
    refine ⟨98480974592486504244516101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65653983061657669496344067 98480974592486504244516101)
    ·
      refine ⟨18465182736091219545846769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98480974592486504244516101 18465182736091219545846769)
      ·
        refine ⟨13848887052068414659385077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18465182736091219545846769 13848887052068414659385077)
        ·
          refine ⟨1298333161131413874317351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13848887052068414659385077 1298333161131413874317351)
          ·
            refine ⟨1947499741697120811476027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1298333161131413874317351 1947499741697120811476027)
            ·
              refine ⟨2921249612545681217214041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1947499741697120811476027 2921249612545681217214041)
              ·
                refine ⟨2190937209409260912910531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2921249612545681217214041 2190937209409260912910531)
                ·
                  refine ⟨3286405814113891369365797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2190937209409260912910531 3286405814113891369365797)
                  ·
                    refine ⟨616201090146354631756087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3286405814113891369365797 616201090146354631756087)
                    ·
                      rfl

theorem cell22_1800071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 2, 1, 4].length) (baseStart_1800071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1800071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1800071 prefixEnd_1800071 := by exact prefixLift 1800071
  have htrace : WordTrace (prefixWord ++ tailWord_1800071) baseStart_1800071 baseEnd_1800071 := by
    simpa [prefixWord, tailWord_1800071, baseEnd_1800071] using wordTrace_append hprefix tailTrace_1800071
  have hstable : (prefixWord ++ tailWord_1800071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800071).length < 2 ^ (prefixWord ++ tailWord_1800071).sum := by decide
  have hdescent : baseEnd_1800071 < baseStart_1800071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800097 : List Nat := [1, 2, 3, 4, 3, 9]
def baseStart_1800097 : Nat := 118140960795 + 1800097 * 2 ^ 59
def prefixEnd_1800097 : Nat := 4983230072969 + 3 ^ 40 * 1800097 * 2
def baseEnd_1800097 : Nat := 7607530746638262106247

theorem tailTrace_1800097 : CollatzResearch.WordTrace tailWord_1800097 prefixEnd_1800097 7607530746638262106247 := by
  unfold tailWord_1800097
  simp only [CollatzResearch.WordTrace]
  refine ⟨65654931359563475936790545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43769954239708983957860363 65654931359563475936790545)
  ·
    refine ⟨49241198519672606952592909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65654931359563475936790545 49241198519672606952592909)
    ·
      refine ⟨18465449444877227607222341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49241198519672606952592909 18465449444877227607222341)
      ·
        refine ⟨3462271770914480176354189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18465449444877227607222341 3462271770914480176354189)
        ·
          refine ⟨1298351914092930066132821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3462271770914480176354189 1298351914092930066132821)
          ·
            refine ⟨7607530746638262106247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1298351914092930066132821 7607530746638262106247)
            ·
              rfl

theorem cell22_1800097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 9].length) (baseStart_1800097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1800097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1800097 prefixEnd_1800097 := by exact prefixLift 1800097
  have htrace : WordTrace (prefixWord ++ tailWord_1800097) baseStart_1800097 baseEnd_1800097 := by
    simpa [prefixWord, tailWord_1800097, baseEnd_1800097] using wordTrace_append hprefix tailTrace_1800097
  have hstable : (prefixWord ++ tailWord_1800097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800097).length < 2 ^ (prefixWord ++ tailWord_1800097).sum := by decide
  have hdescent : baseEnd_1800097 < baseStart_1800097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800159 : List Nat := [1, 1, 2, 3, 4, 3, 1, 2, 5]
def baseStart_1800159 : Nat := 118140960795 + 1800159 * 2 ^ 59
def prefixEnd_1800159 : Nat := 4983230072969 + 3 ^ 40 * 1800159 * 2
def baseEnd_1800159 : Nat := 205410404781583911851939

theorem tailTrace_1800159 : CollatzResearch.WordTrace tailWord_1800159 prefixEnd_1800159 205410404781583911851939 := by
  unfold tailWord_1800159
  simp only [CollatzResearch.WordTrace]
  refine ⟨65657192685338860525547531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43771461790225907017031687 65657192685338860525547531)
  ·
    refine ⟨98485789028008290788321297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65657192685338860525547531 98485789028008290788321297)
    ·
      refine ⟨73864341771006218091240973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98485789028008290788321297 73864341771006218091240973)
      ·
        refine ⟨27699128164127331784215365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73864341771006218091240973 27699128164127331784215365)
        ·
          refine ⟨5193586530773874709540381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27699128164127331784215365 5193586530773874709540381)
          ·
            refine ⟨1947594949040203016077643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5193586530773874709540381 1947594949040203016077643)
            ·
              refine ⟨2921392423560304524116465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1947594949040203016077643 2921392423560304524116465)
              ·
                refine ⟨2191044317670228393087349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2921392423560304524116465 2191044317670228393087349)
                ·
                  refine ⟨205410404781583911851939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2191044317670228393087349 205410404781583911851939)
                  ·
                    rfl

theorem cell22_1800159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 2, 5].length) (baseStart_1800159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1800159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1800159 prefixEnd_1800159 := by exact prefixLift 1800159
  have htrace : WordTrace (prefixWord ++ tailWord_1800159) baseStart_1800159 baseEnd_1800159 := by
    simpa [prefixWord, tailWord_1800159, baseEnd_1800159] using wordTrace_append hprefix tailTrace_1800159
  have hstable : (prefixWord ++ tailWord_1800159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800159).length < 2 ^ (prefixWord ++ tailWord_1800159).sum := by decide
  have hdescent : baseEnd_1800159 < baseStart_1800159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800281 : List Nat := [1, 2, 1, 2, 2, 1, 5, 4, 1, 3]
def baseStart_1800281 : Nat := 118140960795 + 1800281 * 2 ^ 59
def prefixEnd_1800281 : Nat := 4983230072969 + 3 ^ 40 * 1800281 * 2
def baseEnd_1800281 : Nat := 616272977437984084005443

theorem tailTrace_1800281 : CollatzResearch.WordTrace tailWord_1800281 prefixEnd_1800281 616272977437984084005443 := by
  unfold tailWord_1800281
  simp only [CollatzResearch.WordTrace]
  refine ⟨65661642390896875361488697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43774428260597916907659131 65661642390896875361488697)
  ·
    refine ⟨49246231793172656521116523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65661642390896875361488697 49246231793172656521116523)
    ·
      refine ⟨73869347689758984781674785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49246231793172656521116523 73869347689758984781674785)
      ·
        refine ⟨55402010767319238586256089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73869347689758984781674785 55402010767319238586256089)
        ·
          refine ⟨41551508075489428939692067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55402010767319238586256089 41551508075489428939692067)
          ·
            refine ⟨62327262113234143409538101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41551508075489428939692067 62327262113234143409538101)
            ·
              refine ⟨5843180823115700944644197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62327262113234143409538101 5843180823115700944644197)
              ·
                refine ⟨1095596404334193927120787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5843180823115700944644197 1095596404334193927120787)
                ·
                  refine ⟨1643394606501290890681181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1095596404334193927120787 1643394606501290890681181)
                  ·
                    refine ⟨616272977437984084005443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1643394606501290890681181 616272977437984084005443)
                    ·
                      rfl

theorem cell22_1800281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 4, 1, 3].length) (baseStart_1800281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1800281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1800281 prefixEnd_1800281 := by exact prefixLift 1800281
  have htrace : WordTrace (prefixWord ++ tailWord_1800281) baseStart_1800281 baseEnd_1800281 := by
    simpa [prefixWord, tailWord_1800281, baseEnd_1800281] using wordTrace_append hprefix tailTrace_1800281
  have hstable : (prefixWord ++ tailWord_1800281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800281).length < 2 ^ (prefixWord ++ tailWord_1800281).sum := by decide
  have hdescent : baseEnd_1800281 < baseStart_1800281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800292 : List Nat := [2, 3, 1, 1, 2, 1, 3, 1, 1, 7]
def baseStart_1800292 : Nat := 118140960795 + 1800292 * 2 ^ 59
def prefixEnd_1800292 : Nat := 4983230072969 + 3 ^ 40 * 1800292 * 2
def baseEnd_1800292 : Nat := 616276742962783721980409

theorem tailTrace_1800292 : CollatzResearch.WordTrace tailWord_1800292 prefixEnd_1800292 616276742962783721980409 := by
  unfold tailWord_1800292
  simp only [CollatzResearch.WordTrace]
  refine ⟨32831021796928512120069565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43774695729238016160092753 32831021796928512120069565)
  ·
    refine ⟨12311633173848192045026087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32831021796928512120069565 12311633173848192045026087)
    ·
      refine ⟨18467449760772288067539131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12311633173848192045026087 18467449760772288067539131)
      ·
        refine ⟨27701174641158432101308697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18467449760772288067539131 27701174641158432101308697)
        ·
          refine ⟨20775880980868824075981523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27701174641158432101308697 20775880980868824075981523)
          ·
            refine ⟨31163821471303236113972285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20775880980868824075981523 31163821471303236113972285)
            ·
              refine ⟨11686433051738713542739607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31163821471303236113972285 11686433051738713542739607)
              ·
                refine ⟨17529649577608070314109411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11686433051738713542739607 17529649577608070314109411)
                ·
                  refine ⟨26294474366412105471164117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17529649577608070314109411 26294474366412105471164117)
                  ·
                    refine ⟨616276742962783721980409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26294474366412105471164117 616276742962783721980409)
                    ·
                      rfl

theorem cell22_1800292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_1800292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1800292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1800292 prefixEnd_1800292 := by exact prefixLift 1800292
  have htrace : WordTrace (prefixWord ++ tailWord_1800292) baseStart_1800292 baseEnd_1800292 := by
    simpa [prefixWord, tailWord_1800292, baseEnd_1800292] using wordTrace_append hprefix tailTrace_1800292
  have hstable : (prefixWord ++ tailWord_1800292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800292).length < 2 ^ (prefixWord ++ tailWord_1800292).sum := by decide
  have hdescent : baseEnd_1800292 < baseStart_1800292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800384 : List Nat := [2, 1, 1, 2, 5, 3, 8]
def baseStart_1800384 : Nat := 118140960795 + 1800384 * 2 ^ 59
def prefixEnd_1800384 : Nat := 4983230072969 + 3 ^ 40 * 1800384 * 2
def baseEnd_1800384 : Nat := 22826230979367635136301

theorem tailTrace_1800384 : CollatzResearch.WordTrace tailWord_1800384 prefixEnd_1800384 22826230979367635136301 := by
  unfold tailWord_1800384
  simp only [CollatzResearch.WordTrace]
  refine ⟨32832699554761861976244103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43776932739682482634992137 32832699554761861976244103)
  ·
    refine ⟨49249049332142792964366155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32832699554761861976244103 49249049332142792964366155)
    ·
      refine ⟨73873573998214189446549233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49249049332142792964366155 73873573998214189446549233)
      ·
        refine ⟨55405180498660642084911925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73873573998214189446549233 55405180498660642084911925)
        ·
          refine ⟨5194235671749435195460493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55405180498660642084911925 5194235671749435195460493)
          ·
            refine ⟨1947838376906038198297685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5194235671749435195460493 1947838376906038198297685)
            ·
              refine ⟨22826230979367635136301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1947838376906038198297685 22826230979367635136301)
              ·
                rfl

theorem cell22_1800384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 8].length) (baseStart_1800384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1800384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1800384 prefixEnd_1800384 := by exact prefixLift 1800384
  have htrace : WordTrace (prefixWord ++ tailWord_1800384) baseStart_1800384 baseEnd_1800384 := by
    simpa [prefixWord, tailWord_1800384, baseEnd_1800384] using wordTrace_append hprefix tailTrace_1800384
  have hstable : (prefixWord ++ tailWord_1800384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800384).length < 2 ^ (prefixWord ++ tailWord_1800384).sum := by decide
  have hdescent : baseEnd_1800384 < baseStart_1800384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800459 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 5, 4]
def baseStart_1800459 : Nat := 118140960795 + 1800459 * 2 ^ 59
def prefixEnd_1800459 : Nat := 4983230072969 + 3 ^ 40 * 1800459 * 2
def baseEnd_1800459 : Nat := 616333910475650953054897

theorem tailTrace_1800459 : CollatzResearch.WordTrace tailWord_1800459 prefixEnd_1800459 616333910475650953054897 := by
  unfold tailWord_1800459
  simp only [CollatzResearch.WordTrace]
  refine ⟨65668134584252011761468431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43778756389501341174312287 65668134584252011761468431)
  ·
    refine ⟨98502201876378017642202647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65668134584252011761468431 98502201876378017642202647)
    ·
      refine ⟨147753302814567026463303971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98502201876378017642202647 147753302814567026463303971)
      ·
        refine ⟨221629954221850539694955957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147753302814567026463303971 221629954221850539694955957)
        ·
          refine ⟨20777808208298488096402121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 221629954221850539694955957 20777808208298488096402121)
          ·
            refine ⟨15583356156223866072301591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20777808208298488096402121 15583356156223866072301591)
            ·
              refine ⟨23375034234335799108452387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15583356156223866072301591 23375034234335799108452387)
              ·
                refine ⟨35062551351503698662678581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23375034234335799108452387 35062551351503698662678581)
                ·
                  refine ⟨3287114189203471749626117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35062551351503698662678581 3287114189203471749626117)
                  ·
                    refine ⟨616333910475650953054897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3287114189203471749626117 616333910475650953054897)
                    ·
                      rfl

theorem cell22_1800459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5, 4].length) (baseStart_1800459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1800459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1800459 prefixEnd_1800459 := by exact prefixLift 1800459
  have htrace : WordTrace (prefixWord ++ tailWord_1800459) baseStart_1800459 baseEnd_1800459 := by
    simpa [prefixWord, tailWord_1800459, baseEnd_1800459] using wordTrace_append hprefix tailTrace_1800459
  have hstable : (prefixWord ++ tailWord_1800459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800459).length < 2 ^ (prefixWord ++ tailWord_1800459).sum := by decide
  have hdescent : baseEnd_1800459 < baseStart_1800459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800476 : List Nat := [2, 2, 3, 1, 1, 1, 1, 6, 1, 4]
def baseStart_1800476 : Nat := 118140960795 + 1800476 * 2 ^ 59
def prefixEnd_1800476 : Nat := 4983230072969 + 3 ^ 40 * 1800476 * 2
def baseEnd_1800476 : Nat := 616339729923068575379845

theorem tailTrace_1800476 : CollatzResearch.WordTrace tailWord_1800476 prefixEnd_1800476 616339729923068575379845 := by
  unfold tailWord_1800476
  simp only [CollatzResearch.WordTrace]
  refine ⟨32834377312595211832418641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43779169750126949109891521 32834377312595211832418641)
  ·
    refine ⟨24625782984446408874313981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32834377312595211832418641 24625782984446408874313981)
    ·
      refine ⟨9234668619167403327867743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24625782984446408874313981 9234668619167403327867743)
      ·
        refine ⟨13852002928751104991801615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9234668619167403327867743 13852002928751104991801615)
        ·
          refine ⟨20778004393126657487702423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13852002928751104991801615 20778004393126657487702423)
          ·
            refine ⟨31167006589689986231553635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20778004393126657487702423 31167006589689986231553635)
            ·
              refine ⟨46750509884534979347330453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31167006589689986231553635 46750509884534979347330453)
              ·
                refine ⟨2191430150837577156906115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46750509884534979347330453 2191430150837577156906115)
                ·
                  refine ⟨3287145226256365735359173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2191430150837577156906115 3287145226256365735359173)
                  ·
                    refine ⟨616339729923068575379845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3287145226256365735359173 616339729923068575379845)
                    ·
                      rfl

theorem cell22_1800476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_1800476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1800476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1800476 prefixEnd_1800476 := by exact prefixLift 1800476
  have htrace : WordTrace (prefixWord ++ tailWord_1800476) baseStart_1800476 baseEnd_1800476 := by
    simpa [prefixWord, tailWord_1800476, baseEnd_1800476] using wordTrace_append hprefix tailTrace_1800476
  have hstable : (prefixWord ++ tailWord_1800476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800476).length < 2 ^ (prefixWord ++ tailWord_1800476).sum := by decide
  have hdescent : baseEnd_1800476 < baseStart_1800476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800519 : List Nat := [1, 1, 4, 1, 2, 2, 2, 9]
def baseStart_1800519 : Nat := 118140960795 + 1800519 * 2 ^ 59
def prefixEnd_1800519 : Nat := 4983230072969 + 3 ^ 40 * 1800519 * 2
def baseEnd_1800519 : Nat := 68483827744647866283857

theorem tailTrace_1800519 : CollatzResearch.WordTrace tailWord_1800519 prefixEnd_1800519 68483827744647866283857 := by
  unfold tailWord_1800519
  simp only [CollatzResearch.WordTrace]
  refine ⟨65670322964034642008652611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43780215309356428005768407 65670322964034642008652611)
  ·
    refine ⟨98505484446051963012978917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65670322964034642008652611 98505484446051963012978917)
    ·
      refine ⟨18469778333634743064933547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98505484446051963012978917 18469778333634743064933547)
      ·
        refine ⟨27704667500452114597400321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18469778333634743064933547 27704667500452114597400321)
        ·
          refine ⟨20778500625339085948050241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27704667500452114597400321 20778500625339085948050241)
          ·
            refine ⟨15583875469004314461037681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20778500625339085948050241 15583875469004314461037681)
            ·
              refine ⟨11687906601753235845778261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15583875469004314461037681 11687906601753235845778261)
              ·
                refine ⟨68483827744647866283857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11687906601753235845778261 68483827744647866283857)
                ·
                  rfl

theorem cell22_1800519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 9].length) (baseStart_1800519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1800519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1800519 prefixEnd_1800519 := by exact prefixLift 1800519
  have htrace : WordTrace (prefixWord ++ tailWord_1800519) baseStart_1800519 baseEnd_1800519 := by
    simpa [prefixWord, tailWord_1800519, baseEnd_1800519] using wordTrace_append hprefix tailTrace_1800519
  have hstable : (prefixWord ++ tailWord_1800519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800519).length < 2 ^ (prefixWord ++ tailWord_1800519).sum := by decide
  have hdescent : baseEnd_1800519 < baseStart_1800519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800626 : List Nat := [3, 2, 1, 1, 1, 1, 4, 3, 6]
def baseStart_1800626 : Nat := 118140960795 + 1800626 * 2 ^ 59
def prefixEnd_1800626 : Nat := 4983230072969 + 3 ^ 40 * 1800626 * 2
def baseEnd_1800626 : Nat := 205463692662839394709795

theorem tailTrace_1800626 : CollatzResearch.WordTrace tailWord_1800626 prefixEnd_1800626 205463692662839394709795 := by
  unfold tailWord_1800626
  simp only [CollatzResearch.WordTrace]
  refine ⟨16418556393661749820699433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43782817049764666188531821 16418556393661749820699433)
  ·
    refine ⟨12313917295246312365524575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16418556393661749820699433 12313917295246312365524575)
    ·
      refine ⟨18470875942869468548286863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12313917295246312365524575 18470875942869468548286863)
      ·
        refine ⟨27706313914304202822430295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18470875942869468548286863 27706313914304202822430295)
        ·
          refine ⟨41559470871456304233645443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27706313914304202822430295 41559470871456304233645443)
          ·
            refine ⟨62339206307184456350468165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41559470871456304233645443 62339206307184456350468165)
            ·
              refine ⟨11688601182597085565712781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62339206307184456350468165 11688601182597085565712781)
              ·
                refine ⟨4383225443473907087142293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11688601182597085565712781 4383225443473907087142293)
                ·
                  refine ⟨205463692662839394709795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4383225443473907087142293 205463692662839394709795)
                  ·
                    rfl

theorem cell22_1800626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_1800626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1800626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1800626 prefixEnd_1800626 := by exact prefixLift 1800626
  have htrace : WordTrace (prefixWord ++ tailWord_1800626) baseStart_1800626 baseEnd_1800626 := by
    simpa [prefixWord, tailWord_1800626, baseEnd_1800626] using wordTrace_append hprefix tailTrace_1800626
  have hstable : (prefixWord ++ tailWord_1800626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800626).length < 2 ^ (prefixWord ++ tailWord_1800626).sum := by decide
  have hdescent : baseEnd_1800626 < baseStart_1800626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800660 : List Nat := [2, 4, 1, 2, 2, 1, 1, 5, 4]
def baseStart_1800660 : Nat := 118140960795 + 1800660 * 2 ^ 59
def prefixEnd_1800660 : Nat := 4983230072969 + 3 ^ 40 * 1800660 * 2
def baseEnd_1800660 : Nat := 205467572294451142926427

theorem tailTrace_1800660 : CollatzResearch.WordTrace tailWord_1800660 prefixEnd_1800660 205467572294451142926427 := by
  unfold tailWord_1800660
  simp only [CollatzResearch.WordTrace]
  refine ⟨32837732828261911544767717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43783643771015882059690289 32837732828261911544767717)
  ·
    refine ⟨6157074905299108414643947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32837732828261911544767717 6157074905299108414643947)
    ·
      refine ⟨9235612357948662621965921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6157074905299108414643947 9235612357948662621965921)
      ·
        refine ⟨6926709268461496966474441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9235612357948662621965921 6926709268461496966474441)
        ·
          refine ⟨5195031951346122724855831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6926709268461496966474441 5195031951346122724855831)
          ·
            refine ⟨7792547927019184087283747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5195031951346122724855831 7792547927019184087283747)
            ·
              refine ⟨11688821890528776130925621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7792547927019184087283747 11688821890528776130925621)
              ·
                refine ⟨1095827052237072762274277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11688821890528776130925621 1095827052237072762274277)
                ·
                  refine ⟨205467572294451142926427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1095827052237072762274277 205467572294451142926427)
                  ·
                    rfl

theorem cell22_1800660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_1800660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1800660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1800660 prefixEnd_1800660 := by exact prefixLift 1800660
  have htrace : WordTrace (prefixWord ++ tailWord_1800660) baseStart_1800660 baseEnd_1800660 := by
    simpa [prefixWord, tailWord_1800660, baseEnd_1800660] using wordTrace_append hprefix tailTrace_1800660
  have hstable : (prefixWord ++ tailWord_1800660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800660).length < 2 ^ (prefixWord ++ tailWord_1800660).sum := by decide
  have hdescent : baseEnd_1800660 < baseStart_1800660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800671 : List Nat := [1, 1, 2, 3, 3, 3, 9]
def baseStart_1800671 : Nat := 118140960795 + 1800671 * 2 ^ 59
def prefixEnd_1800671 : Nat := 4983230072969 + 3 ^ 40 * 1800671 * 2
def baseEnd_1800671 : Nat := 22829869718820483953861

theorem tailTrace_1800671 : CollatzResearch.WordTrace tailWord_1800671 prefixEnd_1800671 22829869718820483953861 := by
  unfold tailWord_1800671
  simp only [CollatzResearch.WordTrace]
  refine ⟨65675866859483971968185867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43783911239655981312123911 65675866859483971968185867)
  ·
    refine ⟨98513800289225957952278801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65675866859483971968185867 98513800289225957952278801)
    ·
      refine ⟨73885350216919468464209101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98513800289225957952278801 73885350216919468464209101)
      ·
        refine ⟨27707006331344800674078413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73885350216919468464209101 27707006331344800674078413)
        ·
          refine ⟨10390127374254300252779405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27707006331344800674078413 10390127374254300252779405)
          ·
            refine ⟨3896297765345362594792277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10390127374254300252779405 3896297765345362594792277)
            ·
              refine ⟨22829869718820483953861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3896297765345362594792277 22829869718820483953861)
              ·
                rfl

theorem cell22_1800671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 9].length) (baseStart_1800671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1800671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1800671 prefixEnd_1800671 := by exact prefixLift 1800671
  have htrace : WordTrace (prefixWord ++ tailWord_1800671) baseStart_1800671 baseEnd_1800671 := by
    simpa [prefixWord, tailWord_1800671, baseEnd_1800671] using wordTrace_append hprefix tailTrace_1800671
  have hstable : (prefixWord ++ tailWord_1800671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800671).length < 2 ^ (prefixWord ++ tailWord_1800671).sum := by decide
  have hdescent : baseEnd_1800671 < baseStart_1800671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800675 : List Nat := [1, 1, 1, 6, 3, 1, 1, 1, 4, 3]
def baseStart_1800675 : Nat := 118140960795 + 1800675 * 2 ^ 59
def prefixEnd_1800675 : Nat := 4983230072969 + 3 ^ 40 * 1800675 * 2
def baseEnd_1800675 : Nat := 616407851689898389654235

theorem tailTrace_1800675 : CollatzResearch.WordTrace tailWord_1800675 prefixEnd_1800675 616407851689898389654235 := by
  unfold tailWord_1800675
  simp only [CollatzResearch.WordTrace]
  refine ⟨65676012751469480651331479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43784008500979653767554319 65676012751469480651331479)
  ·
    refine ⟨98514019127204220976997219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65676012751469480651331479 98514019127204220976997219)
    ·
      refine ⟨147771028690806331465495829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98514019127204220976997219 147771028690806331465495829)
      ·
        refine ⟨6926766969881546787445117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 147771028690806331465495829 6926766969881546787445117)
        ·
          refine ⟨2597537613705580045291919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6926766969881546787445117 2597537613705580045291919)
          ·
            refine ⟨3896306420558370067937879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2597537613705580045291919 3896306420558370067937879)
            ·
              refine ⟨5844459630837555101906819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3896306420558370067937879 5844459630837555101906819)
              ·
                refine ⟨8766689446256332652860229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5844459630837555101906819 8766689446256332652860229)
                ·
                  refine ⟨1643754271173062372411293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8766689446256332652860229 1643754271173062372411293)
                  ·
                    refine ⟨616407851689898389654235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1643754271173062372411293 616407851689898389654235)
                    ·
                      rfl

theorem cell22_1800675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 4, 3].length) (baseStart_1800675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1800675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1800675 prefixEnd_1800675 := by exact prefixLift 1800675
  have htrace : WordTrace (prefixWord ++ tailWord_1800675) baseStart_1800675 baseEnd_1800675 := by
    simpa [prefixWord, tailWord_1800675, baseEnd_1800675] using wordTrace_append hprefix tailTrace_1800675
  have hstable : (prefixWord ++ tailWord_1800675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800675).length < 2 ^ (prefixWord ++ tailWord_1800675).sum := by decide
  have hdescent : baseEnd_1800675 < baseStart_1800675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800703 : List Nat := [1, 1, 2, 2, 1, 2, 3, 4, 3, 3]
def baseStart_1800703 : Nat := 118140960795 + 1800703 * 2 ^ 59
def prefixEnd_1800703 : Nat := 4983230072969 + 3 ^ 40 * 1800703 * 2
def baseEnd_1800703 : Nat := 616417436662115649954149

theorem tailTrace_1800703 : CollatzResearch.WordTrace tailWord_1800703 prefixEnd_1800703 616417436662115649954149 := by
  unfold tailWord_1800703
  simp only [CollatzResearch.WordTrace]
  refine ⟨65677033995368041433350763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43784689330245360955567175 65677033995368041433350763)
  ·
    refine ⟨98515550993052062150026145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65677033995368041433350763 98515550993052062150026145)
    ·
      refine ⟨73886663244789046612519609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98515550993052062150026145 73886663244789046612519609)
      ·
        refine ⟨55414997433591784959389707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73886663244789046612519609 55414997433591784959389707)
        ·
          refine ⟨83122496150387677439084561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55414997433591784959389707 83122496150387677439084561)
          ·
            refine ⟨62341872112790758079313421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83122496150387677439084561 62341872112790758079313421)
            ·
              refine ⟨23378202042296534279742533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62341872112790758079313421 23378202042296534279742533)
              ·
                refine ⟨4383412882930600177451725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23378202042296534279742533 4383412882930600177451725)
                ·
                  refine ⟨1643779831098975066544397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4383412882930600177451725 1643779831098975066544397)
                  ·
                    refine ⟨616417436662115649954149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1643779831098975066544397 616417436662115649954149)
                    ·
                      rfl

theorem cell22_1800703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 3, 3].length) (baseStart_1800703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1800703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1800703 prefixEnd_1800703 := by exact prefixLift 1800703
  have htrace : WordTrace (prefixWord ++ tailWord_1800703) baseStart_1800703 baseEnd_1800703 := by
    simpa [prefixWord, tailWord_1800703, baseEnd_1800703] using wordTrace_append hprefix tailTrace_1800703
  have hstable : (prefixWord ++ tailWord_1800703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800703).length < 2 ^ (prefixWord ++ tailWord_1800703).sum := by decide
  have hdescent : baseEnd_1800703 < baseStart_1800703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800705 : List Nat := [1, 2, 4, 1, 3, 3, 2, 6]
def baseStart_1800705 : Nat := 118140960795 + 1800705 * 2 ^ 59
def prefixEnd_1800705 : Nat := 4983230072969 + 3 ^ 40 * 1800705 * 2
def baseEnd_1800705 : Nat := 68490902366998701267127

theorem tailTrace_1800705 : CollatzResearch.WordTrace tailWord_1800705 prefixEnd_1800705 68490902366998701267127 := by
  unfold tailWord_1800705
  simp only [CollatzResearch.WordTrace]
  refine ⟨65677106941360795774923569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43784737960907197183282379 65677106941360795774923569)
  ·
    refine ⟨49257830206020596831192677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65677106941360795774923569 49257830206020596831192677)
    ·
      refine ⟨9235843163628861905848627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49257830206020596831192677 9235843163628861905848627)
      ·
        refine ⟨13853764745443292858772941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9235843163628861905848627 13853764745443292858772941)
        ·
          refine ⟨5195161779541234822039853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13853764745443292858772941 5195161779541234822039853)
          ·
            refine ⟨1948185667327963058264945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5195161779541234822039853 1948185667327963058264945)
            ·
              refine ⟨1461139250495972293698709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1948185667327963058264945 1461139250495972293698709)
              ·
                refine ⟨68490902366998701267127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1461139250495972293698709 68490902366998701267127)
                ·
                  rfl

theorem cell22_1800705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 6].length) (baseStart_1800705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1800705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1800705 prefixEnd_1800705 := by exact prefixLift 1800705
  have htrace : WordTrace (prefixWord ++ tailWord_1800705) baseStart_1800705 baseEnd_1800705 := by
    simpa [prefixWord, tailWord_1800705, baseEnd_1800705] using wordTrace_append hprefix tailTrace_1800705
  have hstable : (prefixWord ++ tailWord_1800705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800705).length < 2 ^ (prefixWord ++ tailWord_1800705).sum := by decide
  have hdescent : baseEnd_1800705 < baseStart_1800705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800733 : List Nat := [1, 4, 2, 2, 1, 2, 2, 1, 7]
def baseStart_1800733 : Nat := 118140960795 + 1800733 * 2 ^ 59
def prefixEnd_1800733 : Nat := 4983230072969 + 3 ^ 40 * 1800733 * 2
def baseEnd_1800733 : Nat := 205475902091735190568019

theorem tailTrace_1800733 : CollatzResearch.WordTrace tailWord_1800733 prefixEnd_1800733 205475902091735190568019 := by
  unfold tailWord_1800733
  simp only [CollatzResearch.WordTrace]
  refine ⟨65678128185259356556942853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43785418790172904371295235 65678128185259356556942853)
  ·
    refine ⟨12314649034736129354426785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65678128185259356556942853 12314649034736129354426785)
    ·
      refine ⟨9235986776052097015820089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12314649034736129354426785 9235986776052097015820089)
      ·
        refine ⟨6926990082039072761865067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9235986776052097015820089 6926990082039072761865067)
        ·
          refine ⟨10390485123058609142797601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6926990082039072761865067 10390485123058609142797601)
          ·
            refine ⟨7792863842293956857098201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10390485123058609142797601 7792863842293956857098201)
            ·
              refine ⟨5844647881720467642823651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7792863842293956857098201 5844647881720467642823651)
              ·
                refine ⟨8766971822580701464235477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5844647881720467642823651 8766971822580701464235477)
                ·
                  refine ⟨205475902091735190568019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8766971822580701464235477 205475902091735190568019)
                  ·
                    rfl

theorem cell22_1800733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_1800733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1800733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1800733 prefixEnd_1800733 := by exact prefixLift 1800733
  have htrace : WordTrace (prefixWord ++ tailWord_1800733) baseStart_1800733 baseEnd_1800733 := by
    simpa [prefixWord, tailWord_1800733, baseEnd_1800733] using wordTrace_append hprefix tailTrace_1800733
  have hstable : (prefixWord ++ tailWord_1800733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800733).length < 2 ^ (prefixWord ++ tailWord_1800733).sum := by decide
  have hdescent : baseEnd_1800733 < baseStart_1800733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800743 : List Nat := [1, 1, 7, 2, 2, 1, 2, 1, 2, 3]
def baseStart_1800743 : Nat := 118140960795 + 1800743 * 2 ^ 59
def prefixEnd_1800743 : Nat := 4983230072969 + 3 ^ 40 * 1800743 * 2
def baseEnd_1800743 : Nat := 616431129479568878954027

theorem tailTrace_1800743 : CollatzResearch.WordTrace tailWord_1800743 prefixEnd_1800743 616431129479568878954027 := by
  unfold tailWord_1800743
  simp only [CollatzResearch.WordTrace]
  refine ⟨65678492915223128264806883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43785661943482085509871255 65678492915223128264806883)
  ·
    refine ⟨98517739372834692397210325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65678492915223128264806883 98517739372834692397210325)
    ·
      refine ⟨2309009516550813103059617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 98517739372834692397210325 2309009516550813103059617)
      ·
        refine ⟨1731757137413109827294713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2309009516550813103059617 1731757137413109827294713)
        ·
          refine ⟨1298817853059832370471035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1731757137413109827294713 1298817853059832370471035)
          ·
            refine ⟨1948226779589748555706553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1298817853059832370471035 1948226779589748555706553)
            ·
              refine ⟨1461170084692311416779915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1948226779589748555706553 1461170084692311416779915)
              ·
                refine ⟨2191755127038467125169873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1461170084692311416779915 2191755127038467125169873)
                ·
                  refine ⟨1643816345278850343877405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2191755127038467125169873 1643816345278850343877405)
                  ·
                    refine ⟨616431129479568878954027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1643816345278850343877405 616431129479568878954027)
                    ·
                      rfl

theorem cell22_1800743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_1800743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1800743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1800743 prefixEnd_1800743 := by exact prefixLift 1800743
  have htrace : WordTrace (prefixWord ++ tailWord_1800743) baseStart_1800743 baseEnd_1800743 := by
    simpa [prefixWord, tailWord_1800743, baseEnd_1800743] using wordTrace_append hprefix tailTrace_1800743
  have hstable : (prefixWord ++ tailWord_1800743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800743).length < 2 ^ (prefixWord ++ tailWord_1800743).sum := by decide
  have hdescent : baseEnd_1800743 < baseStart_1800743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800810 : List Nat := [3, 1, 3, 2, 1, 1, 4, 1, 1, 5]
def baseStart_1800810 : Nat := 118140960795 + 1800810 * 2 ^ 59
def prefixEnd_1800810 : Nat := 4983230072969 + 3 ^ 40 * 1800810 * 2
def baseEnd_1800810 : Nat := 616454064948803037528821

theorem tailTrace_1800810 : CollatzResearch.WordTrace tailWord_1800810 prefixEnd_1800810 616454064948803037528821 := by
  unfold tailWord_1800810
  simp only [CollatzResearch.WordTrace]
  refine ⟨16420234151495099676873971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43787291070653599138330589 16420234151495099676873971)
  ·
    refine ⟨24630351227242649515310957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16420234151495099676873971 24630351227242649515310957)
    ·
      refine ⟨9236381710215993568241609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24630351227242649515310957 9236381710215993568241609)
      ·
        refine ⟨6927286282661995176181207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9236381710215993568241609 6927286282661995176181207)
        ·
          refine ⟨10390929423992992764271811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6927286282661995176181207 10390929423992992764271811)
          ·
            refine ⟨15586394135989489146407717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10390929423992992764271811 15586394135989489146407717)
            ·
              refine ⟨2922448900498029214951447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15586394135989489146407717 2922448900498029214951447)
              ·
                refine ⟨4383673350747043822427171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2922448900498029214951447 4383673350747043822427171)
                ·
                  refine ⟨6575510026120565733640757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4383673350747043822427171 6575510026120565733640757)
                  ·
                    refine ⟨616454064948803037528821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6575510026120565733640757 616454064948803037528821)
                    ·
                      rfl

theorem cell22_1800810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_1800810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1800810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1800810 prefixEnd_1800810 := by exact prefixLift 1800810
  have htrace : WordTrace (prefixWord ++ tailWord_1800810) baseStart_1800810 baseEnd_1800810 := by
    simpa [prefixWord, tailWord_1800810, baseEnd_1800810] using wordTrace_append hprefix tailTrace_1800810
  have hstable : (prefixWord ++ tailWord_1800810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800810).length < 2 ^ (prefixWord ++ tailWord_1800810).sum := by decide
  have hdescent : baseEnd_1800810 < baseStart_1800810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800825 : List Nat := [1, 2, 1, 3, 3, 2, 3, 1, 2, 4]
def baseStart_1800825 : Nat := 118140960795 + 1800825 * 2 ^ 59
def prefixEnd_1800825 : Nat := 4983230072969 + 3 ^ 40 * 1800825 * 2
def baseEnd_1800825 : Nat := 616459199755347998403775

theorem tailTrace_1800825 : CollatzResearch.WordTrace tailWord_1800825 prefixEnd_1800825 616459199755347998403775 := by
  unfold tailWord_1800825
  simp only [CollatzResearch.WordTrace]
  refine ⟨65681483700926056269291929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43787655800617370846194619 65681483700926056269291929)
  ·
    refine ⟨49261112775694542201968947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65681483700926056269291929 49261112775694542201968947)
    ·
      refine ⟨73891669163541813302953421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49261112775694542201968947 73891669163541813302953421)
      ·
        refine ⟨27709375936328179988607533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73891669163541813302953421 27709375936328179988607533)
        ·
          refine ⟨10391015976123067495727825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27709375936328179988607533 10391015976123067495727825)
          ·
            refine ⟨7793261982092300621795869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10391015976123067495727825 7793261982092300621795869)
            ·
              refine ⟨2922473243284612733173451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7793261982092300621795869 2922473243284612733173451)
              ·
                refine ⟨4383709864926919099760177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2922473243284612733173451 4383709864926919099760177)
                ·
                  refine ⟨3287782398695189324820133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4383709864926919099760177 3287782398695189324820133)
                  ·
                    refine ⟨616459199755347998403775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3287782398695189324820133 616459199755347998403775)
                    ·
                      rfl

theorem cell22_1800825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 2, 4].length) (baseStart_1800825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1800825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1800825 prefixEnd_1800825 := by exact prefixLift 1800825
  have htrace : WordTrace (prefixWord ++ tailWord_1800825) baseStart_1800825 baseEnd_1800825 := by
    simpa [prefixWord, tailWord_1800825, baseEnd_1800825] using wordTrace_append hprefix tailTrace_1800825
  have hstable : (prefixWord ++ tailWord_1800825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800825).length < 2 ^ (prefixWord ++ tailWord_1800825).sum := by decide
  have hdescent : baseEnd_1800825 < baseStart_1800825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800885 : List Nat := [1, 3, 3, 3, 1, 1, 1, 2, 7]
def baseStart_1800885 : Nat := 118140960795 + 1800885 * 2 ^ 59
def prefixEnd_1800885 : Nat := 4983230072969 + 3 ^ 40 * 1800885 * 2
def baseEnd_1800885 : Nat := 205493246327175947301197

theorem tailTrace_1800885 : CollatzResearch.WordTrace tailWord_1800885 prefixEnd_1800885 205493246327175947301197 := by
  unfold tailWord_1800885
  simp only [CollatzResearch.WordTrace]
  refine ⟨65683672080708686516476109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43789114720472457677650739 65683672080708686516476109)
  ·
    refine ⟨24631377030265757443678541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65683672080708686516476109 24631377030265757443678541)
    ·
      refine ⟨9236766386349659041379453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24631377030265757443678541 9236766386349659041379453)
      ·
        refine ⟨3463787394881122140517295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9236766386349659041379453 3463787394881122140517295)
        ·
          refine ⟨5195681092321683210775943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3463787394881122140517295 5195681092321683210775943)
          ·
            refine ⟨7793521638482524816163915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5195681092321683210775943 7793521638482524816163915)
            ·
              refine ⟨11690282457723787224245873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7793521638482524816163915 11690282457723787224245873)
              ·
                refine ⟨8767711843292840418184405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11690282457723787224245873 8767711843292840418184405)
                ·
                  refine ⟨205493246327175947301197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8767711843292840418184405 205493246327175947301197)
                  ·
                    rfl

theorem cell22_1800885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 7].length) (baseStart_1800885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1800885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1800885 prefixEnd_1800885 := by exact prefixLift 1800885
  have htrace : WordTrace (prefixWord ++ tailWord_1800885) baseStart_1800885 baseEnd_1800885 := by
    simpa [prefixWord, tailWord_1800885, baseEnd_1800885] using wordTrace_append hprefix tailTrace_1800885
  have hstable : (prefixWord ++ tailWord_1800885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800885).length < 2 ^ (prefixWord ++ tailWord_1800885).sum := by decide
  have hdescent : baseEnd_1800885 < baseStart_1800885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800906 : List Nat := [3, 1, 2, 1, 4, 2, 3, 2, 1, 3]
def baseStart_1800906 : Nat := 118140960795 + 1800906 * 2 ^ 59
def prefixEnd_1800906 : Nat := 4983230072969 + 3 ^ 40 * 1800906 * 2
def baseEnd_1800906 : Nat := 616486927710690787128527

theorem tailTrace_1800906 : CollatzResearch.WordTrace tailWord_1800906 prefixEnd_1800906 616486927710690787128527 := by
  unfold tailWord_1800906
  simp only [CollatzResearch.WordTrace]
  refine ⟨16421109503408151775747643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43789625342421738068660381 16421109503408151775747643)
  ·
    refine ⟨24631664255112227663621465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16421109503408151775747643 24631664255112227663621465)
    ·
      refine ⟨18473748191334170747716099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24631664255112227663621465 18473748191334170747716099)
      ·
        refine ⟨27710622287001256121574149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18473748191334170747716099 27710622287001256121574149)
        ·
          refine ⟨5195741678812735522795153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27710622287001256121574149 5195741678812735522795153)
          ·
            refine ⟨3896806259109551642096365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5195741678812735522795153 3896806259109551642096365)
            ·
              refine ⟨1461302347166081865786137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3896806259109551642096365 1461302347166081865786137)
              ·
                refine ⟨1095976760374561399339603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1461302347166081865786137 1095976760374561399339603)
                ·
                  refine ⟨1643965140561842099009405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1095976760374561399339603 1643965140561842099009405)
                  ·
                    refine ⟨616486927710690787128527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1643965140561842099009405 616486927710690787128527)
                    ·
                      rfl

theorem cell22_1800906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 2, 1, 3].length) (baseStart_1800906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1800906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1800906 prefixEnd_1800906 := by exact prefixLift 1800906
  have htrace : WordTrace (prefixWord ++ tailWord_1800906) baseStart_1800906 baseEnd_1800906 := by
    simpa [prefixWord, tailWord_1800906, baseEnd_1800906] using wordTrace_append hprefix tailTrace_1800906
  have hstable : (prefixWord ++ tailWord_1800906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800906).length < 2 ^ (prefixWord ++ tailWord_1800906).sum := by decide
  have hdescent : baseEnd_1800906 < baseStart_1800906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800932 : List Nat := [2, 3, 1, 1, 1, 4, 3, 2, 1, 4]
def baseStart_1800932 : Nat := 118140960795 + 1800932 * 2 ^ 59
def prefixEnd_1800932 : Nat := 4983230072969 + 3 ^ 40 * 1800932 * 2
def baseEnd_1800932 : Nat := 616495828042035385978447

theorem tailTrace_1800932 : CollatzResearch.WordTrace tailWord_1800932 prefixEnd_1800932 616495828042035385978447 := by
  unfold tailWord_1800932
  simp only [CollatzResearch.WordTrace]
  refine ⟨32842693155769206771718525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43790257541025609028958033 32842693155769206771718525)
  ·
    refine ⟨12316009933413452539394447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32842693155769206771718525 12316009933413452539394447)
    ·
      refine ⟨18474014900120178809091671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12316009933413452539394447 18474014900120178809091671)
      ·
        refine ⟨27711022350180268213637507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18474014900120178809091671 27711022350180268213637507)
        ·
          refine ⟨41566533525270402320456261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27711022350180268213637507 41566533525270402320456261)
          ·
            refine ⟨7793725035988200435085549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41566533525270402320456261 7793725035988200435085549)
            ·
              refine ⟨2922646888495575163157081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7793725035988200435085549 2922646888495575163157081)
              ·
                refine ⟨2191985166371681372367811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2922646888495575163157081 2191985166371681372367811)
                ·
                  refine ⟨3287977749557522058551717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2191985166371681372367811 3287977749557522058551717)
                  ·
                    refine ⟨616495828042035385978447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3287977749557522058551717 616495828042035385978447)
                    ·
                      rfl

theorem cell22_1800932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_1800932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1800932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1800932 prefixEnd_1800932 := by exact prefixLift 1800932
  have htrace : WordTrace (prefixWord ++ tailWord_1800932) baseStart_1800932 baseEnd_1800932 := by
    simpa [prefixWord, tailWord_1800932, baseEnd_1800932] using wordTrace_append hprefix tailTrace_1800932
  have hstable : (prefixWord ++ tailWord_1800932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800932).length < 2 ^ (prefixWord ++ tailWord_1800932).sum := by decide
  have hdescent : baseEnd_1800932 < baseStart_1800932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800945 : List Nat := [1, 2, 2, 2, 2, 2, 3, 2, 1, 5]
def baseStart_1800945 : Nat := 118140960795 + 1800945 * 2 ^ 59
def prefixEnd_1800945 : Nat := 4983230072969 + 3 ^ 40 * 1800945 * 2
def baseEnd_1800945 : Nat := 616500278207707685403407

theorem tailTrace_1800945 : CollatzResearch.WordTrace tailWord_1800945 prefixEnd_1800945 616500278207707685403407 := by
  unfold tailWord_1800945
  simp only [CollatzResearch.WordTrace]
  refine ⟨65685860460491316763660289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43790573640327544509106859 65685860460491316763660289)
  ·
    refine ⟨49264395345368487572745217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65685860460491316763660289 49264395345368487572745217)
    ·
      refine ⟨36948296509026365679558913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49264395345368487572745217 36948296509026365679558913)
      ·
        refine ⟨27711222381769774259669185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36948296509026365679558913 27711222381769774259669185)
        ·
          refine ⟨20783416786327330694751889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27711222381769774259669185 20783416786327330694751889)
          ·
            refine ⟨15587562589745498021063917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20783416786327330694751889 15587562589745498021063917)
            ·
              refine ⟨5845335971154561757898969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15587562589745498021063917 5845335971154561757898969)
              ·
                refine ⟨4384001978365921318424227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5845335971154561757898969 4384001978365921318424227)
                ·
                  refine ⟨6576002967548881977636341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4384001978365921318424227 6576002967548881977636341)
                  ·
                    refine ⟨616500278207707685403407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6576002967548881977636341 616500278207707685403407)
                    ·
                      rfl

theorem cell22_1800945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 5].length) (baseStart_1800945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1800945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1800945 prefixEnd_1800945 := by exact prefixLift 1800945
  have htrace : WordTrace (prefixWord ++ tailWord_1800945) baseStart_1800945 baseEnd_1800945 := by
    simpa [prefixWord, tailWord_1800945, baseEnd_1800945] using wordTrace_append hprefix tailTrace_1800945
  have hstable : (prefixWord ++ tailWord_1800945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800945).length < 2 ^ (prefixWord ++ tailWord_1800945).sum := by decide
  have hdescent : baseEnd_1800945 < baseStart_1800945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800992 : List Nat := [2, 1, 1, 5, 1, 3, 3, 6]
def baseStart_1800992 : Nat := 118140960795 + 1800992 * 2 ^ 59
def prefixEnd_1800992 : Nat := 4983230072969 + 3 ^ 40 * 1800992 * 2
def baseEnd_1800992 : Nat := 68501818585357247719807

theorem tailTrace_1800992 : CollatzResearch.WordTrace tailWord_1800992 prefixEnd_1800992 68501818585357247719807 := by
  unfold tailWord_1800992
  simp only [CollatzResearch.WordTrace]
  refine ⟨32843787345660521895310615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43791716460880695860414153 32843787345660521895310615)
  ·
    refine ⟨49265681018490782842965923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32843787345660521895310615 49265681018490782842965923)
    ·
      refine ⟨73898521527736174264448885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49265681018490782842965923 73898521527736174264448885)
      ·
        refine ⟨6927986393225266337292083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73898521527736174264448885 6927986393225266337292083)
        ·
          refine ⟨10391979589837899505938125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6927986393225266337292083 10391979589837899505938125)
          ·
            refine ⟨3896992346189212314726797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10391979589837899505938125 3896992346189212314726797)
            ·
              refine ⟨1461372129820954618022549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3896992346189212314726797 1461372129820954618022549)
              ·
                refine ⟨68501818585357247719807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1461372129820954618022549 68501818585357247719807)
                ·
                  rfl

theorem cell22_1800992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 6].length) (baseStart_1800992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1800992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1800992 prefixEnd_1800992 := by exact prefixLift 1800992
  have htrace : WordTrace (prefixWord ++ tailWord_1800992) baseStart_1800992 baseEnd_1800992 := by
    simpa [prefixWord, tailWord_1800992, baseEnd_1800992] using wordTrace_append hprefix tailTrace_1800992
  have hstable : (prefixWord ++ tailWord_1800992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800992).length < 2 ^ (prefixWord ++ tailWord_1800992).sum := by decide
  have hdescent : baseEnd_1800992 < baseStart_1800992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800994 : List Nat := [3, 3, 1, 1, 2, 4, 1, 1, 2, 4]
def baseStart_1800994 : Nat := 118140960795 + 1800994 * 2 ^ 59
def prefixEnd_1800994 : Nat := 4983230072969 + 3 ^ 40 * 1800994 * 2
def baseEnd_1800994 : Nat := 616517051909087890928257

theorem tailTrace_1800994 : CollatzResearch.WordTrace tailWord_1800994 prefixEnd_1800994 616517051909087890928257 := by
  unfold tailWord_1800994
  simp only [CollatzResearch.WordTrace]
  refine ⟨16421911909328449533048509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43791765091542532088129357 16421911909328449533048509)
  ·
    refine ⟨6158216965998168574893191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16421911909328449533048509 6158216965998168574893191)
    ·
      refine ⟨9237325448997252862339787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6158216965998168574893191 9237325448997252862339787)
      ·
        refine ⟨13855988173495879293509681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9237325448997252862339787 13855988173495879293509681)
        ·
          refine ⟨10391991130121909470132261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13855988173495879293509681 10391991130121909470132261)
          ·
            refine ⟨1948498336897858025649799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10391991130121909470132261 1948498336897858025649799)
            ·
              refine ⟨2922747505346787038474699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1948498336897858025649799 2922747505346787038474699)
              ·
                refine ⟨4384121258020180557712049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2922747505346787038474699 4384121258020180557712049)
                ·
                  refine ⟨3288090943515135418284037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4384121258020180557712049 3288090943515135418284037)
                  ·
                    refine ⟨616517051909087890928257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3288090943515135418284037 616517051909087890928257)
                    ·
                      rfl

theorem cell22_1800994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_1800994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1800994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1800994 prefixEnd_1800994 := by exact prefixLift 1800994
  have htrace : WordTrace (prefixWord ++ tailWord_1800994) baseStart_1800994 baseEnd_1800994 := by
    simpa [prefixWord, tailWord_1800994, baseEnd_1800994] using wordTrace_append hprefix tailTrace_1800994
  have hstable : (prefixWord ++ tailWord_1800994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800994).length < 2 ^ (prefixWord ++ tailWord_1800994).sum := by decide
  have hdescent : baseEnd_1800994 < baseStart_1800994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801030 : List Nat := [6, 1, 1, 2, 2, 1, 3, 1, 2, 3]
def baseStart_1801030 : Nat := 118140960795 + 1801030 * 2 ^ 59
def prefixEnd_1801030 : Nat := 4983230072969 + 3 ^ 40 * 1801030 * 2
def baseEnd_1801030 : Nat := 616529375444795797028147

theorem tailTrace_1801030 : CollatzResearch.WordTrace tailWord_1801030 prefixEnd_1801030 616529375444795797028147 := by
  unfold tailWord_1801030
  simp only [CollatzResearch.WordTrace]
  refine ⟨2052780020786980508765767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43792640443455584187003029 2052780020786980508765767)
  ·
    refine ⟨3079170031180470763148651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2052780020786980508765767 3079170031180470763148651)
    ·
      refine ⟨4618755046770706144722977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3079170031180470763148651 4618755046770706144722977)
      ·
        refine ⟨3464066285078029608542233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4618755046770706144722977 3464066285078029608542233)
        ·
          refine ⟨2598049713808522206406675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3464066285078029608542233 2598049713808522206406675)
          ·
            refine ⟨3897074570712783309610013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2598049713808522206406675 3897074570712783309610013)
            ·
              refine ⟨1461402964017293741103755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3897074570712783309610013 1461402964017293741103755)
              ·
                refine ⟨2192104446025940611655633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1461402964017293741103755 2192104446025940611655633)
                ·
                  refine ⟨1644078334519455458741725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2192104446025940611655633 1644078334519455458741725)
                  ·
                    refine ⟨616529375444795797028147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1644078334519455458741725 616529375444795797028147)
                    ·
                      rfl

theorem cell22_1801030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_1801030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1801030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1801030 prefixEnd_1801030 := by exact prefixLift 1801030
  have htrace : WordTrace (prefixWord ++ tailWord_1801030) baseStart_1801030 baseEnd_1801030 := by
    simpa [prefixWord, tailWord_1801030, baseEnd_1801030] using wordTrace_append hprefix tailTrace_1801030
  have hstable : (prefixWord ++ tailWord_1801030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801030).length < 2 ^ (prefixWord ++ tailWord_1801030).sum := by decide
  have hdescent : baseEnd_1801030 < baseStart_1801030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801067 : List Nat := [1, 1, 1, 1, 2, 2, 6, 3, 1, 4]
def baseStart_1801067 : Nat := 118140960795 + 1801067 * 2 ^ 59
def prefixEnd_1801067 : Nat := 4983230072969 + 3 ^ 40 * 1801067 * 2
def baseEnd_1801067 : Nat := 616542041300940033853033

theorem tailTrace_1801067 : CollatzResearch.WordTrace tailWord_1801067 prefixEnd_1801067 616542041300940033853033 := by
  unfold tailWord_1801067
  simp only [CollatzResearch.WordTrace]
  refine ⟨65690310166049331599601455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43793540110699554399734303 65690310166049331599601455)
  ·
    refine ⟨98535465249073997399402183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65690310166049331599601455 98535465249073997399402183)
    ·
      refine ⟨147803197873610996099103275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98535465249073997399402183 147803197873610996099103275)
      ·
        refine ⟨221704796810416494148654913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147803197873610996099103275 221704796810416494148654913)
        ·
          refine ⟨166278597607812370611491185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221704796810416494148654913 166278597607812370611491185)
          ·
            refine ⟨124708948205859277958618389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166278597607812370611491185 124708948205859277958618389)
            ·
              refine ⟨5845731947149653654310237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 124708948205859277958618389 5845731947149653654310237)
              ·
                refine ⟨2192149480181120120366339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5845731947149653654310237 2192149480181120120366339)
                ·
                  refine ⟨3288224220271680180549509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2192149480181120120366339 3288224220271680180549509)
                  ·
                    refine ⟨616542041300940033853033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3288224220271680180549509 616542041300940033853033)
                    ·
                      rfl

theorem cell22_1801067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3, 1, 4].length) (baseStart_1801067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1801067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1801067 prefixEnd_1801067 := by exact prefixLift 1801067
  have htrace : WordTrace (prefixWord ++ tailWord_1801067) baseStart_1801067 baseEnd_1801067 := by
    simpa [prefixWord, tailWord_1801067, baseEnd_1801067] using wordTrace_append hprefix tailTrace_1801067
  have hstable : (prefixWord ++ tailWord_1801067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801067).length < 2 ^ (prefixWord ++ tailWord_1801067).sum := by decide
  have hdescent : baseEnd_1801067 < baseStart_1801067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801080 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 5, 5]
def baseStart_1801080 : Nat := 118140960795 + 1801080 * 2 ^ 59
def prefixEnd_1801080 : Nat := 4983230072969 + 3 ^ 40 * 1801080 * 2
def baseEnd_1801080 : Nat := 616546491466612333277993

theorem tailTrace_1801080 : CollatzResearch.WordTrace tailWord_1801080 prefixEnd_1801080 616546491466612333277993 := by
  unfold tailWord_1801080
  simp only [CollatzResearch.WordTrace]
  refine ⟨32845392157501117409912347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43793856210001489879883129 32845392157501117409912347)
  ·
    refine ⟨49268088236251676114868521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32845392157501117409912347 49268088236251676114868521)
    ·
      refine ⟨36951066177188757086151391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49268088236251676114868521 36951066177188757086151391)
      ·
        refine ⟨55426599265783135629227087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36951066177188757086151391 55426599265783135629227087)
        ·
          refine ⟨83139898898674703443840631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55426599265783135629227087 83139898898674703443840631)
          ·
            refine ⟨124709848348012055165760947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83139898898674703443840631 124709848348012055165760947)
            ·
              refine ⟨187064772522018082748641421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124709848348012055165760947 187064772522018082748641421)
              ·
                refine ⟨70149289695756781030740533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187064772522018082748641421 70149289695756781030740533)
                ·
                  refine ⟨6576495908977198221631925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70149289695756781030740533 6576495908977198221631925)
                  ·
                    refine ⟨616546491466612333277993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6576495908977198221631925 616546491466612333277993)
                    ·
                      rfl

theorem cell22_1801080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_1801080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1801080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1801080 prefixEnd_1801080 := by exact prefixLift 1801080
  have htrace : WordTrace (prefixWord ++ tailWord_1801080) baseStart_1801080 baseEnd_1801080 := by
    simpa [prefixWord, tailWord_1801080, baseEnd_1801080] using wordTrace_append hprefix tailTrace_1801080
  have hstable : (prefixWord ++ tailWord_1801080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801080).length < 2 ^ (prefixWord ++ tailWord_1801080).sum := by decide
  have hdescent : baseEnd_1801080 < baseStart_1801080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801114 : List Nat := [3, 1, 1, 4, 3, 1, 1, 2, 1, 5]
def baseStart_1801114 : Nat := 118140960795 + 1801114 * 2 ^ 59
def prefixEnd_1801114 : Nat := 4983230072969 + 3 ^ 40 * 1801114 * 2
def baseEnd_1801114 : Nat := 616558130361447577927889

theorem tailTrace_1801114 : CollatzResearch.WordTrace tailWord_1801114 prefixEnd_1801114 616558130361447577927889 := by
  unfold tailWord_1801114
  simp only [CollatzResearch.WordTrace]
  refine ⟨16423006099219764656640599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43794682931252705751041597 16423006099219764656640599)
  ·
    refine ⟨24634509148829646984960899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16423006099219764656640599 24634509148829646984960899)
    ·
      refine ⟨36951763723244470477441349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24634509148829646984960899 36951763723244470477441349)
      ·
        refine ⟨6928455698108338214520253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36951763723244470477441349 6928455698108338214520253)
        ·
          refine ⟨2598170886790626830445095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6928455698108338214520253 2598170886790626830445095)
          ·
            refine ⟨3897256330185940245667643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2598170886790626830445095 3897256330185940245667643)
            ·
              refine ⟨5845884495278910368501465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3897256330185940245667643 5845884495278910368501465)
              ·
                refine ⟨4384413371459182776376099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5845884495278910368501465 4384413371459182776376099)
                ·
                  refine ⟨6576620057188774164564149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4384413371459182776376099 6576620057188774164564149)
                  ·
                    refine ⟨616558130361447577927889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6576620057188774164564149 616558130361447577927889)
                    ·
                      rfl

theorem cell22_1801114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 1, 5].length) (baseStart_1801114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1801114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1801114 prefixEnd_1801114 := by exact prefixLift 1801114
  have htrace : WordTrace (prefixWord ++ tailWord_1801114) baseStart_1801114 baseEnd_1801114 := by
    simpa [prefixWord, tailWord_1801114, baseEnd_1801114] using wordTrace_append hprefix tailTrace_1801114
  have hstable : (prefixWord ++ tailWord_1801114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801114).length < 2 ^ (prefixWord ++ tailWord_1801114).sum := by decide
  have hdescent : baseEnd_1801114 < baseStart_1801114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801127 : List Nat := [1, 1, 6, 1, 3, 10]
def baseStart_1801127 : Nat := 118140960795 + 1801127 * 2 ^ 59
def prefixEnd_1801127 : Nat := 4983230072969 + 3 ^ 40 * 1801127 * 2
def baseEnd_1801127 : Nat := 7611883710211356510529

theorem tailTrace_1801127 : CollatzResearch.WordTrace tailWord_1801127 prefixEnd_1801127 7611883710211356510529 := by
  unfold tailWord_1801127
  simp only [CollatzResearch.WordTrace]
  refine ⟨65692498545831961846785635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43794999030554641231190423 65692498545831961846785635)
  ·
    refine ⟨98538747818747942770178453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65692498545831961846785635 98538747818747942770178453)
    ·
      refine ⟨4619003804003809817352115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 98538747818747942770178453 4619003804003809817352115)
      ·
        refine ⟨6928505706005714726028173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4619003804003809817352115 6928505706005714726028173)
        ·
          refine ⟨2598189639752143022260565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6928505706005714726028173 2598189639752143022260565)
          ·
            refine ⟨7611883710211356510529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2598189639752143022260565 7611883710211356510529)
            ·
              rfl

theorem cell22_1801127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 10].length) (baseStart_1801127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1801127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1801127 prefixEnd_1801127 := by exact prefixLift 1801127
  have htrace : WordTrace (prefixWord ++ tailWord_1801127) baseStart_1801127 baseEnd_1801127 := by
    simpa [prefixWord, tailWord_1801127, baseEnd_1801127] using wordTrace_append hprefix tailTrace_1801127
  have hstable : (prefixWord ++ tailWord_1801127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801127).length < 2 ^ (prefixWord ++ tailWord_1801127).sum := by decide
  have hdescent : baseEnd_1801127 < baseStart_1801127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801133 : List Nat := [1, 5, 2, 3, 1, 1, 1, 4, 4]
def baseStart_1801133 : Nat := 118140960795 + 1801133 * 2 ^ 59
def prefixEnd_1801133 : Nat := 4983230072969 + 3 ^ 40 * 1801133 * 2
def baseEnd_1801133 : Nat := 205521544816579287234277

theorem tailTrace_1801133 : CollatzResearch.WordTrace tailWord_1801133 prefixEnd_1801133 205521544816579287234277 := by
  unfold tailWord_1801133
  simp only [CollatzResearch.WordTrace]
  refine ⟨65692717383810224871504053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43795144922540149914336035 65692717383810224871504053)
  ·
    refine ⟨6158692254732208581703505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65692717383810224871504053 6158692254732208581703505)
    ·
      refine ⟨4619019191049156436277629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6158692254732208581703505 4619019191049156436277629)
      ·
        refine ⟨1732132196643433663604111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4619019191049156436277629 1732132196643433663604111)
        ·
          refine ⟨2598198294965150495406167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1732132196643433663604111 2598198294965150495406167)
          ·
            refine ⟨3897297442447725743109251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2598198294965150495406167 3897297442447725743109251)
            ·
              refine ⟨5845946163671588614663877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3897297442447725743109251 5845946163671588614663877)
              ·
                refine ⟨1096114905688422865249477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5845946163671588614663877 1096114905688422865249477)
                ·
                  refine ⟨205521544816579287234277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1096114905688422865249477 205521544816579287234277)
                  ·
                    rfl

theorem cell22_1801133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_1801133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1801133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1801133 prefixEnd_1801133 := by exact prefixLift 1801133
  have htrace : WordTrace (prefixWord ++ tailWord_1801133) baseStart_1801133 baseEnd_1801133 := by
    simpa [prefixWord, tailWord_1801133, baseEnd_1801133] using wordTrace_append hprefix tailTrace_1801133
  have hstable : (prefixWord ++ tailWord_1801133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801133).length < 2 ^ (prefixWord ++ tailWord_1801133).sum := by decide
  have hdescent : baseEnd_1801133 < baseStart_1801133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801176 : List Nat := [2, 1, 2, 2, 2, 3, 1, 5, 1, 3]
def baseStart_1801176 : Nat := 118140960795 + 1801176 * 2 ^ 59
def prefixEnd_1801176 : Nat := 4983230072969 + 3 ^ 40 * 1801176 * 2
def baseEnd_1801176 : Nat := 616579354228500082877699

theorem tailTrace_1801176 : CollatzResearch.WordTrace tailWord_1801176 prefixEnd_1801176 616579354228500082877699 := by
  unfold tailWord_1801176
  simp only [CollatzResearch.WordTrace]
  refine ⟨32847142861327221607659691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43796190481769628810212921 32847142861327221607659691)
  ·
    refine ⟨49270714291990832411489537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32847142861327221607659691 49270714291990832411489537)
    ·
      refine ⟨36953035718993124308617153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49270714291990832411489537 36953035718993124308617153)
      ·
        refine ⟨27714776789244843231462865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36953035718993124308617153 27714776789244843231462865)
        ·
          refine ⟨20786082591933632423597149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27714776789244843231462865 20786082591933632423597149)
          ·
            refine ⟨7794780971975112158848931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20786082591933632423597149 7794780971975112158848931)
            ·
              refine ⟨11692171457962668238273397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7794780971975112158848931 11692171457962668238273397)
              ·
                refine ⟨1096141074184000147338131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11692171457962668238273397 1096141074184000147338131)
                ·
                  refine ⟨1644211611276000221007197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1096141074184000147338131 1644211611276000221007197)
                  ·
                    refine ⟨616579354228500082877699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1644211611276000221007197 616579354228500082877699)
                    ·
                      rfl

theorem cell22_1801176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 5, 1, 3].length) (baseStart_1801176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1801176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1801176 prefixEnd_1801176 := by exact prefixLift 1801176
  have htrace : WordTrace (prefixWord ++ tailWord_1801176) baseStart_1801176 baseEnd_1801176 := by
    simpa [prefixWord, tailWord_1801176, baseEnd_1801176] using wordTrace_append hprefix tailTrace_1801176
  have hstable : (prefixWord ++ tailWord_1801176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801176).length < 2 ^ (prefixWord ++ tailWord_1801176).sum := by decide
  have hdescent : baseEnd_1801176 < baseStart_1801176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801187 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 4, 5]
def baseStart_1801187 : Nat := 118140960795 + 1801187 * 2 ^ 59
def prefixEnd_1801187 : Nat := 4983230072969 + 3 ^ 40 * 1801187 * 2
def baseEnd_1801187 : Nat := 616583119753299720852665

theorem tailTrace_1801187 : CollatzResearch.WordTrace tailWord_1801187 prefixEnd_1801187 616583119753299720852665 := by
  unfold tailWord_1801187
  simp only [CollatzResearch.WordTrace]
  refine ⟨65694686925614592093969815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43796457950409728062646543 65694686925614592093969815)
  ·
    refine ⟨98542030388421888140954723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65694686925614592093969815 98542030388421888140954723)
    ·
      refine ⟨147813045582632832211432085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98542030388421888140954723 147813045582632832211432085)
      ·
        refine ⟨6928736511685914009910879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 147813045582632832211432085 6928736511685914009910879)
        ·
          refine ⟨10393104767528871014866319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6928736511685914009910879 10393104767528871014866319)
          ·
            refine ⟨15589657151293306522299479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10393104767528871014866319 15589657151293306522299479)
            ·
              refine ⟨23384485726939959783449219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15589657151293306522299479 23384485726939959783449219)
              ·
                refine ⟨35076728590409939675173829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23384485726939959783449219 35076728590409939675173829)
                ·
                  refine ⟨6576886610701863689095093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35076728590409939675173829 6576886610701863689095093)
                  ·
                    refine ⟨616583119753299720852665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6576886610701863689095093 616583119753299720852665)
                    ·
                      rfl

theorem cell22_1801187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 5].length) (baseStart_1801187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1801187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1801187 prefixEnd_1801187 := by exact prefixLift 1801187
  have htrace : WordTrace (prefixWord ++ tailWord_1801187) baseStart_1801187 baseEnd_1801187 := by
    simpa [prefixWord, tailWord_1801187, baseEnd_1801187] using wordTrace_append hprefix tailTrace_1801187
  have hstable : (prefixWord ++ tailWord_1801187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801187).length < 2 ^ (prefixWord ++ tailWord_1801187).sum := by decide
  have hdescent : baseEnd_1801187 < baseStart_1801187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801266 : List Nat := [3, 2, 1, 1, 2, 2, 3, 3, 2, 3]
def baseStart_1801266 : Nat := 118140960795 + 1801266 * 2 ^ 59
def prefixEnd_1801266 : Nat := 4983230072969 + 3 ^ 40 * 1801266 * 2
def baseEnd_1801266 : Nat := 616610163067769848127423

theorem tailTrace_1801266 : CollatzResearch.WordTrace tailWord_1801266 prefixEnd_1801266 616610163067769848127423 := by
  unfold tailWord_1801266
  simp only [CollatzResearch.WordTrace]
  refine ⟨16424392073082097146523913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43798378861552259057397101 16424392073082097146523913)
  ·
    refine ⟨12318294054811572859892935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16424392073082097146523913 12318294054811572859892935)
    ·
      refine ⟨18477441082217359289839403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12318294054811572859892935 18477441082217359289839403)
      ·
        refine ⟨27716161623326038934759105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18477441082217359289839403 27716161623326038934759105)
        ·
          refine ⟨20787121217494529201069329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27716161623326038934759105 20787121217494529201069329)
          ·
            refine ⟨15590340913120896900801997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20787121217494529201069329 15590340913120896900801997)
            ·
              refine ⟨5846377842420336337800749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15590340913120896900801997 5846377842420336337800749)
              ·
                refine ⟨2192391690907626126675281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5846377842420336337800749 2192391690907626126675281)
                ·
                  refine ⟨1644293768180719595006461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2192391690907626126675281 1644293768180719595006461)
                  ·
                    refine ⟨616610163067769848127423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1644293768180719595006461 616610163067769848127423)
                    ·
                      rfl

theorem cell22_1801266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3, 2, 3].length) (baseStart_1801266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1801266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1801266 prefixEnd_1801266 := by exact prefixLift 1801266
  have htrace : WordTrace (prefixWord ++ tailWord_1801266) baseStart_1801266 baseEnd_1801266 := by
    simpa [prefixWord, tailWord_1801266, baseEnd_1801266] using wordTrace_append hprefix tailTrace_1801266
  have hstable : (prefixWord ++ tailWord_1801266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801266).length < 2 ^ (prefixWord ++ tailWord_1801266).sum := by decide
  have hdescent : baseEnd_1801266 < baseStart_1801266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801324 : List Nat := [2, 2, 1, 1, 3, 2, 1, 5, 5]
def baseStart_1801324 : Nat := 118140960795 + 1801324 * 2 ^ 59
def prefixEnd_1801324 : Nat := 4983230072969 + 3 ^ 40 * 1801324 * 2
def baseEnd_1801324 : Nat := 205543339217692343392415

theorem tailTrace_1801324 : CollatzResearch.WordTrace tailWord_1801324 prefixEnd_1801324 205543339217692343392415 := by
  unfold tailWord_1801324
  simp only [CollatzResearch.WordTrace]
  refine ⟨32849841863059132245853513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43799789150745509661138017 32849841863059132245853513)
  ·
    refine ⟨24637381397294349184390135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32849841863059132245853513 24637381397294349184390135)
    ·
      refine ⟨36956072095941523776585203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24637381397294349184390135 36956072095941523776585203)
      ·
        refine ⟨55434108143912285664877805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36956072095941523776585203 55434108143912285664877805)
        ·
          refine ⟨20787790553967107124329177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55434108143912285664877805 20787790553967107124329177)
          ·
            refine ⟨15590842915475330343246883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20787790553967107124329177 15590842915475330343246883)
            ·
              refine ⟨23386264373212995514870325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15590842915475330343246883 23386264373212995514870325)
              ·
                refine ⟨2192462284988718329519093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23386264373212995514870325 2192462284988718329519093)
                ·
                  refine ⟨205543339217692343392415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2192462284988718329519093 205543339217692343392415)
                  ·
                    rfl

theorem cell22_1801324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 5].length) (baseStart_1801324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1801324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1801324 prefixEnd_1801324 := by exact prefixLift 1801324
  have htrace : WordTrace (prefixWord ++ tailWord_1801324) baseStart_1801324 baseEnd_1801324 := by
    simpa [prefixWord, tailWord_1801324, baseEnd_1801324] using wordTrace_append hprefix tailTrace_1801324
  have hstable : (prefixWord ++ tailWord_1801324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801324).length < 2 ^ (prefixWord ++ tailWord_1801324).sum := by decide
  have hdescent : baseEnd_1801324 < baseStart_1801324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801345 : List Nat := [1, 2, 4, 2, 2, 2, 2, 3, 1, 3]
def baseStart_1801345 : Nat := 118140960795 + 1801345 * 2 ^ 59
def prefixEnd_1801345 : Nat := 4983230072969 + 3 ^ 40 * 1801345 * 2
def baseEnd_1801345 : Nat := 616637206382239975402181

theorem tailTrace_1801345 : CollatzResearch.WordTrace tailWord_1801345 prefixEnd_1801345 616637206382239975402181 := by
  unfold tailWord_1801345
  simp only [CollatzResearch.WordTrace]
  refine ⟨65700449659042185078221489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43800299772694790052147659 65700449659042185078221489)
  ·
    refine ⟨49275337244281638808666117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65700449659042185078221489 49275337244281638808666117)
    ·
      refine ⟨9239125733302807276624897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49275337244281638808666117 9239125733302807276624897)
      ·
        refine ⟨6929344299977105457468673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9239125733302807276624897 6929344299977105457468673)
        ·
          refine ⟨5197008224982829093101505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6929344299977105457468673 5197008224982829093101505)
          ·
            refine ⟨3897756168737121819826129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5197008224982829093101505 3897756168737121819826129)
            ·
              refine ⟨2923317126552841364869597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3897756168737121819826129 2923317126552841364869597)
              ·
                refine ⟨1096243922457315511826099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2923317126552841364869597 1096243922457315511826099)
                ·
                  refine ⟨1644365883685973267739149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1096243922457315511826099 1644365883685973267739149)
                  ·
                    refine ⟨616637206382239975402181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1644365883685973267739149 616637206382239975402181)
                    ·
                      rfl

theorem cell22_1801345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_1801345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1801345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1801345 prefixEnd_1801345 := by exact prefixLift 1801345
  have htrace : WordTrace (prefixWord ++ tailWord_1801345) baseStart_1801345 baseEnd_1801345 := by
    simpa [prefixWord, tailWord_1801345, baseEnd_1801345] using wordTrace_append hprefix tailTrace_1801345
  have hstable : (prefixWord ++ tailWord_1801345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801345).length < 2 ^ (prefixWord ++ tailWord_1801345).sum := by decide
  have hdescent : baseEnd_1801345 < baseStart_1801345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801358 : List Nat := [4, 1, 1, 3, 2, 3, 1, 2, 5]
def baseStart_1801358 : Nat := 118140960795 + 1801358 * 2 ^ 59
def prefixEnd_1801358 : Nat := 4983230072969 + 3 ^ 40 * 1801358 * 2
def baseEnd_1801358 : Nat := 205547218849304091609047

theorem tailTrace_1801358 : CollatzResearch.WordTrace tailWord_1801358 prefixEnd_1801358 205547218849304091609047 := by
  unfold tailWord_1801358
  simp only [CollatzResearch.WordTrace]
  refine ⟨8212615475999386037305591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43800615871996725532296485 8212615475999386037305591)
  ·
    refine ⟨12318923213999079055958387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8212615475999386037305591 12318923213999079055958387)
    ·
      refine ⟨18478384820998618583937581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12318923213999079055958387 18478384820998618583937581)
      ·
        refine ⟨6929394307874481968976593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18478384820998618583937581 6929394307874481968976593)
        ·
          refine ⟨5197045730905861476732445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6929394307874481968976593 5197045730905861476732445)
          ·
            refine ⟨1948892149089698053774667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5197045730905861476732445 1948892149089698053774667)
            ·
              refine ⟨2923338223634547080662001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1948892149089698053774667 2923338223634547080662001)
              ·
                refine ⟨2192503667725910310496501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2923338223634547080662001 2192503667725910310496501)
                ·
                  refine ⟨205547218849304091609047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2192503667725910310496501 205547218849304091609047)
                  ·
                    rfl

theorem cell22_1801358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 2, 5].length) (baseStart_1801358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1801358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1801358 prefixEnd_1801358 := by exact prefixLift 1801358
  have htrace : WordTrace (prefixWord ++ tailWord_1801358) baseStart_1801358 baseEnd_1801358 := by
    simpa [prefixWord, tailWord_1801358, baseEnd_1801358] using wordTrace_append hprefix tailTrace_1801358
  have hstable : (prefixWord ++ tailWord_1801358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801358).length < 2 ^ (prefixWord ++ tailWord_1801358).sum := by decide
  have hdescent : baseEnd_1801358 < baseStart_1801358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801399 : List Nat := [1, 1, 3, 1, 4, 1, 1, 3, 1, 6]
def baseStart_1801399 : Nat := 118140960795 + 1801399 * 2 ^ 59
def prefixEnd_1801399 : Nat := 4983230072969 + 3 ^ 40 * 1801399 * 2
def baseEnd_1801399 : Nat := 616655691685801834552015

theorem tailTrace_1801399 : CollatzResearch.WordTrace tailWord_1801399 prefixEnd_1801399 616655691685801834552015 := by
  unfold tailWord_1801399
  simp only [CollatzResearch.WordTrace]
  refine ⟨65702419200846552300687251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43801612800564368200458167 65702419200846552300687251)
  ·
    refine ⟨98553628801269828451030877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65702419200846552300687251 98553628801269828451030877)
    ·
      refine ⟨36957610800476185669136579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98553628801269828451030877 36957610800476185669136579)
      ·
        refine ⟨55436416200714278503704869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36957610800476185669136579 55436416200714278503704869)
        ·
          refine ⟨10394328037633927219444663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55436416200714278503704869 10394328037633927219444663)
          ·
            refine ⟨15591492056450890829166995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10394328037633927219444663 15591492056450890829166995)
            ·
              refine ⟨23387238084676336243750493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15591492056450890829166995 23387238084676336243750493)
              ·
                refine ⟨8770214281753626091406435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23387238084676336243750493 8770214281753626091406435)
                ·
                  refine ⟨13155321422630439137109653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8770214281753626091406435 13155321422630439137109653)
                  ·
                    refine ⟨616655691685801834552015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13155321422630439137109653 616655691685801834552015)
                    ·
                      rfl

theorem cell22_1801399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_1801399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1801399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1801399 prefixEnd_1801399 := by exact prefixLift 1801399
  have htrace : WordTrace (prefixWord ++ tailWord_1801399) baseStart_1801399 baseEnd_1801399 := by
    simpa [prefixWord, tailWord_1801399, baseEnd_1801399] using wordTrace_append hprefix tailTrace_1801399
  have hstable : (prefixWord ++ tailWord_1801399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801399).length < 2 ^ (prefixWord ++ tailWord_1801399).sum := by decide
  have hdescent : baseEnd_1801399 < baseStart_1801399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801401 : List Nat := [1, 2, 1, 4, 1, 3, 1, 2, 4, 3]
def baseStart_1801401 : Nat := 118140960795 + 1801401 * 2 ^ 59
def prefixEnd_1801401 : Nat := 4983230072969 + 3 ^ 40 * 1801401 * 2
def baseEnd_1801401 : Nat := 616656376326674496002009

theorem tailTrace_1801401 : CollatzResearch.WordTrace tailWord_1801401 prefixEnd_1801401 616656376326674496002009 := by
  unfold tailWord_1801401
  simp only [CollatzResearch.WordTrace]
  refine ⟨65702492146839306642260057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43801661431226204428173371 65702492146839306642260057)
  ·
    refine ⟨49276869110129479981695043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65702492146839306642260057 49276869110129479981695043)
    ·
      refine ⟨73915303665194219972542565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49276869110129479981695043 73915303665194219972542565)
      ·
        refine ⟨13859119437223916244851731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73915303665194219972542565 13859119437223916244851731)
        ·
          refine ⟨20788679155835874367277597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13859119437223916244851731 20788679155835874367277597)
          ·
            refine ⟨7795754683438452887729099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20788679155835874367277597 7795754683438452887729099)
            ·
              refine ⟨11693632025157679331593649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7795754683438452887729099 11693632025157679331593649)
              ·
                refine ⟨8770224018868259498695237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11693632025157679331593649 8770224018868259498695237)
                ·
                  refine ⟨1644417003537798656005357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8770224018868259498695237 1644417003537798656005357)
                  ·
                    refine ⟨616656376326674496002009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1644417003537798656005357 616656376326674496002009)
                    ·
                      rfl

theorem cell22_1801401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 4, 3].length) (baseStart_1801401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1801401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1801401 prefixEnd_1801401 := by exact prefixLift 1801401
  have htrace : WordTrace (prefixWord ++ tailWord_1801401) baseStart_1801401 baseEnd_1801401 := by
    simpa [prefixWord, tailWord_1801401, baseEnd_1801401] using wordTrace_append hprefix tailTrace_1801401
  have hstable : (prefixWord ++ tailWord_1801401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801401).length < 2 ^ (prefixWord ++ tailWord_1801401).sum := by decide
  have hdescent : baseEnd_1801401 < baseStart_1801401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801523 : List Nat := [1, 1, 1, 2, 5, 3, 1, 3, 1, 4]
def baseStart_1801523 : Nat := 118140960795 + 1801523 * 2 ^ 59
def prefixEnd_1801523 : Nat := 4983230072969 + 3 ^ 40 * 1801523 * 2
def baseEnd_1801523 : Nat := 616698139419906844451635

theorem tailTrace_1801523 : CollatzResearch.WordTrace tailWord_1801523 prefixEnd_1801523 616698139419906844451635 := by
  unfold tailWord_1801523
  simp only [CollatzResearch.WordTrace]
  refine ⟨65706941852397321478201223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43804627901598214318800815 65706941852397321478201223)
  ·
    refine ⟨98560412778595982217301835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65706941852397321478201223 98560412778595982217301835)
    ·
      refine ⟨147840619167893973325952753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98560412778595982217301835 147840619167893973325952753)
      ·
        refine ⟨110880464375920479994464565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147840619167893973325952753 110880464375920479994464565)
        ·
          refine ⟨10395043535242544999481053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110880464375920479994464565 10395043535242544999481053)
          ·
            refine ⟨3898141325715954374805395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10395043535242544999481053 3898141325715954374805395)
            ·
              refine ⟨5847211988573931562208093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3898141325715954374805395 5847211988573931562208093)
              ·
                refine ⟨2192704495715224335828035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5847211988573931562208093 2192704495715224335828035)
                ·
                  refine ⟨3289056743572836503742053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2192704495715224335828035 3289056743572836503742053)
                  ·
                    refine ⟨616698139419906844451635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3289056743572836503742053 616698139419906844451635)
                    ·
                      rfl

theorem cell22_1801523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3, 1, 4].length) (baseStart_1801523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1801523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1801523 prefixEnd_1801523 := by exact prefixLift 1801523
  have htrace : WordTrace (prefixWord ++ tailWord_1801523) baseStart_1801523 baseEnd_1801523 := by
    simpa [prefixWord, tailWord_1801523, baseEnd_1801523] using wordTrace_append hprefix tailTrace_1801523
  have hstable : (prefixWord ++ tailWord_1801523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801523).length < 2 ^ (prefixWord ++ tailWord_1801523).sum := by decide
  have hdescent : baseEnd_1801523 < baseStart_1801523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801596 : List Nat := [2, 2, 2, 1, 1, 1, 4, 1, 2, 6]
def baseStart_1801596 : Nat := 118140960795 + 1801596 * 2 ^ 59
def prefixEnd_1801596 : Nat := 4983230072969 + 3 ^ 40 * 1801596 * 2
def baseEnd_1801596 : Nat := 616723128811758987376411

theorem tailTrace_1801596 : CollatzResearch.WordTrace tailWord_1801596 prefixEnd_1801596 616723128811758987376411 := by
  unfold tailWord_1801596
  simp only [CollatzResearch.WordTrace]
  refine ⟨32854802190566427472804321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43806402920755236630405761 32854802190566427472804321)
  ·
    refine ⟨24641101642924820604603241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32854802190566427472804321 24641101642924820604603241)
    ·
      refine ⟨18480826232193615453452431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24641101642924820604603241 18480826232193615453452431)
      ·
        refine ⟨27721239348290423180178647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18480826232193615453452431 27721239348290423180178647)
        ·
          refine ⟨41581859022435634770267971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27721239348290423180178647 41581859022435634770267971)
          ·
            refine ⟨62372788533653452155401957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41581859022435634770267971 62372788533653452155401957)
            ·
              refine ⟨11694897850060022279137867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62372788533653452155401957 11694897850060022279137867)
              ·
                refine ⟨17542346775090033418706801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11694897850060022279137867 17542346775090033418706801)
                ·
                  refine ⟨13156760081317525064030101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17542346775090033418706801 13156760081317525064030101)
                  ·
                    refine ⟨616723128811758987376411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13156760081317525064030101 616723128811758987376411)
                    ·
                      rfl

theorem cell22_1801596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_1801596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1801596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1801596 prefixEnd_1801596 := by exact prefixLift 1801596
  have htrace : WordTrace (prefixWord ++ tailWord_1801596) baseStart_1801596 baseEnd_1801596 := by
    simpa [prefixWord, tailWord_1801596, baseEnd_1801596] using wordTrace_append hprefix tailTrace_1801596
  have hstable : (prefixWord ++ tailWord_1801596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801596).length < 2 ^ (prefixWord ++ tailWord_1801596).sum := by decide
  have hdescent : baseEnd_1801596 < baseStart_1801596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801645 : List Nat := [1, 5, 2, 2, 1, 1, 1, 4, 5]
def baseStart_1801645 : Nat := 118140960795 + 1801645 * 2 ^ 59
def prefixEnd_1801645 : Nat := 4983230072969 + 3 ^ 40 * 1801645 * 2
def baseEnd_1801645 : Nat := 205579967504379730967087

theorem tailTrace_1801645 : CollatzResearch.WordTrace tailWord_1801645 prefixEnd_1801645 205579967504379730967087 := by
  unfold tailWord_1801645
  simp only [CollatzResearch.WordTrace]
  refine ⟨65711391557955336314142389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43807594371970224209428259 65711391557955336314142389)
  ·
    refine ⟨6160442958558312779450849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65711391557955336314142389 6160442958558312779450849)
    ·
      refine ⟨4620332218918734584588137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6160442958558312779450849 4620332218918734584588137)
      ·
        refine ⟨3465249164189050938441103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4620332218918734584588137 3465249164189050938441103)
        ·
          refine ⟨5197873746283576407661655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3465249164189050938441103 5197873746283576407661655)
          ·
            refine ⟨7796810619425364611492483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5197873746283576407661655 7796810619425364611492483)
            ·
              refine ⟨11695215929138046917238725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7796810619425364611492483 11695215929138046917238725)
              ·
                refine ⟨2192852986713383796982261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11695215929138046917238725 2192852986713383796982261)
                ·
                  refine ⟨205579967504379730967087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2192852986713383796982261 205579967504379730967087)
                  ·
                    rfl

theorem cell22_1801645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_1801645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1801645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1801645 prefixEnd_1801645 := by exact prefixLift 1801645
  have htrace : WordTrace (prefixWord ++ tailWord_1801645) baseStart_1801645 baseEnd_1801645 := by
    simpa [prefixWord, tailWord_1801645, baseEnd_1801645] using wordTrace_append hprefix tailTrace_1801645
  have hstable : (prefixWord ++ tailWord_1801645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801645).length < 2 ^ (prefixWord ++ tailWord_1801645).sum := by decide
  have hdescent : baseEnd_1801645 < baseStart_1801645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801660 : List Nat := [2, 2, 2, 4, 2, 1, 1, 1, 2, 5]
def baseStart_1801660 : Nat := 118140960795 + 1801660 * 2 ^ 59
def prefixEnd_1801660 : Nat := 4983230072969 + 3 ^ 40 * 1801660 * 2
def baseEnd_1801660 : Nat := 616745037319684153776215

theorem tailTrace_1801660 : CollatzResearch.WordTrace tailWord_1801660 prefixEnd_1801660 616745037319684153776215 := by
  unfold tailWord_1801660
  simp only [CollatzResearch.WordTrace]
  refine ⟨32855969326450496937969217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43807959101933995917292289 32855969326450496937969217)
  ·
    refine ⟨24641976994837872703476913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32855969326450496937969217 24641976994837872703476913)
    ·
      refine ⟨18481482746128404527607685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24641976994837872703476913 18481482746128404527607685)
      ·
        refine ⟨3465278014899075848926441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18481482746128404527607685 3465278014899075848926441)
        ·
          refine ⟨2598958511174306886694831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3465278014899075848926441 2598958511174306886694831)
          ·
            refine ⟨3898437766761460330042247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2598958511174306886694831 3898437766761460330042247)
            ·
              refine ⟨5847656650142190495063371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3898437766761460330042247 5847656650142190495063371)
              ·
                refine ⟨8771484975213285742595057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5847656650142190495063371 8771484975213285742595057)
                ·
                  refine ⟨6578613731409964306946293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8771484975213285742595057 6578613731409964306946293)
                  ·
                    refine ⟨616745037319684153776215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6578613731409964306946293 616745037319684153776215)
                    ·
                      rfl

theorem cell22_1801660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_1801660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1801660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1801660 prefixEnd_1801660 := by exact prefixLift 1801660
  have htrace : WordTrace (prefixWord ++ tailWord_1801660) baseStart_1801660 baseEnd_1801660 := by
    simpa [prefixWord, tailWord_1801660, baseEnd_1801660] using wordTrace_append hprefix tailTrace_1801660
  have hstable : (prefixWord ++ tailWord_1801660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801660).length < 2 ^ (prefixWord ++ tailWord_1801660).sum := by decide
  have hdescent : baseEnd_1801660 < baseStart_1801660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801688 : List Nat := [2, 1, 2, 2, 2, 1, 4, 2, 1, 5]
def baseStart_1801688 : Nat := 118140960795 + 1801688 * 2 ^ 59
def prefixEnd_1801688 : Nat := 4983230072969 + 3 ^ 40 * 1801688 * 2
def baseEnd_1801688 : Nat := 616754622291901414076129

theorem tailTrace_1801688 : CollatzResearch.WordTrace tailWord_1801688 prefixEnd_1801688 616754622291901414076129 := by
  unfold tailWord_1801688
  simp only [CollatzResearch.WordTrace]
  refine ⟨32856479948399777328978859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43808639931199703105305145 32856479948399777328978859)
  ·
    refine ⟨49284719922599665993468289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32856479948399777328978859 49284719922599665993468289)
    ·
      refine ⟨36963539941949749495101217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49284719922599665993468289 36963539941949749495101217)
      ·
        refine ⟨27722654956462312121325913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36963539941949749495101217 27722654956462312121325913)
        ·
          refine ⟨20791991217346734090994435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27722654956462312121325913 20791991217346734090994435)
          ·
            refine ⟨31187986826020101136491653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20791991217346734090994435 31187986826020101136491653)
            ·
              refine ⟨5847747529878768963092185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31187986826020101136491653 5847747529878768963092185)
              ·
                refine ⟨4385810647409076722319139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5847747529878768963092185 4385810647409076722319139)
                ·
                  refine ⟨6578715971113615083478709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4385810647409076722319139 6578715971113615083478709)
                  ·
                    refine ⟨616754622291901414076129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6578715971113615083478709 616754622291901414076129)
                    ·
                      rfl

theorem cell22_1801688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 1, 5].length) (baseStart_1801688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1801688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1801688 prefixEnd_1801688 := by exact prefixLift 1801688
  have htrace : WordTrace (prefixWord ++ tailWord_1801688) baseStart_1801688 baseEnd_1801688 := by
    simpa [prefixWord, tailWord_1801688, baseEnd_1801688] using wordTrace_append hprefix tailTrace_1801688
  have hstable : (prefixWord ++ tailWord_1801688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801688).length < 2 ^ (prefixWord ++ tailWord_1801688).sum := by decide
  have hdescent : baseEnd_1801688 < baseStart_1801688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801690 : List Nat := [3, 1, 1, 2, 3, 2, 1, 5, 4]
def baseStart_1801690 : Nat := 118140960795 + 1801690 * 2 ^ 59
def prefixEnd_1801690 : Nat := 4983230072969 + 3 ^ 40 * 1801690 * 2
def baseEnd_1801690 : Nat := 205585102310924691842041

theorem tailTrace_1801690 : CollatzResearch.WordTrace tailWord_1801690 prefixEnd_1801690 205585102310924691842041 := by
  unfold tailWord_1801690
  simp only [CollatzResearch.WordTrace]
  refine ⟨16428258210698077249882631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43808688561861539333020349 16428258210698077249882631)
  ·
    refine ⟨24642387316047115874823947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16428258210698077249882631 24642387316047115874823947)
    ·
      refine ⟨36963580974070673812235921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24642387316047115874823947 36963580974070673812235921)
      ·
        refine ⟨27722685730553005359176941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36963580974070673812235921 27722685730553005359176941)
        ·
          refine ⟨10396007148957377009691353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27722685730553005359176941 10396007148957377009691353)
          ·
            refine ⟨7797005361718032757268515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10396007148957377009691353 7797005361718032757268515)
            ·
              refine ⟨11695508042577049135902773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7797005361718032757268515 11695508042577049135902773)
              ·
                refine ⟨1096453878991598356490885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11695508042577049135902773 1096453878991598356490885)
                ·
                  refine ⟨205585102310924691842041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1096453878991598356490885 205585102310924691842041)
                  ·
                    rfl

theorem cell22_1801690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 5, 4].length) (baseStart_1801690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1801690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1801690 prefixEnd_1801690 := by exact prefixLift 1801690
  have htrace : WordTrace (prefixWord ++ tailWord_1801690) baseStart_1801690 baseEnd_1801690 := by
    simpa [prefixWord, tailWord_1801690, baseEnd_1801690] using wordTrace_append hprefix tailTrace_1801690
  have hstable : (prefixWord ++ tailWord_1801690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801690).length < 2 ^ (prefixWord ++ tailWord_1801690).sum := by decide
  have hdescent : baseEnd_1801690 < baseStart_1801690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801722 : List Nat := [3, 1, 1, 1, 1, 2, 7, 1, 2, 3]
def baseStart_1801722 : Nat := 118140960795 + 1801722 * 2 ^ 59
def prefixEnd_1801722 : Nat := 4983230072969 + 3 ^ 40 * 1801722 * 2
def baseEnd_1801722 : Nat := 616766261186736658726025

theorem tailTrace_1801722 : CollatzResearch.WordTrace tailWord_1801722 prefixEnd_1801722 616766261186736658726025 := by
  unfold tailWord_1801722
  simp only [CollatzResearch.WordTrace]
  refine ⟨16428549994669094616173855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43809466652450918976463613 16428549994669094616173855)
  ·
    refine ⟨24642824992003641924260783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16428549994669094616173855 24642824992003641924260783)
    ·
      refine ⟨36964237488005462886391175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24642824992003641924260783 36964237488005462886391175)
      ·
        refine ⟨55446356232008194329586763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36964237488005462886391175 55446356232008194329586763)
        ·
          refine ⟨83169534348012291494380145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55446356232008194329586763 83169534348012291494380145)
          ·
            refine ⟨62377150761009218620785109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83169534348012291494380145 62377150761009218620785109)
            ·
              refine ⟨1461964470961153561424651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 62377150761009218620785109 1461964470961153561424651)
              ·
                refine ⟨2192946706441730342136977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1461964470961153561424651 2192946706441730342136977)
                ·
                  refine ⟨1644710029831297756602733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2192946706441730342136977 1644710029831297756602733)
                  ·
                    refine ⟨616766261186736658726025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1644710029831297756602733 616766261186736658726025)
                    ·
                      rfl

theorem cell22_1801722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 1, 2, 3].length) (baseStart_1801722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1801722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1801722 prefixEnd_1801722 := by exact prefixLift 1801722
  have htrace : WordTrace (prefixWord ++ tailWord_1801722) baseStart_1801722 baseEnd_1801722 := by
    simpa [prefixWord, tailWord_1801722, baseEnd_1801722] using wordTrace_append hprefix tailTrace_1801722
  have hstable : (prefixWord ++ tailWord_1801722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801722).length < 2 ^ (prefixWord ++ tailWord_1801722).sum := by decide
  have hdescent : baseEnd_1801722 < baseStart_1801722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801735 : List Nat := [1, 1, 4, 3, 2, 1, 4, 6]
def baseStart_1801735 : Nat := 118140960795 + 1801735 * 2 ^ 59
def prefixEnd_1801735 : Nat := 4983230072969 + 3 ^ 40 * 1801735 * 2
def baseEnd_1801735 : Nat := 68530079039156550905665

theorem tailTrace_1801735 : CollatzResearch.WordTrace tailWord_1801735 prefixEnd_1801735 68530079039156550905665 := by
  unfold tailWord_1801735
  simp only [CollatzResearch.WordTrace]
  refine ⟨65714674127629281684918659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43809782751752854456612439 65714674127629281684918659)
  ·
    refine ⟨98572011191443922527377989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65714674127629281684918659 98572011191443922527377989)
    ·
      refine ⟨18482252098395735473883373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98572011191443922527377989 18482252098395735473883373)
      ·
        refine ⟨6930844536898400802706265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18482252098395735473883373 6930844536898400802706265)
        ·
          refine ⟨5198133402673800602029699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6930844536898400802706265 5198133402673800602029699)
          ·
            refine ⟨7797200104010700903044549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5198133402673800602029699 7797200104010700903044549)
            ·
              refine ⟨1461975019502006419320853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7797200104010700903044549 1461975019502006419320853)
              ·
                refine ⟨68530079039156550905665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1461975019502006419320853 68530079039156550905665)
                ·
                  rfl

theorem cell22_1801735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 6].length) (baseStart_1801735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1801735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1801735 prefixEnd_1801735 := by exact prefixLift 1801735
  have htrace : WordTrace (prefixWord ++ tailWord_1801735) baseStart_1801735 baseEnd_1801735 := by
    simpa [prefixWord, tailWord_1801735, baseEnd_1801735] using wordTrace_append hprefix tailTrace_1801735
  have hstable : (prefixWord ++ tailWord_1801735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801735).length < 2 ^ (prefixWord ++ tailWord_1801735).sum := by decide
  have hdescent : baseEnd_1801735 < baseStart_1801735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801758 : List Nat := [4, 3, 3, 1, 2, 1, 1, 1, 6]
def baseStart_1801758 : Nat := 118140960795 + 1801758 * 2 ^ 59
def prefixEnd_1801758 : Nat := 4983230072969 + 3 ^ 40 * 1801758 * 2
def baseEnd_1801758 : Nat := 205592861574148188275305

theorem tailTrace_1801758 : CollatzResearch.WordTrace tailWord_1801758 prefixEnd_1801758 205592861574148188275305 := by
  unfold tailWord_1801758
  simp only [CollatzResearch.WordTrace]
  refine ⟨8214439125818244576625741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43810342004363971075337285 8214439125818244576625741)
  ·
    refine ⟨3080414672181841716234653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8214439125818244576625741 3080414672181841716234653)
    ·
      refine ⟨1155155502068190643587995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3080414672181841716234653 1155155502068190643587995)
      ·
        refine ⟨1732733253102285965381993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1155155502068190643587995 1732733253102285965381993)
        ·
          refine ⟨1299549939826714474036495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1732733253102285965381993 1299549939826714474036495)
          ·
            refine ⟨1949324909740071711054743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1299549939826714474036495 1949324909740071711054743)
            ·
              refine ⟨2923987364610107566582115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1949324909740071711054743 2923987364610107566582115)
              ·
                refine ⟨4385981046915161349873173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2923987364610107566582115 4385981046915161349873173)
                ·
                  refine ⟨205592861574148188275305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4385981046915161349873173 205592861574148188275305)
                  ·
                    rfl

theorem cell22_1801758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_1801758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1801758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1801758 prefixEnd_1801758 := by exact prefixLift 1801758
  have htrace : WordTrace (prefixWord ++ tailWord_1801758) baseStart_1801758 baseEnd_1801758 := by
    simpa [prefixWord, tailWord_1801758, baseEnd_1801758] using wordTrace_append hprefix tailTrace_1801758
  have hstable : (prefixWord ++ tailWord_1801758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801758).length < 2 ^ (prefixWord ++ tailWord_1801758).sum := by decide
  have hdescent : baseEnd_1801758 < baseStart_1801758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801778 : List Nat := [3, 2, 1, 1, 2, 1, 1, 3, 1, 7]
def baseStart_1801778 : Nat := 118140960795 + 1801778 * 2 ^ 59
def prefixEnd_1801778 : Nat := 4983230072969 + 3 ^ 40 * 1801778 * 2
def baseEnd_1801778 : Nat := 616785431131171179325853

theorem tailTrace_1801778 : CollatzResearch.WordTrace tailWord_1801778 prefixEnd_1801778 616785431131171179325853 := by
  unfold tailWord_1801778
  simp only [CollatzResearch.WordTrace]
  refine ⟨16429060616618375007183497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43810828310982333352489325 16429060616618375007183497)
  ·
    refine ⟨12321795462463781255387623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16429060616618375007183497 12321795462463781255387623)
    ·
      refine ⟨18482693193695671883081435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12321795462463781255387623 18482693193695671883081435)
      ·
        refine ⟨27724039790543507824622153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18482693193695671883081435 27724039790543507824622153)
        ·
          refine ⟨20793029842907630868466615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27724039790543507824622153 20793029842907630868466615)
          ·
            refine ⟨31189544764361446302699923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20793029842907630868466615 31189544764361446302699923)
            ·
              refine ⟨46784317146542169454049885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31189544764361446302699923 46784317146542169454049885)
              ·
                refine ⟨17544118929953313545268707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46784317146542169454049885 17544118929953313545268707)
                ·
                  refine ⟨26316178394929970317903061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17544118929953313545268707 26316178394929970317903061)
                  ·
                    refine ⟨616785431131171179325853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26316178394929970317903061 616785431131171179325853)
                    ·
                      rfl

theorem cell22_1801778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_1801778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1801778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1801778 prefixEnd_1801778 := by exact prefixLift 1801778
  have htrace : WordTrace (prefixWord ++ tailWord_1801778) baseStart_1801778 baseEnd_1801778 := by
    simpa [prefixWord, tailWord_1801778, baseEnd_1801778] using wordTrace_append hprefix tailTrace_1801778
  have hstable : (prefixWord ++ tailWord_1801778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801778).length < 2 ^ (prefixWord ++ tailWord_1801778).sum := by decide
  have hdescent : baseEnd_1801778 < baseStart_1801778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801840 : List Nat := [2, 1, 1, 1, 6, 1, 1, 3, 1, 5]
def baseStart_1801840 : Nat := 118140960795 + 1801840 * 2 ^ 59
def prefixEnd_1801840 : Nat := 4983230072969 + 3 ^ 40 * 1801840 * 2
def baseEnd_1801840 : Nat := 616806654998223684275663

theorem tailTrace_1801840 : CollatzResearch.WordTrace tailWord_1801840 prefixEnd_1801840 616806654998223684275663 := by
  unfold tailWord_1801840
  simp only [CollatzResearch.WordTrace]
  refine ⟨32859251896124442308745487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43812335861499256411660649 32859251896124442308745487)
  ·
    refine ⟨49288877844186663463118231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32859251896124442308745487 49288877844186663463118231)
    ·
      refine ⟨73933316766279995194677347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49288877844186663463118231 73933316766279995194677347)
      ·
        refine ⟨110899975149419992792016021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73933316766279995194677347 110899975149419992792016021)
        ·
          refine ⟨5198436335129062162125751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 110899975149419992792016021 5198436335129062162125751)
          ·
            refine ⟨7797654502693593243188627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5198436335129062162125751 7797654502693593243188627)
            ·
              refine ⟨11696481754040389864782941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7797654502693593243188627 11696481754040389864782941)
              ·
                refine ⟨4386180657765146199293603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11696481754040389864782941 4386180657765146199293603)
                ·
                  refine ⟨6579270986647719298940405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4386180657765146199293603 6579270986647719298940405)
                  ·
                    refine ⟨616806654998223684275663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6579270986647719298940405 616806654998223684275663)
                    ·
                      rfl

theorem cell22_1801840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 1, 5].length) (baseStart_1801840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1801840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1801840 prefixEnd_1801840 := by exact prefixLift 1801840
  have htrace : WordTrace (prefixWord ++ tailWord_1801840) baseStart_1801840 baseEnd_1801840 := by
    simpa [prefixWord, tailWord_1801840, baseEnd_1801840] using wordTrace_append hprefix tailTrace_1801840
  have hstable : (prefixWord ++ tailWord_1801840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801840).length < 2 ^ (prefixWord ++ tailWord_1801840).sum := by decide
  have hdescent : baseEnd_1801840 < baseStart_1801840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
