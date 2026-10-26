import V185TrunkScan19Chunk014

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_151226 : List Nat := [3, 1, 1, 1, 2, 6, 5]
def baseStart_151226 : Nat := 118140960795 + 151226 * 2 ^ 59
def prefixEnd_151226 : Nat := 4983230072969 + 3 ^ 40 * 151226 * 2
def baseEnd_151226 : Nat := 15338592682850481240401

theorem tailTrace_151226 : CollatzResearch.WordTrace tailWord_151226 prefixEnd_151226 15338592682850481240401 := by
  unfold tailWord_151226
  simp only [CollatzResearch.WordTrace]
  refine ⟨1378916337535376047422383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3677110233427669459793021 1378916337535376047422383)
  ·
    refine ⟨2068374506303064071133575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1378916337535376047422383 2068374506303064071133575)
    ·
      refine ⟨3102561759454596106700363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2068374506303064071133575 3102561759454596106700363)
      ·
        refine ⟨4653842639181894160050545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3102561759454596106700363 4653842639181894160050545)
        ·
          refine ⟨3490381979386420620037909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4653842639181894160050545 3490381979386420620037909)
          ·
            refine ⟨163611655283738466564277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3490381979386420620037909 163611655283738466564277)
            ·
              refine ⟨15338592682850481240401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 163611655283738466564277 15338592682850481240401)
              ·
                rfl

theorem cell19_151226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 5].length) (baseStart_151226 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_151226 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_151226 prefixEnd_151226 := by exact prefixLift 151226
  have htrace : WordTrace (prefixWord ++ tailWord_151226) baseStart_151226 baseEnd_151226 := by
    simpa [prefixWord, tailWord_151226, baseEnd_151226] using wordTrace_append hprefix tailTrace_151226
  have hstable : (prefixWord ++ tailWord_151226).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151226).length < 2 ^ (prefixWord ++ tailWord_151226).sum := by decide
  have hdescent : baseEnd_151226 < baseStart_151226 := by decide
  rcases family_descends (prefixWord ++ tailWord_151226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151300 : List Nat := [2, 3, 2, 2, 1, 4, 1, 4]
def baseStart_151300 : Nat := 118140960795 + 151300 * 2 ^ 59
def prefixEnd_151300 : Nat := 4983230072969 + 3 ^ 40 * 151300 * 2
def baseEnd_151300 : Nat := 46038295126141198076557

theorem tailTrace_151300 : CollatzResearch.WordTrace tailWord_151300 prefixEnd_151300 46038295126141198076557 := by
  unfold tailWord_151300
  simp only [CollatzResearch.WordTrace]
  refine ⟨2759182175936707413941677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3678909567915609885255569 2759182175936707413941677)
  ·
    refine ⟨1034693315976265280228129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2759182175936707413941677 1034693315976265280228129)
    ·
      refine ⟨776019986982198960171097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1034693315976265280228129 776019986982198960171097)
      ·
        refine ⟨582014990236649220128323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 776019986982198960171097 582014990236649220128323)
        ·
          refine ⟨873022485354973830192485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 582014990236649220128323 873022485354973830192485)
          ·
            refine ⟨163691716004057593161091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 873022485354973830192485 163691716004057593161091)
            ·
              refine ⟨245537574006086389741637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163691716004057593161091 245537574006086389741637)
              ·
                refine ⟨46038295126141198076557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 245537574006086389741637 46038295126141198076557)
                ·
                  rfl

theorem cell19_151300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 4].length) (baseStart_151300 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_151300 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_151300 prefixEnd_151300 := by exact prefixLift 151300
  have htrace : WordTrace (prefixWord ++ tailWord_151300) baseStart_151300 baseEnd_151300 := by
    simpa [prefixWord, tailWord_151300, baseEnd_151300] using wordTrace_append hprefix tailTrace_151300
  have hstable : (prefixWord ++ tailWord_151300).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151300).length < 2 ^ (prefixWord ++ tailWord_151300).sum := by decide
  have hdescent : baseEnd_151300 < baseStart_151300 := by decide
  rcases family_descends (prefixWord ++ tailWord_151300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151319 : List Nat := [1, 1, 3, 4, 2, 2, 3, 3]
def baseStart_151319 : Nat := 118140960795 + 151319 * 2 ^ 59
def prefixEnd_151319 : Nat := 4983230072969 + 3 ^ 40 * 151319 * 2
def baseEnd_151319 : Nat := 46044076537954783654283

theorem tailTrace_151319 : CollatzResearch.WordTrace tailWord_151319 prefixEnd_151319 46044076537954783654283 := by
  unfold tailWord_151319
  simp only [CollatzResearch.WordTrace]
  refine ⟨5519057338804581072825011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3679371559203054048550007 5519057338804581072825011)
  ·
    refine ⟨8278586008206871609237517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5519057338804581072825011 8278586008206871609237517)
    ·
      refine ⟨3104469753077576853464069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8278586008206871609237517 3104469753077576853464069)
      ·
        refine ⟨582088078702045660024513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3104469753077576853464069 582088078702045660024513)
        ·
          refine ⟨436566059026534245018385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 582088078702045660024513 436566059026534245018385)
          ·
            refine ⟨327424544269900683763789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 436566059026534245018385 327424544269900683763789)
            ·
              refine ⟨122784204101212756411421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 327424544269900683763789 122784204101212756411421)
              ·
                refine ⟨46044076537954783654283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122784204101212756411421 46044076537954783654283)
                ·
                  rfl

theorem cell19_151319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 3].length) (baseStart_151319 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_151319 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_151319 prefixEnd_151319 := by exact prefixLift 151319
  have htrace : WordTrace (prefixWord ++ tailWord_151319) baseStart_151319 baseEnd_151319 := by
    simpa [prefixWord, tailWord_151319, baseEnd_151319] using wordTrace_append hprefix tailTrace_151319
  have hstable : (prefixWord ++ tailWord_151319).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151319).length < 2 ^ (prefixWord ++ tailWord_151319).sum := by decide
  have hdescent : baseEnd_151319 < baseStart_151319 := by decide
  rcases family_descends (prefixWord ++ tailWord_151319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151378 : List Nat := [3, 2, 2, 1, 1, 4, 1, 5]
def baseStart_151378 : Nat := 118140960795 + 151378 * 2 ^ 59
def prefixEnd_151378 : Nat := 4983230072969 + 3 ^ 40 * 151378 * 2
def baseEnd_151378 : Nat := 46062029343060128343011

theorem tailTrace_151378 : CollatzResearch.WordTrace tailWord_151378 prefixEnd_151378 46062029343060128343011 := by
  unfold tailWord_151378
  simp only [CollatzResearch.WordTrace]
  refine ⟨1380302311397708537305697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3680806163727222766148525 1380302311397708537305697)
  ·
    refine ⟨1035226733548281402979273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1380302311397708537305697 1035226733548281402979273)
    ·
      refine ⟨776420050161211052234455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1035226733548281402979273 776420050161211052234455)
      ·
        refine ⟨1164630075241816578351683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 776420050161211052234455 1164630075241816578351683)
        ·
          refine ⟨1746945112862724867527525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1164630075241816578351683 1746945112862724867527525)
          ·
            refine ⟨327552208661760912661411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1746945112862724867527525 327552208661760912661411)
            ·
              refine ⟨491328312992641368992117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327552208661760912661411 491328312992641368992117)
              ·
                refine ⟨46062029343060128343011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 491328312992641368992117 46062029343060128343011)
                ·
                  rfl

theorem cell19_151378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_151378 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_151378 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_151378 prefixEnd_151378 := by exact prefixLift 151378
  have htrace : WordTrace (prefixWord ++ tailWord_151378) baseStart_151378 baseEnd_151378 := by
    simpa [prefixWord, tailWord_151378, baseEnd_151378] using wordTrace_append hprefix tailTrace_151378
  have hstable : (prefixWord ++ tailWord_151378).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151378).length < 2 ^ (prefixWord ++ tailWord_151378).sum := by decide
  have hdescent : baseEnd_151378 < baseStart_151378 := by decide
  rcases family_descends (prefixWord ++ tailWord_151378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151395 : List Nat := [1, 1, 1, 5, 5, 1, 5]
def baseStart_151395 : Nat := 118140960795 + 151395 * 2 ^ 59
def prefixEnd_151395 : Nat := 4983230072969 + 3 ^ 40 * 151395 * 2
def baseEnd_151395 : Nat := 15355734061736375321729

theorem tailTrace_151395 : CollatzResearch.WordTrace tailWord_151395 prefixEnd_151395 15355734061736375321729 := by
  unfold tailWord_151395
  simp only [CollatzResearch.WordTrace]
  refine ⟨5521829286529246052591639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3681219524352830701727759 5521829286529246052591639)
  ·
    refine ⟨8282743929793869078887459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5521829286529246052591639 8282743929793869078887459)
    ·
      refine ⟨12424115894690803618331189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8282743929793869078887459 12424115894690803618331189)
      ·
        refine ⟨1164760865127262839218549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12424115894690803618331189 1164760865127262839218549)
        ·
          refine ⟨109196331105680891176739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1164760865127262839218549 109196331105680891176739)
          ·
            refine ⟨163794496658521336765109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109196331105680891176739 163794496658521336765109)
            ·
              refine ⟨15355734061736375321729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 163794496658521336765109 15355734061736375321729)
              ·
                rfl

theorem cell19_151395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 5].length) (baseStart_151395 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_151395 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_151395 prefixEnd_151395 := by exact prefixLift 151395
  have htrace : WordTrace (prefixWord ++ tailWord_151395) baseStart_151395 baseEnd_151395 := by
    simpa [prefixWord, tailWord_151395, baseEnd_151395] using wordTrace_append hprefix tailTrace_151395
  have hstable : (prefixWord ++ tailWord_151395).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151395).length < 2 ^ (prefixWord ++ tailWord_151395).sum := by decide
  have hdescent : baseEnd_151395 < baseStart_151395 := by decide
  rcases family_descends (prefixWord ++ tailWord_151395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151418 : List Nat := [3, 1, 1, 1, 1, 1, 5, 6]
def baseStart_151418 : Nat := 118140960795 + 151418 * 2 ^ 59
def prefixEnd_151418 : Nat := 4983230072969 + 3 ^ 40 * 151418 * 2
def baseEnd_151418 : Nat := 46074200736351887454013

theorem tailTrace_151418 : CollatzResearch.WordTrace tailWord_151418 prefixEnd_151418 46074200736351887454013 := by
  unfold tailWord_151418
  simp only [CollatzResearch.WordTrace]
  refine ⟨1380667041361480245169727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3681778776963947320452605 1380667041361480245169727)
  ·
    refine ⟨2071000562042220367754591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1380667041361480245169727 2071000562042220367754591)
    ·
      refine ⟨3106500843063330551631887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2071000562042220367754591 3106500843063330551631887)
      ·
        refine ⟨4659751264594995827447831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3106500843063330551631887 4659751264594995827447831)
        ·
          refine ⟨6989626896892493741171747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4659751264594995827447831 6989626896892493741171747)
          ·
            refine ⟨10484440345338740611757621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6989626896892493741171747 10484440345338740611757621)
            ·
              refine ⟨982916282375506932352277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10484440345338740611757621 982916282375506932352277)
              ·
                refine ⟨46074200736351887454013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 982916282375506932352277 46074200736351887454013)
                ·
                  rfl

theorem cell19_151418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_151418 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_151418 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_151418 prefixEnd_151418 := by exact prefixLift 151418
  have htrace : WordTrace (prefixWord ++ tailWord_151418) baseStart_151418 baseEnd_151418 := by
    simpa [prefixWord, tailWord_151418, baseEnd_151418] using wordTrace_append hprefix tailTrace_151418
  have hstable : (prefixWord ++ tailWord_151418).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151418).length < 2 ^ (prefixWord ++ tailWord_151418).sum := by decide
  have hdescent : baseEnd_151418 < baseStart_151418 := by decide
  rcases family_descends (prefixWord ++ tailWord_151418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151473 : List Nat := [1, 2, 2, 4, 2, 1, 3, 4]
def baseStart_151473 : Nat := 118140960795 + 151473 * 2 ^ 59
def prefixEnd_151473 : Nat := 4983230072969 + 3 ^ 40 * 151473 * 2
def baseEnd_151473 : Nat := 46090936402128056231641

theorem tailTrace_151473 : CollatzResearch.WordTrace tailWord_151473 prefixEnd_151473 46090936402128056231641 := by
  unfold tailWord_151473
  simp only [CollatzResearch.WordTrace]
  refine ⟨5524674180246665373931073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3683116120164443582620715 5524674180246665373931073)
  ·
    refine ⟨4143505635184999030448305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5524674180246665373931073 4143505635184999030448305)
    ·
      refine ⟨3107629226388749272836229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4143505635184999030448305 3107629226388749272836229)
      ·
        refine ⟨582680479947890488656793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3107629226388749272836229 582680479947890488656793)
        ·
          refine ⟨437010359960917866492595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 582680479947890488656793 437010359960917866492595)
          ·
            refine ⟨655515539941376799738893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 437010359960917866492595 655515539941376799738893)
            ·
              refine ⟨245818327478016299902085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 655515539941376799738893 245818327478016299902085)
              ·
                refine ⟨46090936402128056231641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 245818327478016299902085 46090936402128056231641)
                ·
                  rfl

theorem cell19_151473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 4].length) (baseStart_151473 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_151473 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_151473 prefixEnd_151473 := by exact prefixLift 151473
  have htrace : WordTrace (prefixWord ++ tailWord_151473) baseStart_151473 baseEnd_151473 := by
    simpa [prefixWord, tailWord_151473, baseEnd_151473] using wordTrace_append hprefix tailTrace_151473
  have hstable : (prefixWord ++ tailWord_151473).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151473).length < 2 ^ (prefixWord ++ tailWord_151473).sum := by decide
  have hdescent : baseEnd_151473 < baseStart_151473 := by decide
  rcases family_descends (prefixWord ++ tailWord_151473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151549 : List Nat := [1, 4, 1, 1, 1, 2, 6, 3]
def baseStart_151549 : Nat := 118140960795 + 151549 * 2 ^ 59
def prefixEnd_151549 : Nat := 4983230072969 + 3 ^ 40 * 151549 * 2
def baseEnd_151549 : Nat := 46114062049382398542545

theorem tailTrace_151549 : CollatzResearch.WordTrace tailWord_151549 prefixEnd_151549 46114062049382398542545 := by
  unfold tailWord_151549
  simp only [CollatzResearch.WordTrace]
  refine ⟨5527446127971330353697701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3684964085314220235798467 5527446127971330353697701)
  ·
    refine ⟨1036396148994624441318319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5527446127971330353697701 1036396148994624441318319)
    ·
      refine ⟨1554594223491936661977479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1036396148994624441318319 1554594223491936661977479)
      ·
        refine ⟨2331891335237904992966219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1554594223491936661977479 2331891335237904992966219)
        ·
          refine ⟨3497837002856857489449329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2331891335237904992966219 3497837002856857489449329)
          ·
            refine ⟨2623377752142643117086997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3497837002856857489449329 2623377752142643117086997)
            ·
              refine ⟨122970832131686396113453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2623377752142643117086997 122970832131686396113453)
              ·
                refine ⟨46114062049382398542545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122970832131686396113453 46114062049382398542545)
                ·
                  rfl

theorem cell19_151549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 3].length) (baseStart_151549 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_151549 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_151549 prefixEnd_151549 := by exact prefixLift 151549
  have htrace : WordTrace (prefixWord ++ tailWord_151549) baseStart_151549 baseEnd_151549 := by
    simpa [prefixWord, tailWord_151549, baseEnd_151549] using wordTrace_append hprefix tailTrace_151549
  have hstable : (prefixWord ++ tailWord_151549).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151549).length < 2 ^ (prefixWord ++ tailWord_151549).sum := by decide
  have hdescent : baseEnd_151549 < baseStart_151549 := by decide
  rcases family_descends (prefixWord ++ tailWord_151549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151589 : List Nat := [1, 3, 1, 2, 2, 3, 1, 6]
def baseStart_151589 : Nat := 118140960795 + 151589 * 2 ^ 59
def prefixEnd_151589 : Nat := 4983230072969 + 3 ^ 40 * 151589 * 2
def baseEnd_151589 : Nat := 46126233442674157653547

theorem tailTrace_151589 : CollatzResearch.WordTrace tailWord_151589 prefixEnd_151589 46126233442674157653547 := by
  unfold tailWord_151589
  simp only [CollatzResearch.WordTrace]
  refine ⟨5528905047826417185153821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3685936698550944790102547 5528905047826417185153821)
  ·
    refine ⟨2073339392934906444432683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5528905047826417185153821 2073339392934906444432683)
    ·
      refine ⟨3110009089402359666649025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2073339392934906444432683 3110009089402359666649025)
      ·
        refine ⟨2332506817051769749986769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3110009089402359666649025 2332506817051769749986769)
        ·
          refine ⟨1749380112788827312490077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2332506817051769749986769 1749380112788827312490077)
          ·
            refine ⟨656017542295810242183779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1749380112788827312490077 656017542295810242183779)
            ·
              refine ⟨984026313443715363275669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 656017542295810242183779 984026313443715363275669)
              ·
                refine ⟨46126233442674157653547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 984026313443715363275669 46126233442674157653547)
                ·
                  rfl

theorem cell19_151589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 6].length) (baseStart_151589 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_151589 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_151589 prefixEnd_151589 := by exact prefixLift 151589
  have htrace : WordTrace (prefixWord ++ tailWord_151589) baseStart_151589 baseEnd_151589 := by
    simpa [prefixWord, tailWord_151589, baseEnd_151589] using wordTrace_append hprefix tailTrace_151589
  have hstable : (prefixWord ++ tailWord_151589).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151589).length < 2 ^ (prefixWord ++ tailWord_151589).sum := by decide
  have hdescent : baseEnd_151589 < baseStart_151589 := by decide
  rcases family_descends (prefixWord ++ tailWord_151589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151606 : List Nat := [5, 1, 2, 1, 1, 1, 1, 7]
def baseStart_151606 : Nat := 118140960795 + 151606 * 2 ^ 59
def prefixEnd_151606 : Nat := 4983230072969 + 3 ^ 40 * 151606 * 2
def baseEnd_151606 : Nat := 46131406284823155275723

theorem tailTrace_151606 : CollatzResearch.WordTrace tailWord_151606 prefixEnd_151606 46131406284823155275723 := by
  unfold tailWord_151606
  simp only [CollatzResearch.WordTrace]
  refine ⟨345595318047801818032667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3686350059176552725681781 345595318047801818032667)
  ·
    refine ⟨518392977071702727049001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 345595318047801818032667 518392977071702727049001)
    ·
      refine ⟨388794732803777045286751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 518392977071702727049001 388794732803777045286751)
      ·
        refine ⟨583192099205665567930127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388794732803777045286751 583192099205665567930127)
        ·
          refine ⟨874788148808498351895191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 583192099205665567930127 874788148808498351895191)
          ·
            refine ⟨1312182223212747527842787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 874788148808498351895191 1312182223212747527842787)
            ·
              refine ⟨1968273334819121291764181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1312182223212747527842787 1968273334819121291764181)
              ·
                refine ⟨46131406284823155275723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1968273334819121291764181 46131406284823155275723)
                ·
                  rfl

theorem cell19_151606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_151606 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_151606 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_151606 prefixEnd_151606 := by exact prefixLift 151606
  have htrace : WordTrace (prefixWord ++ tailWord_151606) baseStart_151606 baseEnd_151606 := by
    simpa [prefixWord, tailWord_151606, baseEnd_151606] using wordTrace_append hprefix tailTrace_151606
  have hstable : (prefixWord ++ tailWord_151606).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151606).length < 2 ^ (prefixWord ++ tailWord_151606).sum := by decide
  have hdescent : baseEnd_151606 < baseStart_151606 := by decide
  rcases family_descends (prefixWord ++ tailWord_151606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151644 : List Nat := [2, 2, 4, 1, 1, 2, 3, 4]
def baseStart_151644 : Nat := 118140960795 + 151644 * 2 ^ 59
def prefixEnd_151644 : Nat := 4983230072969 + 3 ^ 40 * 151644 * 2
def baseEnd_151644 : Nat := 46142969108450326431175

theorem tailTrace_151644 : CollatzResearch.WordTrace tailWord_151644 prefixEnd_151644 46142969108450326431175 := by
  unfold tailWord_151644
  simp only [CollatzResearch.WordTrace]
  refine ⟨2765455531313580789202993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3687274041751441052270657 2765455531313580789202993)
  ·
    refine ⟨2074091648485185591902245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2765455531313580789202993 2074091648485185591902245)
    ·
      refine ⟨388892184090972298481671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2074091648485185591902245 388892184090972298481671)
      ·
        refine ⟨583338276136458447722507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388892184090972298481671 583338276136458447722507)
        ·
          refine ⟨875007414204687671583761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 583338276136458447722507 875007414204687671583761)
          ·
            refine ⟨656255560653515753687821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 875007414204687671583761 656255560653515753687821)
            ·
              refine ⟨246095835245068407632933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 656255560653515753687821 246095835245068407632933)
              ·
                refine ⟨46142969108450326431175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 246095835245068407632933 46142969108450326431175)
                ·
                  rfl

theorem cell19_151644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 4].length) (baseStart_151644 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_151644 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_151644 prefixEnd_151644 := by exact prefixLift 151644
  have htrace : WordTrace (prefixWord ++ tailWord_151644) baseStart_151644 baseEnd_151644 := by
    simpa [prefixWord, tailWord_151644, baseEnd_151644] using wordTrace_append hprefix tailTrace_151644
  have hstable : (prefixWord ++ tailWord_151644).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151644).length < 2 ^ (prefixWord ++ tailWord_151644).sum := by decide
  have hdescent : baseEnd_151644 < baseStart_151644 := by decide
  rcases family_descends (prefixWord ++ tailWord_151644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151663 : List Nat := [1, 1, 2, 1, 3, 5, 3, 3]
def baseStart_151663 : Nat := 118140960795 + 151663 * 2 ^ 59
def prefixEnd_151663 : Nat := 4983230072969 + 3 ^ 40 * 151663 * 2
def baseEnd_151663 : Nat := 46148750520263912008901

theorem tailTrace_151663 : CollatzResearch.WordTrace tailWord_151663 prefixEnd_151663 46148750520263912008901 := by
  unfold tailWord_151663
  simp only [CollatzResearch.WordTrace]
  refine ⟨5531604049558327823347643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3687736033038885215565095 5531604049558327823347643)
  ·
    refine ⟨8297406074337491735021465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5531604049558327823347643 8297406074337491735021465)
    ·
      refine ⟨6223054555753118801266099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8297406074337491735021465 6223054555753118801266099)
      ·
        refine ⟨9334581833629678201899149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6223054555753118801266099 9334581833629678201899149)
        ·
          refine ⟨3500468187611129325712181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9334581833629678201899149 3500468187611129325712181)
          ·
            refine ⟨328168892588543374285517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3500468187611129325712181 328168892588543374285517)
            ·
              refine ⟨123063334720703765357069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 328168892588543374285517 123063334720703765357069)
              ·
                refine ⟨46148750520263912008901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123063334720703765357069 46148750520263912008901)
                ·
                  rfl

theorem cell19_151663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 3].length) (baseStart_151663 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_151663 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_151663 prefixEnd_151663 := by exact prefixLift 151663
  have htrace : WordTrace (prefixWord ++ tailWord_151663) baseStart_151663 baseEnd_151663 := by
    simpa [prefixWord, tailWord_151663, baseEnd_151663] using wordTrace_append hprefix tailTrace_151663
  have hstable : (prefixWord ++ tailWord_151663).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151663).length < 2 ^ (prefixWord ++ tailWord_151663).sum := by decide
  have hdescent : baseEnd_151663 < baseStart_151663 := by decide
  rcases family_descends (prefixWord ++ tailWord_151663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151684 : List Nat := [2, 3, 2, 1, 2, 1, 8]
def baseStart_151684 : Nat := 118140960795 + 151684 * 2 ^ 59
def prefixEnd_151684 : Nat := 4983230072969 + 3 ^ 40 * 151684 * 2
def baseEnd_151684 : Nat := 15385046833914028514059

theorem tailTrace_151684 : CollatzResearch.WordTrace tailWord_151684 prefixEnd_151684 15385046833914028514059 := by
  unfold tailWord_151684
  simp only [CollatzResearch.WordTrace]
  refine ⟨2766184991241124204931053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3688246654988165606574737 2766184991241124204931053)
  ·
    refine ⟨1037319371715421576849145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2766184991241124204931053 1037319371715421576849145)
    ·
      refine ⟨777989528786566182636859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1037319371715421576849145 777989528786566182636859)
      ·
        refine ⟨1166984293179849273955289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 777989528786566182636859 1166984293179849273955289)
        ·
          refine ⟨875238219884886955466467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1166984293179849273955289 875238219884886955466467)
          ·
            refine ⟨1312857329827330433199701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 875238219884886955466467 1312857329827330433199701)
            ·
              refine ⟨15385046833914028514059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1312857329827330433199701 15385046833914028514059)
              ·
                rfl

theorem cell19_151684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 8].length) (baseStart_151684 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_151684 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_151684 prefixEnd_151684 := by exact prefixLift 151684
  have htrace : WordTrace (prefixWord ++ tailWord_151684) baseStart_151684 baseEnd_151684 := by
    simpa [prefixWord, tailWord_151684, baseEnd_151684] using wordTrace_append hprefix tailTrace_151684
  have hstable : (prefixWord ++ tailWord_151684).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151684).length < 2 ^ (prefixWord ++ tailWord_151684).sum := by decide
  have hdescent : baseEnd_151684 < baseStart_151684 := by decide
  rcases family_descends (prefixWord ++ tailWord_151684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151716 : List Nat := [2, 3, 1, 2, 5, 1, 2, 3]
def baseStart_151716 : Nat := 118140960795 + 151716 * 2 ^ 59
def prefixEnd_151716 : Nat := 4983230072969 + 3 ^ 40 * 151716 * 2
def baseEnd_151716 : Nat := 46164877616375492830979

theorem tailTrace_151716 : CollatzResearch.WordTrace tailWord_151716 prefixEnd_151716 46164877616375492830979 := by
  unfold tailWord_151716
  simp only [CollatzResearch.WordTrace]
  refine ⟨2766768559183158937513501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3689024745577545250018001 2766768559183158937513501)
  ·
    refine ⟨1037538209693684601567563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2766768559183158937513501 1037538209693684601567563)
    ·
      refine ⟨1556307314540526902351345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1037538209693684601567563 1556307314540526902351345)
      ·
        refine ⟨1167230485905395176763509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1556307314540526902351345 1167230485905395176763509)
        ·
          refine ⟨109427858053630797821579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1167230485905395176763509 109427858053630797821579)
          ·
            refine ⟨164141787080446196732369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109427858053630797821579 164141787080446196732369)
            ·
              refine ⟨123106340310334647549277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164141787080446196732369 123106340310334647549277)
              ·
                refine ⟨46164877616375492830979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123106340310334647549277 46164877616375492830979)
                ·
                  rfl

theorem cell19_151716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 3].length) (baseStart_151716 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_151716 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_151716 prefixEnd_151716 := by exact prefixLift 151716
  have htrace : WordTrace (prefixWord ++ tailWord_151716) baseStart_151716 baseEnd_151716 := by
    simpa [prefixWord, tailWord_151716, baseEnd_151716] using wordTrace_append hprefix tailTrace_151716
  have hstable : (prefixWord ++ tailWord_151716).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151716).length < 2 ^ (prefixWord ++ tailWord_151716).sum := by decide
  have hdescent : baseEnd_151716 < baseStart_151716 := by decide
  rcases family_descends (prefixWord ++ tailWord_151716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151756 : List Nat := [2, 2, 1, 6, 1, 1, 2, 4]
def baseStart_151756 : Nat := 118140960795 + 151756 * 2 ^ 59
def prefixEnd_151756 : Nat := 4983230072969 + 3 ^ 40 * 151756 * 2
def baseEnd_151756 : Nat := 46177049009667251941981

theorem tailTrace_151756 : CollatzResearch.WordTrace tailWord_151756 prefixEnd_151756 46177049009667251941981 := by
  unfold tailWord_151756
  simp only [CollatzResearch.WordTrace]
  refine ⟨2767498019110702353241561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3689997358814269804322081 2767498019110702353241561)
  ·
    refine ⟨2075623514333026764931171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2767498019110702353241561 2075623514333026764931171)
    ·
      refine ⟨3113435271499540147396757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2075623514333026764931171 3113435271499540147396757)
      ·
        refine ⟨145942278351540944409223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3113435271499540147396757 145942278351540944409223)
        ·
          refine ⟨218913417527311416613835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145942278351540944409223 218913417527311416613835)
          ·
            refine ⟨328370126290967124920753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218913417527311416613835 328370126290967124920753)
            ·
              refine ⟨246277594718225343690565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 328370126290967124920753 246277594718225343690565)
              ·
                refine ⟨46177049009667251941981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 246277594718225343690565 46177049009667251941981)
                ·
                  rfl

theorem cell19_151756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 4].length) (baseStart_151756 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_151756 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_151756 prefixEnd_151756 := by exact prefixLift 151756
  have htrace : WordTrace (prefixWord ++ tailWord_151756) baseStart_151756 baseEnd_151756 := by
    simpa [prefixWord, tailWord_151756, baseEnd_151756] using wordTrace_append hprefix tailTrace_151756
  have hstable : (prefixWord ++ tailWord_151756).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151756).length < 2 ^ (prefixWord ++ tailWord_151756).sum := by decide
  have hdescent : baseEnd_151756 < baseStart_151756 := by decide
  rcases family_descends (prefixWord ++ tailWord_151756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151758 : List Nat := [4, 1, 1, 1, 4, 2, 2, 4]
def baseStart_151758 : Nat := 118140960795 + 151758 * 2 ^ 59
def prefixEnd_151758 : Nat := 4983230072969 + 3 ^ 40 * 151758 * 2
def baseEnd_151758 : Nat := 46177657579331839897531

theorem tailTrace_151758 : CollatzResearch.WordTrace tailWord_151758 prefixEnd_151758 46177657579331839897531 := by
  unfold tailWord_151758
  simp only [CollatzResearch.WordTrace]
  refine ⟨691883623026769881006991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3690045989476106032037285 691883623026769881006991)
  ·
    refine ⟨1037825434540154821510487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 691883623026769881006991 1037825434540154821510487)
    ·
      refine ⟨1556738151810232232265731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1037825434540154821510487 1556738151810232232265731)
      ·
        refine ⟨2335107227715348348398597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1556738151810232232265731 2335107227715348348398597)
        ·
          refine ⟨437832605196627815324737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2335107227715348348398597 437832605196627815324737)
          ·
            refine ⟨328374453897470861493553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 437832605196627815324737 328374453897470861493553)
            ·
              refine ⟨246280840423103146120165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 328374453897470861493553 246280840423103146120165)
              ·
                refine ⟨46177657579331839897531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 246280840423103146120165 46177657579331839897531)
                ·
                  rfl

theorem cell19_151758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_151758 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_151758 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_151758 prefixEnd_151758 := by exact prefixLift 151758
  have htrace : WordTrace (prefixWord ++ tailWord_151758) baseStart_151758 baseEnd_151758 := by
    simpa [prefixWord, tailWord_151758, baseEnd_151758] using wordTrace_append hprefix tailTrace_151758
  have hstable : (prefixWord ++ tailWord_151758).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151758).length < 2 ^ (prefixWord ++ tailWord_151758).sum := by decide
  have hdescent : baseEnd_151758 < baseStart_151758 := by decide
  rcases family_descends (prefixWord ++ tailWord_151758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151796 : List Nat := [2, 6, 1, 10]
def baseStart_151796 : Nat := 118140960795 + 151796 * 2 ^ 59
def prefixEnd_151796 : Nat := 4983230072969 + 3 ^ 40 * 151796 * 2
def baseEnd_151796 : Nat := 570237288925419889543

theorem tailTrace_151796 : CollatzResearch.WordTrace tailWord_151796 prefixEnd_151796 570237288925419889543 := by
  unfold tailWord_151796
  simp only [CollatzResearch.WordTrace]
  refine ⟨2768227479038245768969621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3690969972050994358626161 2768227479038245768969621)
  ·
    refine ⟨129760663079917770420451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2768227479038245768969621 129760663079917770420451)
    ·
      refine ⟨194640994619876655630677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129760663079917770420451 194640994619876655630677)
      ·
        refine ⟨570237288925419889543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 194640994619876655630677 570237288925419889543)
        ·
          rfl

theorem cell19_151796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 10].length) (baseStart_151796 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_151796 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_151796 prefixEnd_151796 := by exact prefixLift 151796
  have htrace : WordTrace (prefixWord ++ tailWord_151796) baseStart_151796 baseEnd_151796 := by
    simpa [prefixWord, tailWord_151796, baseEnd_151796] using wordTrace_append hprefix tailTrace_151796
  have hstable : (prefixWord ++ tailWord_151796).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151796).length < 2 ^ (prefixWord ++ tailWord_151796).sum := by decide
  have hdescent : baseEnd_151796 < baseStart_151796 := by decide
  rcases family_descends (prefixWord ++ tailWord_151796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151817 : List Nat := [1, 2, 1, 1, 3, 4, 3, 4]
def baseStart_151817 : Nat := 118140960795 + 151817 * 2 ^ 59
def prefixEnd_151817 : Nat := 4983230072969 + 3 ^ 40 * 151817 * 2
def baseEnd_151817 : Nat := 46195610384437184586259

theorem tailTrace_151817 : CollatzResearch.WordTrace tailWord_151817 prefixEnd_151817 46195610384437184586259 := by
  unfold tailWord_151817
  simp only [CollatzResearch.WordTrace]
  refine ⟨5537220891000412124453705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3691480594000274749635803 5537220891000412124453705)
  ·
    refine ⟨4152915668250309093340279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5537220891000412124453705 4152915668250309093340279)
    ·
      refine ⟨6229373502375463640010419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4152915668250309093340279 6229373502375463640010419)
      ·
        refine ⟨9344060253563195460015629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6229373502375463640010419 9344060253563195460015629)
        ·
          refine ⟨3504022595086198297505861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9344060253563195460015629 3504022595086198297505861)
          ·
            refine ⟨657004236578662180782349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3504022595086198297505861 657004236578662180782349)
            ·
              refine ⟨246376588716998317793381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 657004236578662180782349 246376588716998317793381)
              ·
                refine ⟨46195610384437184586259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 246376588716998317793381 46195610384437184586259)
                ·
                  rfl

theorem cell19_151817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 4].length) (baseStart_151817 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_151817 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_151817 prefixEnd_151817 := by exact prefixLift 151817
  have htrace : WordTrace (prefixWord ++ tailWord_151817) baseStart_151817 baseEnd_151817 := by
    simpa [prefixWord, tailWord_151817, baseEnd_151817] using wordTrace_append hprefix tailTrace_151817
  have hstable : (prefixWord ++ tailWord_151817).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151817).length < 2 ^ (prefixWord ++ tailWord_151817).sum := by decide
  have hdescent : baseEnd_151817 < baseStart_151817 := by decide
  rcases family_descends (prefixWord ++ tailWord_151817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151902 : List Nat := [4, 4, 2, 1, 2, 1, 5]
def baseStart_151902 : Nat := 118140960795 + 151902 * 2 ^ 59
def prefixEnd_151902 : Nat := 4983230072969 + 3 ^ 40 * 151902 * 2
def baseEnd_151902 : Nat := 15407158198394057565713

theorem tailTrace_151902 : CollatzResearch.WordTrace tailWord_151902 prefixEnd_151902 15407158198394057565713 := by
  unfold tailWord_151902
  simp only [CollatzResearch.WordTrace]
  refine ⟨692540136961558955162245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3693547397128314427531973 692540136961558955162245)
  ·
    refine ⟨129851275680292304092921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 692540136961558955162245 129851275680292304092921)
    ·
      refine ⟨97388456760219228069691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129851275680292304092921 97388456760219228069691)
      ·
        refine ⟨146082685140328842104537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97388456760219228069691 146082685140328842104537)
        ·
          refine ⟨109562013855246631578403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146082685140328842104537 109562013855246631578403)
          ·
            refine ⟨164343020782869947367605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109562013855246631578403 164343020782869947367605)
            ·
              refine ⟨15407158198394057565713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 164343020782869947367605 15407158198394057565713)
              ·
                rfl

theorem cell19_151902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 5].length) (baseStart_151902 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_151902 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_151902 prefixEnd_151902 := by exact prefixLift 151902
  have htrace : WordTrace (prefixWord ++ tailWord_151902) baseStart_151902 baseEnd_151902 := by
    simpa [prefixWord, tailWord_151902, baseEnd_151902] using wordTrace_append hprefix tailTrace_151902
  have hstable : (prefixWord ++ tailWord_151902).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151902).length < 2 ^ (prefixWord ++ tailWord_151902).sum := by decide
  have hdescent : baseEnd_151902 < baseStart_151902 := by decide
  rcases family_descends (prefixWord ++ tailWord_151902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151912 : List Nat := [2, 1, 4, 2, 2, 1, 7]
def baseStart_151912 : Nat := 118140960795 + 151912 * 2 ^ 59
def prefixEnd_151912 : Nat := 4983230072969 + 3 ^ 40 * 151912 * 2
def baseEnd_151912 : Nat := 15408172481168370824963

theorem tailTrace_151912 : CollatzResearch.WordTrace tailWord_151912 prefixEnd_151912 15408172481168370824963 := by
  unfold tailWord_151912
  simp only [CollatzResearch.WordTrace]
  refine ⟨2770342912828121674580995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3693790550437495566107993 2770342912828121674580995)
  ·
    refine ⟨4155514369242182511871493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2770342912828121674580995 4155514369242182511871493)
    ·
      refine ⟨779158944232909220975905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4155514369242182511871493 779158944232909220975905)
      ·
        refine ⟨584369208174681915731929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 779158944232909220975905 584369208174681915731929)
        ·
          refine ⟨438276906131011436798947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 584369208174681915731929 438276906131011436798947)
          ·
            refine ⟨657415359196517155198421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 438276906131011436798947 657415359196517155198421)
            ·
              refine ⟨15408172481168370824963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 657415359196517155198421 15408172481168370824963)
              ·
                rfl

theorem cell19_151912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 7].length) (baseStart_151912 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_151912 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_151912 prefixEnd_151912 := by exact prefixLift 151912
  have htrace : WordTrace (prefixWord ++ tailWord_151912) baseStart_151912 baseEnd_151912 := by
    simpa [prefixWord, tailWord_151912, baseEnd_151912] using wordTrace_append hprefix tailTrace_151912
  have hstable : (prefixWord ++ tailWord_151912).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151912).length < 2 ^ (prefixWord ++ tailWord_151912).sum := by decide
  have hdescent : baseEnd_151912 < baseStart_151912 := by decide
  rcases family_descends (prefixWord ++ tailWord_151912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151931 : List Nat := [1, 1, 1, 1, 1, 8, 2, 4]
def baseStart_151931 : Nat := 118140960795 + 151931 * 2 ^ 59
def prefixEnd_151931 : Nat := 4983230072969 + 3 ^ 40 * 151931 * 2
def baseEnd_151931 : Nat := 46230298855318698052615

theorem tailTrace_151931 : CollatzResearch.WordTrace tailWord_151931 prefixEnd_151931 46230298855318698052615 := by
  unfold tailWord_151931
  simp only [CollatzResearch.WordTrace]
  refine ⟨5541378812587409594103647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3694252541724939729402431 5541378812587409594103647)
  ·
    refine ⟨8312068218881114391155471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5541378812587409594103647 8312068218881114391155471)
    ·
      refine ⟨12468102328321671586733207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8312068218881114391155471 12468102328321671586733207)
      ·
        refine ⟨18702153492482507380099811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12468102328321671586733207 18702153492482507380099811)
        ·
          refine ⟨28053230238723761070149717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18702153492482507380099811 28053230238723761070149717)
          ·
            refine ⟨328748791860044075040817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 28053230238723761070149717 328748791860044075040817)
            ·
              refine ⟨246561593895033056280613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 328748791860044075040817 246561593895033056280613)
              ·
                refine ⟨46230298855318698052615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 246561593895033056280613 46230298855318698052615)
                ·
                  rfl

theorem cell19_151931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 4].length) (baseStart_151931 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_151931 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_151931 prefixEnd_151931 := by exact prefixLift 151931
  have htrace : WordTrace (prefixWord ++ tailWord_151931) baseStart_151931 baseEnd_151931 := by
    simpa [prefixWord, tailWord_151931, baseEnd_151931] using wordTrace_append hprefix tailTrace_151931
  have hstable : (prefixWord ++ tailWord_151931).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151931).length < 2 ^ (prefixWord ++ tailWord_151931).sum := by decide
  have hdescent : baseEnd_151931 < baseStart_151931 := by decide
  rcases family_descends (prefixWord ++ tailWord_151931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151969 : List Nat := [1, 2, 3, 5, 8]
def baseStart_151969 : Nat := 118140960795 + 151969 * 2 ^ 59
def prefixEnd_151969 : Nat := 4983230072969 + 3 ^ 40 * 151969 * 2
def baseEnd_151969 : Nat := 1712661543664661822521

theorem tailTrace_151969 : CollatzResearch.WordTrace tailWord_151969 prefixEnd_151969 1712661543664661822521 := by
  unfold tailWord_151969
  simp only [CollatzResearch.WordTrace]
  refine ⟨5542764786449742083986961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3695176524299828055991307 5542764786449742083986961)
  ·
    refine ⟨4157073589837306562990221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5542764786449742083986961 4157073589837306562990221)
    ·
      refine ⟨1558902596188989961121333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4157073589837306562990221 1558902596188989961121333)
      ·
        refine ⟨146147118392717808855125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1558902596188989961121333 146147118392717808855125)
        ·
          refine ⟨1712661543664661822521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 146147118392717808855125 1712661543664661822521)
          ·
            rfl

theorem cell19_151969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 8].length) (baseStart_151969 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_151969 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_151969 prefixEnd_151969 := by exact prefixLift 151969
  have htrace : WordTrace (prefixWord ++ tailWord_151969) baseStart_151969 baseEnd_151969 := by
    simpa [prefixWord, tailWord_151969, baseEnd_151969] using wordTrace_append hprefix tailTrace_151969
  have hstable : (prefixWord ++ tailWord_151969).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151969).length < 2 ^ (prefixWord ++ tailWord_151969).sum := by decide
  have hdescent : baseEnd_151969 < baseStart_151969 := by decide
  rcases family_descends (prefixWord ++ tailWord_151969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151971 : List Nat := [1, 1, 1, 4, 1, 11]
def baseStart_151971 : Nat := 118140960795 + 151971 * 2 ^ 59
def prefixEnd_151971 : Nat := 4983230072969 + 3 ^ 40 * 151971 * 2
def baseEnd_151971 : Nat := 5138052249845606351513

theorem tailTrace_151971 : CollatzResearch.WordTrace tailWord_151971 prefixEnd_151971 5138052249845606351513 := by
  unfold tailWord_151971
  simp only [CollatzResearch.WordTrace]
  refine ⟨5542837732442496425559767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3695225154961664283706511 5542837732442496425559767)
  ·
    refine ⟨8314256598663744638339651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5542837732442496425559767 8314256598663744638339651)
    ·
      refine ⟨12471384897995616957509477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8314256598663744638339651 12471384897995616957509477)
      ·
        refine ⟨2338384668374178179533027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12471384897995616957509477 2338384668374178179533027)
        ·
          refine ⟨3507577002561267269299541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2338384668374178179533027 3507577002561267269299541)
          ·
            refine ⟨5138052249845606351513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3507577002561267269299541 5138052249845606351513)
            ·
              rfl

theorem cell19_151971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 11].length) (baseStart_151971 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_151971 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_151971 prefixEnd_151971 := by exact prefixLift 151971
  have htrace : WordTrace (prefixWord ++ tailWord_151971) baseStart_151971 baseEnd_151971 := by
    simpa [prefixWord, tailWord_151971, baseEnd_151971] using wordTrace_append hprefix tailTrace_151971
  have hstable : (prefixWord ++ tailWord_151971).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151971).length < 2 ^ (prefixWord ++ tailWord_151971).sum := by decide
  have hdescent : baseEnd_151971 < baseStart_151971 := by decide
  rcases family_descends (prefixWord ++ tailWord_151971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152009 : List Nat := [1, 2, 1, 1, 2, 1, 4, 7]
def baseStart_152009 : Nat := 118140960795 + 152009 * 2 ^ 59
def prefixEnd_152009 : Nat := 4983230072969 + 3 ^ 40 * 152009 * 2
def baseEnd_152009 : Nat := 46254033072237628319069

theorem tailTrace_152009 : CollatzResearch.WordTrace tailWord_152009 prefixEnd_152009 46254033072237628319069 := by
  unfold tailWord_152009
  simp only [CollatzResearch.WordTrace]
  refine ⟨5544223706304828915443081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3696149137536552610295387 5544223706304828915443081)
  ·
    refine ⟨4158167779728621686582311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5544223706304828915443081 4158167779728621686582311)
    ·
      refine ⟨6237251669592932529873467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4158167779728621686582311 6237251669592932529873467)
      ·
        refine ⟨9355877504389398794810201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6237251669592932529873467 9355877504389398794810201)
        ·
          refine ⟨7016908128292049096107651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9355877504389398794810201 7016908128292049096107651)
          ·
            refine ⟨10525362192438073644161477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7016908128292049096107651 10525362192438073644161477)
            ·
              refine ⟨1973505411082138808280277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10525362192438073644161477 1973505411082138808280277)
              ·
                refine ⟨46254033072237628319069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1973505411082138808280277 46254033072237628319069)
                ·
                  rfl

theorem cell19_152009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 7].length) (baseStart_152009 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_152009 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_152009 prefixEnd_152009 := by exact prefixLift 152009
  have htrace : WordTrace (prefixWord ++ tailWord_152009) baseStart_152009 baseEnd_152009 := by
    simpa [prefixWord, tailWord_152009, baseEnd_152009] using wordTrace_append hprefix tailTrace_152009
  have hstable : (prefixWord ++ tailWord_152009).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152009).length < 2 ^ (prefixWord ++ tailWord_152009).sum := by decide
  have hdescent : baseEnd_152009 < baseStart_152009 := by decide
  rcases family_descends (prefixWord ++ tailWord_152009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152047 : List Nat := [1, 1, 2, 1, 4, 1, 1, 8]
def baseStart_152047 : Nat := 118140960795 + 152047 * 2 ^ 59
def prefixEnd_152047 : Nat := 4983230072969 + 3 ^ 40 * 152047 * 2
def baseEnd_152047 : Nat := 46265595895864799474521

theorem tailTrace_152047 : CollatzResearch.WordTrace tailWord_152047 prefixEnd_152047 46265595895864799474521 := by
  unfold tailWord_152047
  simp only [CollatzResearch.WordTrace]
  refine ⟨5545609680167161405326395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3697073120111440936884263 5545609680167161405326395)
  ·
    refine ⟨8318414520250742107989593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5545609680167161405326395 8318414520250742107989593)
    ·
      refine ⟨6238810890188056580992195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8318414520250742107989593 6238810890188056580992195)
      ·
        refine ⟨9358216335282084871488293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6238810890188056580992195 9358216335282084871488293)
        ·
          refine ⟨1754665562865390913404055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9358216335282084871488293 1754665562865390913404055)
          ·
            refine ⟨2631998344298086370106083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1754665562865390913404055 2631998344298086370106083)
            ·
              refine ⟨3947997516447129555159125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2631998344298086370106083 3947997516447129555159125)
              ·
                refine ⟨46265595895864799474521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3947997516447129555159125 46265595895864799474521)
                ·
                  rfl

theorem cell19_152047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 8].length) (baseStart_152047 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_152047 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_152047 prefixEnd_152047 := by exact prefixLift 152047
  have htrace : WordTrace (prefixWord ++ tailWord_152047) baseStart_152047 baseEnd_152047 := by
    simpa [prefixWord, tailWord_152047, baseEnd_152047] using wordTrace_append hprefix tailTrace_152047
  have hstable : (prefixWord ++ tailWord_152047).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152047).length < 2 ^ (prefixWord ++ tailWord_152047).sum := by decide
  have hdescent : baseEnd_152047 < baseStart_152047 := by decide
  rcases family_descends (prefixWord ++ tailWord_152047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152176 : List Nat := [2, 1, 1, 1, 7, 1, 3, 3]
def baseStart_152176 : Nat := 118140960795 + 152176 * 2 ^ 59
def prefixEnd_152176 : Nat := 4983230072969 + 3 ^ 40 * 152176 * 2
def baseEnd_152176 : Nat := 46304848639230722607503

theorem tailTrace_152176 : CollatzResearch.WordTrace tailWord_152176 prefixEnd_152176 46304848639230722607503 := by
  unfold tailWord_152176
  simp only [CollatzResearch.WordTrace]
  refine ⟨2775157348349908218386191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3700209797799877624514921 2775157348349908218386191)
  ·
    refine ⟨4162736022524862327579287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2775157348349908218386191 4162736022524862327579287)
    ·
      refine ⟨6244104033787293491368931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4162736022524862327579287 6244104033787293491368931)
      ·
        refine ⟨9366156050680940237053397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6244104033787293491368931 9366156050680940237053397)
        ·
          refine ⟨219519282437834536805939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 9366156050680940237053397 219519282437834536805939)
          ·
            refine ⟨329278923656751805208909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219519282437834536805939 329278923656751805208909)
            ·
              refine ⟨123479596371281926953341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 329278923656751805208909 123479596371281926953341)
              ·
                refine ⟨46304848639230722607503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123479596371281926953341 46304848639230722607503)
                ·
                  rfl

theorem cell19_152176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 3].length) (baseStart_152176 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_152176 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_152176 prefixEnd_152176 := by exact prefixLift 152176
  have htrace : WordTrace (prefixWord ++ tailWord_152176) baseStart_152176 baseEnd_152176 := by
    simpa [prefixWord, tailWord_152176, baseEnd_152176] using wordTrace_append hprefix tailTrace_152176
  have hstable : (prefixWord ++ tailWord_152176).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152176).length < 2 ^ (prefixWord ++ tailWord_152176).sum := by decide
  have hdescent : baseEnd_152176 < baseStart_152176 := by decide
  rcases family_descends (prefixWord ++ tailWord_152176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152199 : List Nat := [1, 1, 4, 2, 1, 2, 8]
def baseStart_152199 : Nat := 118140960795 + 152199 * 2 ^ 59
def prefixEnd_152199 : Nat := 4983230072969 + 3 ^ 40 * 152199 * 2
def baseEnd_152199 : Nat := 15437282396791161365443

theorem tailTrace_152199 : CollatzResearch.WordTrace tailWord_152199 prefixEnd_152199 15437282396791161365443 := by
  unfold tailWord_152199
  simp only [CollatzResearch.WordTrace]
  refine ⟨5551153575616491364859651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3700769050410994243239767 5551153575616491364859651)
  ·
    refine ⟨8326730363424737047289477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5551153575616491364859651 8326730363424737047289477)
    ·
      refine ⟨1561261943142138196366777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8326730363424737047289477 1561261943142138196366777)
      ·
        refine ⟨1170946457356603647275083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1561261943142138196366777 1170946457356603647275083)
        ·
          refine ⟨1756419686034905470912625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1170946457356603647275083 1756419686034905470912625)
          ·
            refine ⟨1317314764526179103184469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1756419686034905470912625 1317314764526179103184469)
            ·
              refine ⟨15437282396791161365443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1317314764526179103184469 15437282396791161365443)
              ·
                rfl

theorem cell19_152199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 8].length) (baseStart_152199 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_152199 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_152199 prefixEnd_152199 := by exact prefixLift 152199
  have htrace : WordTrace (prefixWord ++ tailWord_152199) baseStart_152199 baseEnd_152199 := by
    simpa [prefixWord, tailWord_152199, baseEnd_152199] using wordTrace_append hprefix tailTrace_152199
  have hstable : (prefixWord ++ tailWord_152199).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152199).length < 2 ^ (prefixWord ++ tailWord_152199).sum := by decide
  have hdescent : baseEnd_152199 < baseStart_152199 := by decide
  rcases family_descends (prefixWord ++ tailWord_152199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152256 : List Nat := [2, 1, 1, 2, 4, 2, 7]
def baseStart_152256 : Nat := 118140960795 + 152256 * 2 ^ 59
def prefixEnd_152256 : Nat := 4983230072969 + 3 ^ 40 * 152256 * 2
def baseEnd_152256 : Nat := 15443063808604746943169

theorem tailTrace_152256 : CollatzResearch.WordTrace tailWord_152256 prefixEnd_152256 15443063808604746943169 := by
  unfold tailWord_152256
  simp only [CollatzResearch.WordTrace]
  refine ⟨2776616268204995049842311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3702155024273326733123081 2776616268204995049842311)
  ·
    refine ⟨4164924402307492574763467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2776616268204995049842311 4164924402307492574763467)
    ·
      refine ⟨6247386603461238862145201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4164924402307492574763467 6247386603461238862145201)
      ·
        refine ⟨4685539952595929146608901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6247386603461238862145201 4685539952595929146608901)
        ·
          refine ⟨878538741111736714989169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4685539952595929146608901 878538741111736714989169)
          ·
            refine ⟨658904055833802536241877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 878538741111736714989169 658904055833802536241877)
            ·
              refine ⟨15443063808604746943169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 658904055833802536241877 15443063808604746943169)
              ·
                rfl

theorem cell19_152256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 7].length) (baseStart_152256 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_152256 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_152256 prefixEnd_152256 := by exact prefixLift 152256
  have htrace : WordTrace (prefixWord ++ tailWord_152256) baseStart_152256 baseEnd_152256 := by
    simpa [prefixWord, tailWord_152256, baseEnd_152256] using wordTrace_append hprefix tailTrace_152256
  have hstable : (prefixWord ++ tailWord_152256).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152256).length < 2 ^ (prefixWord ++ tailWord_152256).sum := by decide
  have hdescent : baseEnd_152256 < baseStart_152256 := by decide
  rcases family_descends (prefixWord ++ tailWord_152256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152269 : List Nat := [1, 6, 2, 1, 2, 1, 2, 4]
def baseStart_152269 : Nat := 118140960795 + 152269 * 2 ^ 59
def prefixEnd_152269 : Nat := 4983230072969 + 3 ^ 40 * 152269 * 2
def baseEnd_152269 : Nat := 46333147128634062540583

theorem tailTrace_152269 : CollatzResearch.WordTrace tailWord_152269 prefixEnd_152269 46333147128634062540583 := by
  unfold tailWord_152269
  simp only [CollatzResearch.WordTrace]
  refine ⟨5553706685362893319907861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3702471123575262213271907 5553706685362893319907861)
  ·
    refine ⟨260330000876385624370681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5553706685362893319907861 260330000876385624370681)
    ·
      refine ⟨195247500657289218278011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260330000876385624370681 195247500657289218278011)
      ·
        refine ⟨292871250985933827417017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195247500657289218278011 292871250985933827417017)
        ·
          refine ⟨219653438239450370562763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292871250985933827417017 219653438239450370562763)
          ·
            refine ⟨329480157359175555844145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219653438239450370562763 329480157359175555844145)
            ·
              refine ⟨247110118019381666883109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 329480157359175555844145 247110118019381666883109)
              ·
                refine ⟨46333147128634062540583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 247110118019381666883109 46333147128634062540583)
                ·
                  rfl

theorem cell19_152269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 4].length) (baseStart_152269 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_152269 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_152269 prefixEnd_152269 := by exact prefixLift 152269
  have htrace : WordTrace (prefixWord ++ tailWord_152269) baseStart_152269 baseEnd_152269 := by
    simpa [prefixWord, tailWord_152269, baseEnd_152269] using wordTrace_append hprefix tailTrace_152269
  have hstable : (prefixWord ++ tailWord_152269).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152269).length < 2 ^ (prefixWord ++ tailWord_152269).sum := by decide
  have hdescent : baseEnd_152269 < baseStart_152269 := by decide
  rcases family_descends (prefixWord ++ tailWord_152269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152309 : List Nat := [1, 3, 6, 1, 8]
def baseStart_152309 : Nat := 118140960795 + 152309 * 2 ^ 59
def prefixEnd_152309 : Nat := 4983230072969 + 3 ^ 40 * 152309 * 2
def baseEnd_152309 : Nat := 1716493278589845246355

theorem tailTrace_152309 : CollatzResearch.WordTrace tailWord_152309 prefixEnd_152309 1716493278589845246355 := by
  unfold tailWord_152309
  simp only [CollatzResearch.WordTrace]
  refine ⟨5555165605217980151363981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3703443736811986767575987 5555165605217980151363981)
  ·
    refine ⟨2083187101956742556761493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5555165605217980151363981 2083187101956742556761493)
    ·
      refine ⟨97649395404222307348195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2083187101956742556761493 97649395404222307348195)
      ·
        refine ⟨146474093106333461022293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97649395404222307348195 146474093106333461022293)
        ·
          refine ⟨1716493278589845246355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 146474093106333461022293 1716493278589845246355)
          ·
            rfl

theorem cell19_152309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 8].length) (baseStart_152309 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_152309 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_152309 prefixEnd_152309 := by exact prefixLift 152309
  have htrace : WordTrace (prefixWord ++ tailWord_152309) baseStart_152309 baseEnd_152309 := by
    simpa [prefixWord, tailWord_152309, baseEnd_152309] using wordTrace_append hprefix tailTrace_152309
  have hstable : (prefixWord ++ tailWord_152309).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152309).length < 2 ^ (prefixWord ++ tailWord_152309).sum := by decide
  have hdescent : baseEnd_152309 < baseStart_152309 := by decide
  rcases family_descends (prefixWord ++ tailWord_152309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152370 : List Nat := [3, 2, 1, 1, 3, 1, 8]
def baseStart_152370 : Nat := 118140960795 + 152370 * 2 ^ 59
def prefixEnd_152370 : Nat := 4983230072969 + 3 ^ 40 * 152370 * 2
def baseEnd_152370 : Nat := 15454626632231918098621

theorem tailTrace_152370 : CollatzResearch.WordTrace tailWord_152370 prefixEnd_152370 15454626632231918098621 := by
  unfold tailWord_152370
  simp only [CollatzResearch.WordTrace]
  refine ⟨1389347614499246892333641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3704926971997991712889709 1389347614499246892333641)
  ·
    refine ⟨1042010710874435169250231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1389347614499246892333641 1042010710874435169250231)
    ·
      refine ⟨1563016066311652753875347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1042010710874435169250231 1563016066311652753875347)
      ·
        refine ⟨2344524099467479130813021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1563016066311652753875347 2344524099467479130813021)
        ·
          refine ⟨879196537300304674054883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2344524099467479130813021 879196537300304674054883)
          ·
            refine ⟨1318794805950457011082325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 879196537300304674054883 1318794805950457011082325)
            ·
              refine ⟨15454626632231918098621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1318794805950457011082325 15454626632231918098621)
              ·
                rfl

theorem cell19_152370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 8].length) (baseStart_152370 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_152370 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_152370 prefixEnd_152370 := by exact prefixLift 152370
  have htrace : WordTrace (prefixWord ++ tailWord_152370) baseStart_152370 baseEnd_152370 := by
    simpa [prefixWord, tailWord_152370, baseEnd_152370] using wordTrace_append hprefix tailTrace_152370
  have hstable : (prefixWord ++ tailWord_152370).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152370).length < 2 ^ (prefixWord ++ tailWord_152370).sum := by decide
  have hdescent : baseEnd_152370 < baseStart_152370 := by decide
  rcases family_descends (prefixWord ++ tailWord_152370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152503 : List Nat := [1, 1, 3, 1, 3, 1, 5, 4]
def baseStart_152503 : Nat := 118140960795 + 152503 * 2 ^ 59
def prefixEnd_152503 : Nat := 4983230072969 + 3 ^ 40 * 152503 * 2
def baseEnd_152503 : Nat := 46404349779390853339945

theorem tailTrace_152503 : CollatzResearch.WordTrace tailWord_152503 prefixEnd_152503 46404349779390853339945 := by
  unfold tailWord_152503
  simp only [CollatzResearch.WordTrace]
  refine ⟨5562241366515151283926163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3708160911010100855950775 5562241366515151283926163)
  ·
    refine ⟨8343362049772726925889245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5562241366515151283926163 8343362049772726925889245)
    ·
      refine ⟨3128760768664772597208467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8343362049772726925889245 3128760768664772597208467)
      ·
        refine ⟨4693141152997158895812701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3128760768664772597208467 4693141152997158895812701)
        ·
          refine ⟨1759927932373934585929763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4693141152997158895812701 1759927932373934585929763)
          ·
            refine ⟨2639891898560901878894645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1759927932373934585929763 2639891898560901878894645)
            ·
              refine ⟨247489865490084551146373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2639891898560901878894645 247489865490084551146373)
              ·
                refine ⟨46404349779390853339945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 247489865490084551146373 46404349779390853339945)
                ·
                  rfl

theorem cell19_152503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 4].length) (baseStart_152503 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_152503 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_152503 prefixEnd_152503 := by exact prefixLift 152503
  have htrace : WordTrace (prefixWord ++ tailWord_152503) baseStart_152503 baseEnd_152503 := by
    simpa [prefixWord, tailWord_152503, baseEnd_152503] using wordTrace_append hprefix tailTrace_152503
  have hstable : (prefixWord ++ tailWord_152503).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152503).length < 2 ^ (prefixWord ++ tailWord_152503).sum := by decide
  have hdescent : baseEnd_152503 < baseStart_152503 := by decide
  rcases family_descends (prefixWord ++ tailWord_152503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152516 : List Nat := [2, 3, 3, 3, 1, 1, 3, 3]
def baseStart_152516 : Nat := 118140960795 + 152516 * 2 ^ 59
def prefixEnd_152516 : Nat := 4983230072969 + 3 ^ 40 * 152516 * 2
def baseEnd_152516 : Nat := 46408305482210675051021

theorem tailTrace_152516 : CollatzResearch.WordTrace tailWord_152516 prefixEnd_152516 46408305482210675051021 := by
  unfold tailWord_152516
  simp only [CollatzResearch.WordTrace]
  refine ⟨2781357757734027252074701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3708477010312036336099601 2781357757734027252074701)
  ·
    refine ⟨1043009159150260219528013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2781357757734027252074701 1043009159150260219528013)
    ·
      refine ⟨391128434681347582323005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1043009159150260219528013 391128434681347582323005)
      ·
        refine ⟨146673163005505343371127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 391128434681347582323005 146673163005505343371127)
        ·
          refine ⟨220009744508258015056691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146673163005505343371127 220009744508258015056691)
          ·
            refine ⟨330014616762387022585037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220009744508258015056691 330014616762387022585037)
            ·
              refine ⟨123755481285895133469389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 330014616762387022585037 123755481285895133469389)
              ·
                refine ⟨46408305482210675051021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123755481285895133469389 46408305482210675051021)
                ·
                  rfl

theorem cell19_152516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 3].length) (baseStart_152516 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_152516 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_152516 prefixEnd_152516 := by exact prefixLift 152516
  have htrace : WordTrace (prefixWord ++ tailWord_152516) baseStart_152516 baseEnd_152516 := by
    simpa [prefixWord, tailWord_152516, baseEnd_152516] using wordTrace_append hprefix tailTrace_152516
  have hstable : (prefixWord ++ tailWord_152516).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152516).length < 2 ^ (prefixWord ++ tailWord_152516).sum := by decide
  have hdescent : baseEnd_152516 < baseStart_152516 := by decide
  rcases family_descends (prefixWord ++ tailWord_152516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152577 : List Nat := [1, 2, 4, 1, 2, 2, 4, 3]
def baseStart_152577 : Nat := 118140960795 + 152577 * 2 ^ 59
def prefixEnd_152577 : Nat := 4983230072969 + 3 ^ 40 * 152577 * 2
def baseEnd_152577 : Nat := 46426866856980607695299

theorem tailTrace_152577 : CollatzResearch.WordTrace tailWord_152577 prefixEnd_152577 46426866856980607695299 := by
  unfold tailWord_152577
  simp only [CollatzResearch.WordTrace]
  refine ⟨5564940368247061922119985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3709960245498041281413323 5564940368247061922119985)
  ·
    refine ⟨4173705276185296441589989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5564940368247061922119985 4173705276185296441589989)
    ·
      refine ⟨782569739284743082798123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4173705276185296441589989 782569739284743082798123)
      ·
        refine ⟨1173854608927114624197185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 782569739284743082798123 1173854608927114624197185)
        ·
          refine ⟨880390956695335968147889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1173854608927114624197185 880390956695335968147889)
          ·
            refine ⟨660293217521501976110917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 880390956695335968147889 660293217521501976110917)
            ·
              refine ⟨123804978285281620520797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 660293217521501976110917 123804978285281620520797)
              ·
                refine ⟨46426866856980607695299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123804978285281620520797 46426866856980607695299)
                ·
                  rfl

theorem cell19_152577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 3].length) (baseStart_152577 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_152577 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_152577 prefixEnd_152577 := by exact prefixLift 152577
  have htrace : WordTrace (prefixWord ++ tailWord_152577) baseStart_152577 baseEnd_152577 := by
    simpa [prefixWord, tailWord_152577, baseEnd_152577] using wordTrace_append hprefix tailTrace_152577
  have hstable : (prefixWord ++ tailWord_152577).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152577).length < 2 ^ (prefixWord ++ tailWord_152577).sum := by decide
  have hdescent : baseEnd_152577 < baseStart_152577 := by decide
  rcases family_descends (prefixWord ++ tailWord_152577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152615 : List Nat := [1, 1, 7, 1, 1, 1, 1, 6]
def baseStart_152615 : Nat := 118140960795 + 152615 * 2 ^ 59
def prefixEnd_152615 : Nat := 4983230072969 + 3 ^ 40 * 152615 * 2
def baseEnd_152615 : Nat := 46438429680607778850751

theorem tailTrace_152615 : CollatzResearch.WordTrace tailWord_152615 prefixEnd_152615 46438429680607778850751 := by
  unfold tailWord_152615
  simp only [CollatzResearch.WordTrace]
  refine ⟨5566326342109394412003299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3710884228072929608002199 5566326342109394412003299)
  ·
    refine ⟨8349489513164091618004949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5566326342109394412003299 8349489513164091618004949)
    ·
      refine ⟨195691160464783397296991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 8349489513164091618004949 195691160464783397296991)
      ·
        refine ⟨293536740697175095945487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195691160464783397296991 293536740697175095945487)
        ·
          refine ⟨440305111045762643918231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293536740697175095945487 440305111045762643918231)
          ·
            refine ⟨660457666568643965877347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440305111045762643918231 660457666568643965877347)
            ·
              refine ⟨990686499852965948816021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 660457666568643965877347 990686499852965948816021)
              ·
                refine ⟨46438429680607778850751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 990686499852965948816021 46438429680607778850751)
                ·
                  rfl

theorem cell19_152615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 6].length) (baseStart_152615 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_152615 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_152615 prefixEnd_152615 := by exact prefixLift 152615
  have htrace : WordTrace (prefixWord ++ tailWord_152615) baseStart_152615 baseEnd_152615 := by
    simpa [prefixWord, tailWord_152615, baseEnd_152615] using wordTrace_append hprefix tailTrace_152615
  have hstable : (prefixWord ++ tailWord_152615).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152615).length < 2 ^ (prefixWord ++ tailWord_152615).sum := by decide
  have hdescent : baseEnd_152615 < baseStart_152615 := by decide
  rcases family_descends (prefixWord ++ tailWord_152615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152636 : List Nat := [2, 2, 2, 2, 2, 2, 2, 5]
def baseStart_152636 : Nat := 118140960795 + 152636 * 2 ^ 59
def prefixEnd_152636 : Nat := 4983230072969 + 3 ^ 40 * 152636 * 2
def baseEnd_152636 : Nat := 46444819662085952384027

theorem tailTrace_152636 : CollatzResearch.WordTrace tailWord_152636 prefixEnd_152636 46444819662085952384027 := by
  unfold tailWord_152636
  simp only [CollatzResearch.WordTrace]
  refine ⟨2783546137516657499258881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3711394850022209999011841 2783546137516657499258881)
  ·
    refine ⟨2087659603137493124444161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2783546137516657499258881 2087659603137493124444161)
    ·
      refine ⟨1565744702353119843333121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2087659603137493124444161 1565744702353119843333121)
      ·
        refine ⟨1174308526764839882499841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1565744702353119843333121 1174308526764839882499841)
        ·
          refine ⟨880731395073629911874881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1174308526764839882499841 880731395073629911874881)
          ·
            refine ⟨660548546305222433906161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 880731395073629911874881 660548546305222433906161)
            ·
              refine ⟨495411409728916825429621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 660548546305222433906161 495411409728916825429621)
              ·
                refine ⟨46444819662085952384027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 495411409728916825429621 46444819662085952384027)
                ·
                  rfl

theorem cell19_152636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_152636 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_152636 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_152636 prefixEnd_152636 := by exact prefixLift 152636
  have htrace : WordTrace (prefixWord ++ tailWord_152636) baseStart_152636 baseEnd_152636 := by
    simpa [prefixWord, tailWord_152636, baseEnd_152636] using wordTrace_append hprefix tailTrace_152636
  have hstable : (prefixWord ++ tailWord_152636).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152636).length < 2 ^ (prefixWord ++ tailWord_152636).sum := by decide
  have hdescent : baseEnd_152636 < baseStart_152636 := by decide
  rcases family_descends (prefixWord ++ tailWord_152636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152746 : List Nat := [3, 1, 5, 1, 1, 1, 4, 3]
def baseStart_152746 : Nat := 118140960795 + 152746 * 2 ^ 59
def prefixEnd_152746 : Nat := 4983230072969 + 3 ^ 40 * 152746 * 2
def baseEnd_152746 : Nat := 46478290993638289939283

theorem tailTrace_152746 : CollatzResearch.WordTrace tailWord_152746 prefixEnd_152746 46478290993638289939283 := by
  unfold tailWord_152746
  simp only [CollatzResearch.WordTrace]
  refine ⟨1392776076158700946255523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3714069536423202523348061 1392776076158700946255523)
  ·
    refine ⟨2089164114238051419383285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1392776076158700946255523 2089164114238051419383285)
    ·
      refine ⟨195859135709817320567183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2089164114238051419383285 195859135709817320567183)
      ·
        refine ⟨293788703564725980850775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195859135709817320567183 293788703564725980850775)
        ·
          refine ⟨440683055347088971276163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293788703564725980850775 440683055347088971276163)
          ·
            refine ⟨661024583020633456914245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440683055347088971276163 661024583020633456914245)
            ·
              refine ⟨123942109316368773171421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 661024583020633456914245 123942109316368773171421)
              ·
                refine ⟨46478290993638289939283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123942109316368773171421 46478290993638289939283)
                ·
                  rfl

theorem cell19_152746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 3].length) (baseStart_152746 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_152746 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_152746 prefixEnd_152746 := by exact prefixLift 152746
  have htrace : WordTrace (prefixWord ++ tailWord_152746) baseStart_152746 baseEnd_152746 := by
    simpa [prefixWord, tailWord_152746, baseEnd_152746] using wordTrace_append hprefix tailTrace_152746
  have hstable : (prefixWord ++ tailWord_152746).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152746).length < 2 ^ (prefixWord ++ tailWord_152746).sum := by decide
  have hdescent : baseEnd_152746 < baseStart_152746 := by decide
  rcases family_descends (prefixWord ++ tailWord_152746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152752 : List Nat := [2, 1, 1, 1, 2, 1, 2, 9]
def baseStart_152752 : Nat := 118140960795 + 152752 * 2 ^ 59
def prefixEnd_152752 : Nat := 4983230072969 + 3 ^ 40 * 152752 * 2
def baseEnd_152752 : Nat := 46480116702632053805933

theorem tailTrace_152752 : CollatzResearch.WordTrace tailWord_152752 prefixEnd_152752 46480116702632053805933 := by
  unfold tailWord_152752
  simp only [CollatzResearch.WordTrace]
  refine ⟨2785661571306533404870255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3714215428408711206493673 2785661571306533404870255)
  ·
    refine ⟨4178492356959800107305383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2785661571306533404870255 4178492356959800107305383)
    ·
      refine ⟨6267738535439700160958075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4178492356959800107305383 6267738535439700160958075)
      ·
        refine ⟨9401607803159550241437113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6267738535439700160958075 9401607803159550241437113)
        ·
          refine ⟨7051205852369662681077835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9401607803159550241437113 7051205852369662681077835)
          ·
            refine ⟨10576808778554494021616753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7051205852369662681077835 10576808778554494021616753)
            ·
              refine ⟨7932606583915870516212565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10576808778554494021616753 7932606583915870516212565)
              ·
                refine ⟨46480116702632053805933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7932606583915870516212565 46480116702632053805933)
                ·
                  rfl

theorem cell19_152752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_152752 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_152752 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_152752 prefixEnd_152752 := by exact prefixLift 152752
  have htrace : WordTrace (prefixWord ++ tailWord_152752) baseStart_152752 baseEnd_152752 := by
    simpa [prefixWord, tailWord_152752, baseEnd_152752] using wordTrace_append hprefix tailTrace_152752
  have hstable : (prefixWord ++ tailWord_152752).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152752).length < 2 ^ (prefixWord ++ tailWord_152752).sum := by decide
  have hdescent : baseEnd_152752 < baseStart_152752 := by decide
  rcases family_descends (prefixWord ++ tailWord_152752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152820 : List Nat := [2, 6, 1, 2, 2, 6]
def baseStart_152820 : Nat := 118140960795 + 152820 * 2 ^ 59
def prefixEnd_152820 : Nat := 4983230072969 + 3 ^ 40 * 152820 * 2
def baseEnd_152820 : Nat := 5166756452358671588293

theorem tailTrace_152820 : CollatzResearch.WordTrace tailWord_152820 prefixEnd_152820 5166756452358671588293 := by
  unfold tailWord_152820
  simp only [CollatzResearch.WordTrace]
  refine ⟨2786901653183357211607957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3715868870911142948810609 2786901653183357211607957)
  ·
    refine ⟨130636014992969869294123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2786901653183357211607957 130636014992969869294123)
    ·
      refine ⟨195954022489454803941185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130636014992969869294123 195954022489454803941185)
      ·
        refine ⟨146965516867091102955889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195954022489454803941185 146965516867091102955889)
        ·
          refine ⟨110224137650318327216917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146965516867091102955889 110224137650318327216917)
          ·
            refine ⟨5166756452358671588293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 110224137650318327216917 5166756452358671588293)
            ·
              rfl

theorem cell19_152820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 6].length) (baseStart_152820 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_152820 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_152820 prefixEnd_152820 := by exact prefixLift 152820
  have htrace : WordTrace (prefixWord ++ tailWord_152820) baseStart_152820 baseEnd_152820 := by
    simpa [prefixWord, tailWord_152820, baseEnd_152820] using wordTrace_append hprefix tailTrace_152820
  have hstable : (prefixWord ++ tailWord_152820).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152820).length < 2 ^ (prefixWord ++ tailWord_152820).sum := by decide
  have hdescent : baseEnd_152820 < baseStart_152820 := by decide
  rcases family_descends (prefixWord ++ tailWord_152820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152828 : List Nat := [2, 2, 2, 1, 12]
def baseStart_152828 : Nat := 118140960795 + 152828 * 2 ^ 59
def prefixEnd_152828 : Nat := 4983230072969 + 3 ^ 40 * 152828 * 2
def baseEnd_152828 : Nat := 1722342309255051708031

theorem tailTrace_152828 : CollatzResearch.WordTrace tailWord_152828 prefixEnd_152828 1722342309255051708031 := by
  unfold tailWord_152828
  simp only [CollatzResearch.WordTrace]
  refine ⟨2787047545168865894753569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3716063393558487859671425 2787047545168865894753569)
  ·
    refine ⟨2090285658876649421065177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2787047545168865894753569 2090285658876649421065177)
    ·
      refine ⟨1567714244157487065798883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2090285658876649421065177 1567714244157487065798883)
      ·
        refine ⟨2351571366236230598698325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1567714244157487065798883 2351571366236230598698325)
        ·
          refine ⟨1722342309255051708031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 2351571366236230598698325 1722342309255051708031)
          ·
            rfl

theorem cell19_152828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 12].length) (baseStart_152828 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_152828 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_152828 prefixEnd_152828 := by exact prefixLift 152828
  have htrace : WordTrace (prefixWord ++ tailWord_152828) baseStart_152828 baseEnd_152828 := by
    simpa [prefixWord, tailWord_152828, baseEnd_152828] using wordTrace_append hprefix tailTrace_152828
  have hstable : (prefixWord ++ tailWord_152828).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152828).length < 2 ^ (prefixWord ++ tailWord_152828).sum := by decide
  have hdescent : baseEnd_152828 < baseStart_152828 := by decide
  rcases family_descends (prefixWord ++ tailWord_152828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152904 : List Nat := [2, 1, 3, 1, 1, 2, 1, 8]
def baseStart_152904 : Nat := 118140960795 + 152904 * 2 ^ 59
def prefixEnd_152904 : Nat := 4983230072969 + 3 ^ 40 * 152904 * 2
def baseEnd_152904 : Nat := 46526367997140738427741

theorem tailTrace_152904 : CollatzResearch.WordTrace tailWord_152904 prefixEnd_152904 46526367997140738427741 := by
  unfold tailWord_152904
  simp only [CollatzResearch.WordTrace]
  refine ⟨2788433519031198384636883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3717911358708264512849177 2788433519031198384636883)
  ·
    refine ⟨4182650278546797576955325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2788433519031198384636883 4182650278546797576955325)
    ·
      refine ⟨1568493854455049091358247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4182650278546797576955325 1568493854455049091358247)
      ·
        refine ⟨2352740781682573637037371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1568493854455049091358247 2352740781682573637037371)
        ·
          refine ⟨3529111172523860455556057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2352740781682573637037371 3529111172523860455556057)
          ·
            refine ⟨2646833379392895341667043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3529111172523860455556057 2646833379392895341667043)
            ·
              refine ⟨3970250069089343012500565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2646833379392895341667043 3970250069089343012500565)
              ·
                refine ⟨46526367997140738427741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3970250069089343012500565 46526367997140738427741)
                ·
                  rfl

theorem cell19_152904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_152904 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_152904 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_152904 prefixEnd_152904 := by exact prefixLift 152904
  have htrace : WordTrace (prefixWord ++ tailWord_152904) baseStart_152904 baseEnd_152904 := by
    simpa [prefixWord, tailWord_152904, baseEnd_152904] using wordTrace_append hprefix tailTrace_152904
  have hstable : (prefixWord ++ tailWord_152904).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152904).length < 2 ^ (prefixWord ++ tailWord_152904).sum := by decide
  have hdescent : baseEnd_152904 < baseStart_152904 := by decide
  rcases family_descends (prefixWord ++ tailWord_152904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152919 : List Nat := [1, 1, 3, 2, 3, 4, 2, 3]
def baseStart_152919 : Nat := 118140960795 + 152919 * 2 ^ 59
def prefixEnd_152919 : Nat := 4983230072969 + 3 ^ 40 * 152919 * 2
def baseEnd_152919 : Nat := 46530932269625148094367

theorem tailTrace_152919 : CollatzResearch.WordTrace tailWord_152919 prefixEnd_152919 46530932269625148094367 := by
  unfold tailWord_152919
  simp only [CollatzResearch.WordTrace]
  refine ⟨5577414133008054331069811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3718276088672036220713207 5577414133008054331069811)
  ·
    refine ⟨8366121199512081496604717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5577414133008054331069811 8366121199512081496604717)
    ·
      refine ⟨3137295449817030561226769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8366121199512081496604717 3137295449817030561226769)
      ·
        refine ⟨2352971587362772920920077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3137295449817030561226769 2352971587362772920920077)
        ·
          refine ⟨882364345261039845345029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2352971587362772920920077 882364345261039845345029)
          ·
            refine ⟨165443314736444971002193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 882364345261039845345029 165443314736444971002193)
            ·
              refine ⟨124082486052333728251645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165443314736444971002193 124082486052333728251645)
              ·
                refine ⟨46530932269625148094367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124082486052333728251645 46530932269625148094367)
                ·
                  rfl

theorem cell19_152919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 3].length) (baseStart_152919 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_152919 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_152919 prefixEnd_152919 := by exact prefixLift 152919
  have htrace : WordTrace (prefixWord ++ tailWord_152919) baseStart_152919 baseEnd_152919 := by
    simpa [prefixWord, tailWord_152919, baseEnd_152919] using wordTrace_append hprefix tailTrace_152919
  have hstable : (prefixWord ++ tailWord_152919).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152919).length < 2 ^ (prefixWord ++ tailWord_152919).sum := by decide
  have hdescent : baseEnd_152919 < baseStart_152919 := by decide
  rcases family_descends (prefixWord ++ tailWord_152919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152921 : List Nat := [1, 2, 1, 2, 2, 2, 6, 3]
def baseStart_152921 : Nat := 118140960795 + 152921 * 2 ^ 59
def prefixEnd_152921 : Nat := 4983230072969 + 3 ^ 40 * 152921 * 2
def baseEnd_152921 : Nat := 46531540839289736049917

theorem tailTrace_152921 : CollatzResearch.WordTrace tailWord_152921 prefixEnd_152921 46531540839289736049917 := by
  unfold tailWord_152921
  simp only [CollatzResearch.WordTrace]
  refine ⟨5577487079000808672642617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3718324719333872448428411 5577487079000808672642617)
  ·
    refine ⟨4183115309250606504481963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5577487079000808672642617 4183115309250606504481963)
    ·
      refine ⟨6274672963875909756722945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4183115309250606504481963 6274672963875909756722945)
      ·
        refine ⟨4706004722906932317542209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6274672963875909756722945 4706004722906932317542209)
        ·
          refine ⟨3529503542180199238156657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4706004722906932317542209 3529503542180199238156657)
          ·
            refine ⟨2647127656635149428617493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3529503542180199238156657 2647127656635149428617493)
            ·
              refine ⟨124084108904772629466445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2647127656635149428617493 124084108904772629466445)
              ·
                refine ⟨46531540839289736049917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124084108904772629466445 46531540839289736049917)
                ·
                  rfl

theorem cell19_152921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 3].length) (baseStart_152921 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_152921 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_152921 prefixEnd_152921 := by exact prefixLift 152921
  have htrace : WordTrace (prefixWord ++ tailWord_152921) baseStart_152921 baseEnd_152921 := by
    simpa [prefixWord, tailWord_152921, baseEnd_152921] using wordTrace_append hprefix tailTrace_152921
  have hstable : (prefixWord ++ tailWord_152921).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152921).length < 2 ^ (prefixWord ++ tailWord_152921).sum := by decide
  have hdescent : baseEnd_152921 < baseStart_152921 := by decide
  rcases family_descends (prefixWord ++ tailWord_152921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152938 : List Nat := [3, 1, 3, 3, 2, 2, 5]
def baseStart_152938 : Nat := 118140960795 + 152938 * 2 ^ 59
def prefixEnd_152938 : Nat := 4983230072969 + 3 ^ 40 * 152938 * 2
def baseEnd_152938 : Nat := 15512237893812911224031

theorem tailTrace_152938 : CollatzResearch.WordTrace tailWord_152938 prefixEnd_152938 15512237893812911224031 := by
  unfold tailWord_152938
  simp only [CollatzResearch.WordTrace]
  refine ⟨1394526779984805144002867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3718738079959480384007645 1394526779984805144002867)
  ·
    refine ⟨2091790169977207716004301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1394526779984805144002867 2091790169977207716004301)
    ·
      refine ⟨784421313741452893501613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2091790169977207716004301 784421313741452893501613)
      ·
        refine ⟨294157992653044835063105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 784421313741452893501613 294157992653044835063105)
        ·
          refine ⟨220618494489783626297329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 294157992653044835063105 220618494489783626297329)
          ·
            refine ⟨165463870867337719722997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220618494489783626297329 165463870867337719722997)
            ·
              refine ⟨15512237893812911224031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 165463870867337719722997 15512237893812911224031)
              ·
                rfl

theorem cell19_152938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 5].length) (baseStart_152938 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_152938 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_152938 prefixEnd_152938 := by exact prefixLift 152938
  have htrace : WordTrace (prefixWord ++ tailWord_152938) baseStart_152938 baseEnd_152938 := by
    simpa [prefixWord, tailWord_152938, baseEnd_152938] using wordTrace_append hprefix tailTrace_152938
  have hstable : (prefixWord ++ tailWord_152938).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152938).length < 2 ^ (prefixWord ++ tailWord_152938).sum := by decide
  have hdescent : baseEnd_152938 < baseStart_152938 := by decide
  rcases family_descends (prefixWord ++ tailWord_152938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152940 : List Nat := [2, 2, 1, 1, 5, 3, 5]
def baseStart_152940 : Nat := 118140960795 + 152940 * 2 ^ 59
def prefixEnd_152940 : Nat := 4983230072969 + 3 ^ 40 * 152940 * 2
def baseEnd_152940 : Nat := 15512440750367773875881

theorem tailTrace_152940 : CollatzResearch.WordTrace tailWord_152940 prefixEnd_152940 15512440750367773875881 := by
  unfold tailWord_152940
  simp only [CollatzResearch.WordTrace]
  refine ⟨2789090032965987458792137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3718786710621316611722849 2789090032965987458792137)
  ·
    refine ⟨2091817524724490594094103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2789090032965987458792137 2091817524724490594094103)
    ·
      refine ⟨3137726287086735891141155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2091817524724490594094103 3137726287086735891141155)
      ·
        refine ⟨4706589430630103836711733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3137726287086735891141155 4706589430630103836711733)
        ·
          refine ⟨441242759121572234691725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4706589430630103836711733 441242759121572234691725)
          ·
            refine ⟨165466034670589588009397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 441242759121572234691725 165466034670589588009397)
            ·
              refine ⟨15512440750367773875881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 165466034670589588009397 15512440750367773875881)
              ·
                rfl

theorem cell19_152940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 5].length) (baseStart_152940 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_152940 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_152940 prefixEnd_152940 := by exact prefixLift 152940
  have htrace : WordTrace (prefixWord ++ tailWord_152940) baseStart_152940 baseEnd_152940 := by
    simpa [prefixWord, tailWord_152940, baseEnd_152940] using wordTrace_append hprefix tailTrace_152940
  have hstable : (prefixWord ++ tailWord_152940).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152940).length < 2 ^ (prefixWord ++ tailWord_152940).sum := by decide
  have hdescent : baseEnd_152940 < baseStart_152940 := by decide
  rcases family_descends (prefixWord ++ tailWord_152940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153086 : List Nat := [4, 2, 2, 3, 1, 2, 2, 3]
def baseStart_153086 : Nat := 118140960795 + 153086 * 2 ^ 59
def prefixEnd_153086 : Nat := 4983230072969 + 3 ^ 40 * 153086 * 2
def baseEnd_153086 : Nat := 46581747836618242382801

theorem tailTrace_153086 : CollatzResearch.WordTrace tailWord_153086 prefixEnd_153086 46581747836618242382801 := by
  unfold tailWord_153086
  simp only [CollatzResearch.WordTrace]
  refine ⟨697938140425380231549889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3722336748935361234932741 697938140425380231549889)
  ·
    refine ⟨523453605319035173662417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 697938140425380231549889 523453605319035173662417)
    ·
      refine ⟨392590203989276380246813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 523453605319035173662417 392590203989276380246813)
      ·
        refine ⟨147221326495978642592555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 392590203989276380246813 147221326495978642592555)
        ·
          refine ⟨220831989743967963888833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147221326495978642592555 220831989743967963888833)
          ·
            refine ⟨165623992307975972916625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220831989743967963888833 165623992307975972916625)
            ·
              refine ⟨124217994230981979687469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165623992307975972916625 124217994230981979687469)
              ·
                refine ⟨46581747836618242382801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124217994230981979687469 46581747836618242382801)
                ·
                  rfl

theorem cell19_153086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_153086 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_153086 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_153086 prefixEnd_153086 := by exact prefixLift 153086
  have htrace : WordTrace (prefixWord ++ tailWord_153086) baseStart_153086 baseEnd_153086 := by
    simpa [prefixWord, tailWord_153086, baseEnd_153086] using wordTrace_append hprefix tailTrace_153086
  have hstable : (prefixWord ++ tailWord_153086).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153086).length < 2 ^ (prefixWord ++ tailWord_153086).sum := by decide
  have hdescent : baseEnd_153086 < baseStart_153086 := by decide
  rcases family_descends (prefixWord ++ tailWord_153086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153090 : List Nat := [3, 4, 1, 2, 1, 2, 1, 5]
def baseStart_153090 : Nat := 118140960795 + 153090 * 2 ^ 59
def prefixEnd_153090 : Nat := 4983230072969 + 3 ^ 40 * 153090 * 2
def baseEnd_153090 : Nat := 46582964975947418293901

theorem tailTrace_153090 : CollatzResearch.WordTrace tailWord_153090 prefixEnd_153090 46582964975947418293901 := by
  unfold tailWord_153090
  simp only [CollatzResearch.WordTrace]
  refine ⟨1395912753847137633886181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3722434010259033690363149 1395912753847137633886181)
  ·
    refine ⟨261733641346338306353659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1395912753847137633886181 261733641346338306353659)
    ·
      refine ⟨392600462019507459530489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261733641346338306353659 392600462019507459530489)
      ·
        refine ⟨294450346514630594647867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 392600462019507459530489 294450346514630594647867)
        ·
          refine ⟨441675519771945891971801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294450346514630594647867 441675519771945891971801)
          ·
            refine ⟨331256639828959418978851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 441675519771945891971801 331256639828959418978851)
            ·
              refine ⟨496884959743439128468277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 331256639828959418978851 496884959743439128468277)
              ·
                refine ⟨46582964975947418293901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 496884959743439128468277 46582964975947418293901)
                ·
                  rfl

theorem cell19_153090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_153090 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_153090 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_153090 prefixEnd_153090 := by exact prefixLift 153090
  have htrace : WordTrace (prefixWord ++ tailWord_153090) baseStart_153090 baseEnd_153090 := by
    simpa [prefixWord, tailWord_153090, baseEnd_153090] using wordTrace_append hprefix tailTrace_153090
  have hstable : (prefixWord ++ tailWord_153090).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153090).length < 2 ^ (prefixWord ++ tailWord_153090).sum := by decide
  have hdescent : baseEnd_153090 < baseStart_153090 := by decide
  rcases family_descends (prefixWord ++ tailWord_153090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153128 : List Nat := [2, 1, 5, 2, 2, 1, 2, 4]
def baseStart_153128 : Nat := 118140960795 + 153128 * 2 ^ 59
def prefixEnd_153128 : Nat := 4983230072969 + 3 ^ 40 * 153128 * 2
def baseEnd_153128 : Nat := 46594527799574589449353

theorem tailTrace_153128 : CollatzResearch.WordTrace tailWord_153128 prefixEnd_153128 46594527799574589449353 := by
  unfold tailWord_153128
  simp only [CollatzResearch.WordTrace]
  refine ⟨2792518494625441512714019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3723357992833922016952025 2792518494625441512714019)
  ·
    refine ⟨4188777741938162269071029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2792518494625441512714019 4188777741938162269071029)
    ·
      refine ⟨392697913306702712725409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4188777741938162269071029 392697913306702712725409)
      ·
        refine ⟨294523434980027034544057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 392697913306702712725409 294523434980027034544057)
        ·
          refine ⟨220892576235020275908043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 294523434980027034544057 220892576235020275908043)
          ·
            refine ⟨331338864352530413862065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220892576235020275908043 331338864352530413862065)
            ·
              refine ⟨248504148264397810396549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 331338864352530413862065 248504148264397810396549)
              ·
                refine ⟨46594527799574589449353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 248504148264397810396549 46594527799574589449353)
                ·
                  rfl

theorem cell19_153128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 4].length) (baseStart_153128 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_153128 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_153128 prefixEnd_153128 := by exact prefixLift 153128
  have htrace : WordTrace (prefixWord ++ tailWord_153128) baseStart_153128 baseEnd_153128 := by
    simpa [prefixWord, tailWord_153128, baseEnd_153128] using wordTrace_append hprefix tailTrace_153128
  have hstable : (prefixWord ++ tailWord_153128).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153128).length < 2 ^ (prefixWord ++ tailWord_153128).sum := by decide
  have hdescent : baseEnd_153128 < baseStart_153128 := by decide
  rcases family_descends (prefixWord ++ tailWord_153128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153130 : List Nat := [3, 1, 4, 1, 1, 1, 4, 4]
def baseStart_153130 : Nat := 118140960795 + 153130 * 2 ^ 59
def prefixEnd_153130 : Nat := 4983230072969 + 3 ^ 40 * 153130 * 2
def baseEnd_153130 : Nat := 46595136369239177404903

theorem tailTrace_153130 : CollatzResearch.WordTrace tailWord_153130 prefixEnd_153130 46595136369239177404903 := by
  unfold tailWord_153130
  simp only [CollatzResearch.WordTrace]
  refine ⟨1396277483810909341750211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3723406623495758244667229 1396277483810909341750211)
  ·
    refine ⟨2094416225716364012625317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1396277483810909341750211 2094416225716364012625317)
    ·
      refine ⟨392703042321818252367247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2094416225716364012625317 392703042321818252367247)
      ·
        refine ⟨589054563482727378550871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 392703042321818252367247 589054563482727378550871)
        ·
          refine ⟨883581845224091067826307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 589054563482727378550871 883581845224091067826307)
          ·
            refine ⟨1325372767836136601739461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 883581845224091067826307 1325372767836136601739461)
            ·
              refine ⟨248507393969275612826149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1325372767836136601739461 248507393969275612826149)
              ·
                refine ⟨46595136369239177404903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 248507393969275612826149 46595136369239177404903)
                ·
                  rfl

theorem cell19_153130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_153130 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_153130 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_153130 prefixEnd_153130 := by exact prefixLift 153130
  have htrace : WordTrace (prefixWord ++ tailWord_153130) baseStart_153130 baseEnd_153130 := by
    simpa [prefixWord, tailWord_153130, baseEnd_153130] using wordTrace_append hprefix tailTrace_153130
  have hstable : (prefixWord ++ tailWord_153130).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153130).length < 2 ^ (prefixWord ++ tailWord_153130).sum := by decide
  have hdescent : baseEnd_153130 < baseStart_153130 := by decide
  rcases family_descends (prefixWord ++ tailWord_153130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153151 : List Nat := [1, 1, 2, 2, 3, 3, 2, 5]
def baseStart_153151 : Nat := 118140960795 + 153151 * 2 ^ 59
def prefixEnd_153151 : Nat := 4983230072969 + 3 ^ 40 * 153151 * 2
def baseEnd_153151 : Nat := 46601526350717350938179

theorem tailTrace_153151 : CollatzResearch.WordTrace tailWord_153151 prefixEnd_153151 46601526350717350938179 := by
  unfold tailWord_153151
  simp only [CollatzResearch.WordTrace]
  refine ⟨5585875868167557953515307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3723917245445038635676871 5585875868167557953515307)
  ·
    refine ⟨8378813802251336930272961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5585875868167557953515307 8378813802251336930272961)
    ·
      refine ⟨6284110351688502697704721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8378813802251336930272961 6284110351688502697704721)
      ·
        refine ⟨4713082763766377023278541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6284110351688502697704721 4713082763766377023278541)
        ·
          refine ⟨1767406036412391383729453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4713082763766377023278541 1767406036412391383729453)
          ·
            refine ⟨662777263654646768898545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1767406036412391383729453 662777263654646768898545)
            ·
              refine ⟨497082947740985076673909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 662777263654646768898545 497082947740985076673909)
              ·
                refine ⟨46601526350717350938179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 497082947740985076673909 46601526350717350938179)
                ·
                  rfl

theorem cell19_153151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 5].length) (baseStart_153151 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_153151 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_153151 prefixEnd_153151 := by exact prefixLift 153151
  have htrace : WordTrace (prefixWord ++ tailWord_153151) baseStart_153151 baseEnd_153151 := by
    simpa [prefixWord, tailWord_153151, baseEnd_153151] using wordTrace_append hprefix tailTrace_153151
  have hstable : (prefixWord ++ tailWord_153151).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153151).length < 2 ^ (prefixWord ++ tailWord_153151).sum := by decide
  have hdescent : baseEnd_153151 < baseStart_153151 := by decide
  rcases family_descends (prefixWord ++ tailWord_153151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153170 : List Nat := [3, 2, 2, 1, 2, 9]
def baseStart_153170 : Nat := 118140960795 + 153170 * 2 ^ 59
def prefixEnd_153170 : Nat := 4983230072969 + 3 ^ 40 * 153170 * 2
def baseEnd_153170 : Nat := 5178589751392326279545

theorem tailTrace_153170 : CollatzResearch.WordTrace tailWord_153170 prefixEnd_153170 5178589751392326279545 := by
  unfold tailWord_153170
  simp only [CollatzResearch.WordTrace]
  refine ⟨1396642213774681049614241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3724379236732482798971309 1396642213774681049614241)
  ·
    refine ⟨1047481660331010787210681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1396642213774681049614241 1047481660331010787210681)
    ·
      refine ⟨785611245248258090408011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1047481660331010787210681 785611245248258090408011)
      ·
        refine ⟨1178416867872387135612017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 785611245248258090408011 1178416867872387135612017)
        ·
          refine ⟨883812650904290351709013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1178416867872387135612017 883812650904290351709013)
          ·
            refine ⟨5178589751392326279545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 883812650904290351709013 5178589751392326279545)
            ·
              rfl

theorem cell19_153170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 9].length) (baseStart_153170 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_153170 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_153170 prefixEnd_153170 := by exact prefixLift 153170
  have htrace : WordTrace (prefixWord ++ tailWord_153170) baseStart_153170 baseEnd_153170 := by
    simpa [prefixWord, tailWord_153170, baseEnd_153170] using wordTrace_append hprefix tailTrace_153170
  have hstable : (prefixWord ++ tailWord_153170).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153170).length < 2 ^ (prefixWord ++ tailWord_153170).sum := by decide
  have hdescent : baseEnd_153170 < baseStart_153170 := by decide
  rcases family_descends (prefixWord ++ tailWord_153170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153181 : List Nat := [1, 4, 4, 2, 2, 1, 1, 4]
def baseStart_153181 : Nat := 118140960795 + 153181 * 2 ^ 59
def prefixEnd_153181 : Nat := 4983230072969 + 3 ^ 40 * 153181 * 2
def baseEnd_153181 : Nat := 46610654895686170271431

theorem tailTrace_153181 : CollatzResearch.WordTrace tailWord_153181 prefixEnd_153181 46610654895686170271431 := by
  unfold tailWord_153181
  simp only [CollatzResearch.WordTrace]
  refine ⟨5586970058058873077107397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3724646705372582051404931 5586970058058873077107397)
  ·
    refine ⟨1047556885886038701957637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5586970058058873077107397 1047556885886038701957637)
    ·
      refine ⟨196416916103632256617057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1047556885886038701957637 196416916103632256617057)
      ·
        refine ⟨147312687077724192462793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196416916103632256617057 147312687077724192462793)
        ·
          refine ⟨110484515308293144347095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147312687077724192462793 110484515308293144347095)
          ·
            refine ⟨165726772962439716520643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110484515308293144347095 165726772962439716520643)
            ·
              refine ⟨248590159443659574780965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165726772962439716520643 248590159443659574780965)
              ·
                refine ⟨46610654895686170271431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 248590159443659574780965 46610654895686170271431)
                ·
                  rfl

theorem cell19_153181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 4].length) (baseStart_153181 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_153181 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_153181 prefixEnd_153181 := by exact prefixLift 153181
  have htrace : WordTrace (prefixWord ++ tailWord_153181) baseStart_153181 baseEnd_153181 := by
    simpa [prefixWord, tailWord_153181, baseEnd_153181] using wordTrace_append hprefix tailTrace_153181
  have hstable : (prefixWord ++ tailWord_153181).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153181).length < 2 ^ (prefixWord ++ tailWord_153181).sum := by decide
  have hdescent : baseEnd_153181 < baseStart_153181 := by decide
  rcases family_descends (prefixWord ++ tailWord_153181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153187 : List Nat := [1, 1, 1, 5, 1, 5, 1, 4]
def baseStart_153187 : Nat := 118140960795 + 153187 * 2 ^ 59
def prefixEnd_153187 : Nat := 4983230072969 + 3 ^ 40 * 153187 * 2
def baseEnd_153187 : Nat := 46612480604679934138081

theorem tailTrace_153187 : CollatzResearch.WordTrace tailWord_153187 prefixEnd_153187 46612480604679934138081 := by
  unfold tailWord_153187
  simp only [CollatzResearch.WordTrace]
  refine ⟨5587188896037136101825815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3724792597358090734550543 5587188896037136101825815)
  ·
    refine ⟨8380783344055704152738723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5587188896037136101825815 8380783344055704152738723)
    ·
      refine ⟨12571175016083556229108085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8380783344055704152738723 12571175016083556229108085)
      ·
        refine ⟨1178547657757833396478883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12571175016083556229108085 1178547657757833396478883)
        ·
          refine ⟨1767821486636750094718325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1178547657757833396478883 1767821486636750094718325)
          ·
            refine ⟨165733264372195321379843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1767821486636750094718325 165733264372195321379843)
            ·
              refine ⟨248599896558292982069765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165733264372195321379843 248599896558292982069765)
              ·
                refine ⟨46612480604679934138081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 248599896558292982069765 46612480604679934138081)
                ·
                  rfl

theorem cell19_153187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 4].length) (baseStart_153187 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_153187 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_153187 prefixEnd_153187 := by exact prefixLift 153187
  have htrace : WordTrace (prefixWord ++ tailWord_153187) baseStart_153187 baseEnd_153187 := by
    simpa [prefixWord, tailWord_153187, baseEnd_153187] using wordTrace_append hprefix tailTrace_153187
  have hstable : (prefixWord ++ tailWord_153187).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153187).length < 2 ^ (prefixWord ++ tailWord_153187).sum := by decide
  have hdescent : baseEnd_153187 < baseStart_153187 := by decide
  rcases family_descends (prefixWord ++ tailWord_153187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153303 : List Nat := [1, 1, 3, 2, 1, 3, 4, 4]
def baseStart_153303 : Nat := 118140960795 + 153303 * 2 ^ 59
def prefixEnd_153303 : Nat := 4983230072969 + 3 ^ 40 * 153303 * 2
def baseEnd_153303 : Nat := 46647777645226035559987

theorem tailTrace_153303 : CollatzResearch.WordTrace tailWord_153303 prefixEnd_153303 46647777645226035559987 := by
  unfold tailWord_153303
  simp only [CollatzResearch.WordTrace]
  refine ⟨5591419763616887913048563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3727613175744591942032375 5591419763616887913048563)
  ·
    refine ⟨8387129645425331869572845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5591419763616887913048563 8387129645425331869572845)
    ·
      refine ⟨3145173617034499451089817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8387129645425331869572845 3145173617034499451089817)
      ·
        refine ⟨2358880212775874588317363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3145173617034499451089817 2358880212775874588317363)
        ·
          refine ⟨3538320319163811882476045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2358880212775874588317363 3538320319163811882476045)
          ·
            refine ⟨1326870119686429455928517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3538320319163811882476045 1326870119686429455928517)
            ·
              refine ⟨248788147441205522986597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1326870119686429455928517 248788147441205522986597)
              ·
                refine ⟨46647777645226035559987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 248788147441205522986597 46647777645226035559987)
                ·
                  rfl

theorem cell19_153303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 4].length) (baseStart_153303 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_153303 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_153303 prefixEnd_153303 := by exact prefixLift 153303
  have htrace : WordTrace (prefixWord ++ tailWord_153303) baseStart_153303 baseEnd_153303 := by
    simpa [prefixWord, tailWord_153303, baseEnd_153303] using wordTrace_append hprefix tailTrace_153303
  have hstable : (prefixWord ++ tailWord_153303).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153303).length < 2 ^ (prefixWord ++ tailWord_153303).sum := by decide
  have hdescent : baseEnd_153303 < baseStart_153303 := by decide
  rcases family_descends (prefixWord ++ tailWord_153303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153322 : List Nat := [3, 1, 3, 1, 1, 1, 4, 5]
def baseStart_153322 : Nat := 118140960795 + 153322 * 2 ^ 59
def prefixEnd_153322 : Nat := 4983230072969 + 3 ^ 40 * 153322 * 2
def baseEnd_153322 : Nat := 46653559057039621137713

theorem tailTrace_153322 : CollatzResearch.WordTrace tailWord_153322 prefixEnd_153322 46653559057039621137713 := by
  unfold tailWord_153322
  simp only [CollatzResearch.WordTrace]
  refine ⟨1398028187637013539497555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3728075167032036105326813 1398028187637013539497555)
  ·
    refine ⟨2097042281455520309246333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1398028187637013539497555 2097042281455520309246333)
    ·
      refine ⟨786390855545820115967375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2097042281455520309246333 786390855545820115967375)
      ·
        refine ⟨1179586283318730173951063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 786390855545820115967375 1179586283318730173951063)
        ·
          refine ⟨1769379424978095260926595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1179586283318730173951063 1769379424978095260926595)
          ·
            refine ⟨2654069137467142891389893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1769379424978095260926595 2654069137467142891389893)
            ·
              refine ⟨497637963275089292135605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2654069137467142891389893 497637963275089292135605)
              ·
                refine ⟨46653559057039621137713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 497637963275089292135605 46653559057039621137713)
                ·
                  rfl

theorem cell19_153322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_153322 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_153322 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_153322 prefixEnd_153322 := by exact prefixLift 153322
  have htrace : WordTrace (prefixWord ++ tailWord_153322) baseStart_153322 baseEnd_153322 := by
    simpa [prefixWord, tailWord_153322, baseEnd_153322] using wordTrace_append hprefix tailTrace_153322
  have hstable : (prefixWord ++ tailWord_153322).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153322).length < 2 ^ (prefixWord ++ tailWord_153322).sum := by decide
  have hdescent : baseEnd_153322 < baseStart_153322 := by decide
  rcases family_descends (prefixWord ++ tailWord_153322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153377 : List Nat := [1, 2, 3, 2, 1, 4, 3, 3]
def baseStart_153377 : Nat := 118140960795 + 153377 * 2 ^ 59
def prefixEnd_153377 : Nat := 4983230072969 + 3 ^ 40 * 153377 * 2
def baseEnd_153377 : Nat := 46670294722815789915341

theorem tailTrace_153377 : CollatzResearch.WordTrace tailWord_153377 prefixEnd_153377 46670294722815789915341 := by
  unfold tailWord_153377
  simp only [CollatzResearch.WordTrace]
  refine ⟨5594118765348798551242385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3729412510232532367494923 5594118765348798551242385)
  ·
    refine ⟨4195589074011598913431789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5594118765348798551242385 4195589074011598913431789)
    ·
      refine ⟨1573345902754349592536921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4195589074011598913431789 1573345902754349592536921)
      ·
        refine ⟨1180009427065762194402691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1573345902754349592536921 1180009427065762194402691)
        ·
          refine ⟨1770014140598643291604037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1180009427065762194402691 1770014140598643291604037)
          ·
            refine ⟨331877651362245617175757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1770014140598643291604037 331877651362245617175757)
            ·
              refine ⟨124454119260842106440909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 331877651362245617175757 124454119260842106440909)
              ·
                refine ⟨46670294722815789915341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124454119260842106440909 46670294722815789915341)
                ·
                  rfl

theorem cell19_153377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 3].length) (baseStart_153377 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_153377 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_153377 prefixEnd_153377 := by exact prefixLift 153377
  have htrace : WordTrace (prefixWord ++ tailWord_153377) baseStart_153377 baseEnd_153377 := by
    simpa [prefixWord, tailWord_153377, baseEnd_153377] using wordTrace_append hprefix tailTrace_153377
  have hstable : (prefixWord ++ tailWord_153377).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153377).length < 2 ^ (prefixWord ++ tailWord_153377).sum := by decide
  have hdescent : baseEnd_153377 < baseStart_153377 := by decide
  rcases family_descends (prefixWord ++ tailWord_153377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153396 : List Nat := [2, 5, 1, 1, 2, 2, 6]
def baseStart_153396 : Nat := 118140960795 + 153396 * 2 ^ 59
def prefixEnd_153396 : Nat := 4983230072969 + 3 ^ 40 * 153396 * 2
def baseEnd_153396 : Nat := 15558692044876458497689

theorem tailTrace_153396 : CollatzResearch.WordTrace tailWord_153396 prefixEnd_153396 15558692044876458497689 := by
  unfold tailWord_153396
  simp only [CollatzResearch.WordTrace]
  refine ⟨2797405876139982398092021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3729874501519976530789361 2797405876139982398092021)
  ·
    refine ⟨262256800888123349821127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2797405876139982398092021 262256800888123349821127)
    ·
      refine ⟨393385201332185024731691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262256800888123349821127 393385201332185024731691)
      ·
        refine ⟨590077801998277537097537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393385201332185024731691 590077801998277537097537)
        ·
          refine ⟨442558351498708152823153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 590077801998277537097537 442558351498708152823153)
          ·
            refine ⟨331918763624031114617365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 442558351498708152823153 331918763624031114617365)
            ·
              refine ⟨15558692044876458497689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 331918763624031114617365 15558692044876458497689)
              ·
                rfl

theorem cell19_153396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 6].length) (baseStart_153396 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_153396 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_153396 prefixEnd_153396 := by exact prefixLift 153396
  have htrace : WordTrace (prefixWord ++ tailWord_153396) baseStart_153396 baseEnd_153396 := by
    simpa [prefixWord, tailWord_153396, baseEnd_153396] using wordTrace_append hprefix tailTrace_153396
  have hstable : (prefixWord ++ tailWord_153396).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153396).length < 2 ^ (prefixWord ++ tailWord_153396).sum := by decide
  have hdescent : baseEnd_153396 < baseStart_153396 := by decide
  rcases family_descends (prefixWord ++ tailWord_153396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153470 : List Nat := [4, 2, 3, 1, 1, 2, 2, 4]
def baseStart_153470 : Nat := 118140960795 + 153470 * 2 ^ 59
def prefixEnd_153470 : Nat := 4983230072969 + 3 ^ 40 * 153470 * 2
def baseEnd_153470 : Nat := 46698593212219129848421

theorem tailTrace_153470 : CollatzResearch.WordTrace tailWord_153470 prefixEnd_153470 46698593212219129848421 := by
  unfold tailWord_153470
  simp only [CollatzResearch.WordTrace]
  refine ⟨699688844251484429297233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3731673836007916956251909 699688844251484429297233)
  ·
    refine ⟨524766633188613321972925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 699688844251484429297233 524766633188613321972925)
    ·
      refine ⟨196787487445729995739847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 524766633188613321972925 196787487445729995739847)
      ·
        refine ⟨295181231168594993609771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196787487445729995739847 295181231168594993609771)
        ·
          refine ⟨442771846752892490414657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295181231168594993609771 442771846752892490414657)
          ·
            refine ⟨332078885064669367810993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 442771846752892490414657 332078885064669367810993)
            ·
              refine ⟨249059163798502025858245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 332078885064669367810993 249059163798502025858245)
              ·
                refine ⟨46698593212219129848421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 249059163798502025858245 46698593212219129848421)
                ·
                  rfl

theorem cell19_153470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_153470 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_153470 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_153470 prefixEnd_153470 := by exact prefixLift 153470
  have htrace : WordTrace (prefixWord ++ tailWord_153470) baseStart_153470 baseEnd_153470 := by
    simpa [prefixWord, tailWord_153470, baseEnd_153470] using wordTrace_append hprefix tailTrace_153470
  have hstable : (prefixWord ++ tailWord_153470).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153470).length < 2 ^ (prefixWord ++ tailWord_153470).sum := by decide
  have hdescent : baseEnd_153470 < baseStart_153470 := by decide
  rcases family_descends (prefixWord ++ tailWord_153470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153514 : List Nat := [3, 1, 15]
def baseStart_153514 : Nat := 118140960795 + 153514 * 2 ^ 59
def prefixEnd_153514 : Nat := 4983230072969 + 3 ^ 40 * 153514 * 2
def baseEnd_153514 : Nat := 192230377550782159961

theorem tailTrace_153514 : CollatzResearch.WordTrace tailWord_153514 prefixEnd_153514 192230377550782159961 := by
  unfold tailWord_153514
  simp only [CollatzResearch.WordTrace]
  refine ⟨1399778891463117737244899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3732743710568313965986397 1399778891463117737244899)
  ·
    refine ⟨2099668337194676605867349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1399778891463117737244899 2099668337194676605867349)
    ·
      refine ⟨192230377550782159961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 15 2099668337194676605867349 192230377550782159961)
      ·
        rfl

theorem cell19_153514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 15].length) (baseStart_153514 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_153514 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_153514 prefixEnd_153514 := by exact prefixLift 153514
  have htrace : WordTrace (prefixWord ++ tailWord_153514) baseStart_153514 baseEnd_153514 := by
    simpa [prefixWord, tailWord_153514, baseEnd_153514] using wordTrace_append hprefix tailTrace_153514
  have hstable : (prefixWord ++ tailWord_153514).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153514).length < 2 ^ (prefixWord ++ tailWord_153514).sum := by decide
  have hdescent : baseEnd_153514 < baseStart_153514 := by decide
  rcases family_descends (prefixWord ++ tailWord_153514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153548 : List Nat := [2, 2, 1, 4, 1, 3, 3, 3]
def baseStart_153548 : Nat := 118140960795 + 153548 * 2 ^ 59
def prefixEnd_153548 : Nat := 4983230072969 + 3 ^ 40 * 153548 * 2
def baseEnd_153548 : Nat := 46722327429138060114875

theorem tailTrace_153548 : CollatzResearch.WordTrace tailWord_153548 prefixEnd_153548 46722327429138060114875 := by
  unfold tailWord_153548
  simp only [CollatzResearch.WordTrace]
  refine ⟨2800177823864647377858649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3733570431819529837144865 2800177823864647377858649)
  ·
    refine ⟨2100133367898485533393987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2800177823864647377858649 2100133367898485533393987)
    ·
      refine ⟨3150200051847728300090981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2100133367898485533393987 3150200051847728300090981)
      ·
        refine ⟨590662509721449056267059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3150200051847728300090981 590662509721449056267059)
        ·
          refine ⟨885993764582173584400589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 590662509721449056267059 885993764582173584400589)
          ·
            refine ⟨332247661718315094150221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 885993764582173584400589 332247661718315094150221)
            ·
              refine ⟨124592873144368160306333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 332247661718315094150221 124592873144368160306333)
              ·
                refine ⟨46722327429138060114875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124592873144368160306333 46722327429138060114875)
                ·
                  rfl

theorem cell19_153548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 3].length) (baseStart_153548 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_153548 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_153548 prefixEnd_153548 := by exact prefixLift 153548
  have htrace : WordTrace (prefixWord ++ tailWord_153548) baseStart_153548 baseEnd_153548 := by
    simpa [prefixWord, tailWord_153548, baseEnd_153548] using wordTrace_append hprefix tailTrace_153548
  have hstable : (prefixWord ++ tailWord_153548).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153548).length < 2 ^ (prefixWord ++ tailWord_153548).sum := by decide
  have hdescent : baseEnd_153548 < baseStart_153548 := by decide
  rcases family_descends (prefixWord ++ tailWord_153548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153552 : List Nat := [2, 1, 1, 1, 1, 2, 4, 7]
def baseStart_153552 : Nat := 118140960795 + 153552 * 2 ^ 59
def prefixEnd_153552 : Nat := 4983230072969 + 3 ^ 40 * 153552 * 2
def baseEnd_153552 : Nat := 46723544568467236025975

theorem tailTrace_153552 : CollatzResearch.WordTrace tailWord_153552 prefixEnd_153552 46723544568467236025975 := by
  unfold tailWord_153552
  simp only [CollatzResearch.WordTrace]
  refine ⟨2800250769857401719431455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3733667693143202292575273 2800250769857401719431455)
  ·
    refine ⟨4200376154786102579147183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2800250769857401719431455 4200376154786102579147183)
    ·
      refine ⟨6300564232179153868720775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4200376154786102579147183 6300564232179153868720775)
      ·
        refine ⟨9450846348268730803081163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6300564232179153868720775 9450846348268730803081163)
        ·
          refine ⟨14176269522403096204621745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9450846348268730803081163 14176269522403096204621745)
          ·
            refine ⟨10632202141802322153466309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14176269522403096204621745 10632202141802322153466309)
            ·
              refine ⟨1993537901587935403774933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10632202141802322153466309 1993537901587935403774933)
              ·
                refine ⟨46723544568467236025975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1993537901587935403774933 46723544568467236025975)
                ·
                  rfl

theorem cell19_153552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_153552 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_153552 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_153552 prefixEnd_153552 := by exact prefixLift 153552
  have htrace : WordTrace (prefixWord ++ tailWord_153552) baseStart_153552 baseEnd_153552 := by
    simpa [prefixWord, tailWord_153552, baseEnd_153552] using wordTrace_append hprefix tailTrace_153552
  have hstable : (prefixWord ++ tailWord_153552).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153552).length < 2 ^ (prefixWord ++ tailWord_153552).sum := by decide
  have hdescent : baseEnd_153552 < baseStart_153552 := by decide
  rcases family_descends (prefixWord ++ tailWord_153552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153605 : List Nat := [1, 3, 1, 1, 2, 6, 2, 3]
def baseStart_153605 : Nat := 118140960795 + 153605 * 2 ^ 59
def prefixEnd_153605 : Nat := 4983230072969 + 3 ^ 40 * 153605 * 2
def baseEnd_153605 : Nat := 46739671664578816848053

theorem tailTrace_153605 : CollatzResearch.WordTrace tailWord_153605 prefixEnd_153605 46739671664578816848053 := by
  unfold tailWord_153605
  simp only [CollatzResearch.WordTrace]
  refine ⟨5602434608522793490542269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3734956405681862327028179 5602434608522793490542269)
  ·
    refine ⟨2100912978196047558953351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5602434608522793490542269 2100912978196047558953351)
    ·
      refine ⟨3151369467294071338430027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2100912978196047558953351 3151369467294071338430027)
      ·
        refine ⟨4727054200941107007645041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3151369467294071338430027 4727054200941107007645041)
        ·
          refine ⟨3545290650705830255733781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4727054200941107007645041 3545290650705830255733781)
          ·
            refine ⟨166185499251835793237521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3545290650705830255733781 166185499251835793237521)
            ·
              refine ⟨124639124438876844928141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166185499251835793237521 124639124438876844928141)
              ·
                refine ⟨46739671664578816848053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124639124438876844928141 46739671664578816848053)
                ·
                  rfl

theorem cell19_153605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 3].length) (baseStart_153605 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_153605 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_153605 prefixEnd_153605 := by exact prefixLift 153605
  have htrace : WordTrace (prefixWord ++ tailWord_153605) baseStart_153605 baseEnd_153605 := by
    simpa [prefixWord, tailWord_153605, baseEnd_153605] using wordTrace_append hprefix tailTrace_153605
  have hstable : (prefixWord ++ tailWord_153605).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153605).length < 2 ^ (prefixWord ++ tailWord_153605).sum := by decide
  have hdescent : baseEnd_153605 < baseStart_153605 := by decide
  rcases family_descends (prefixWord ++ tailWord_153605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153607 : List Nat := [1, 1, 4, 3, 1, 3, 1, 5]
def baseStart_153607 : Nat := 118140960795 + 153607 * 2 ^ 59
def prefixEnd_153607 : Nat := 4983230072969 + 3 ^ 40 * 153607 * 2
def baseEnd_153607 : Nat := 46740280234243404803603

theorem tailTrace_153607 : CollatzResearch.WordTrace tailWord_153607 prefixEnd_153607 46740280234243404803603 := by
  unfold tailWord_153607
  simp only [CollatzResearch.WordTrace]
  refine ⟨5602507554515547832115075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3735005036343698554743383 5602507554515547832115075)
  ·
    refine ⟨8403761331773321748172613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5602507554515547832115075 8403761331773321748172613)
    ·
      refine ⟨1575705249707497827782365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8403761331773321748172613 1575705249707497827782365)
      ·
        refine ⟨590889468640311685418387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1575705249707497827782365 590889468640311685418387)
        ·
          refine ⟨886334202960467528127581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 590889468640311685418387 886334202960467528127581)
          ·
            refine ⟨332375326110175323047843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 886334202960467528127581 332375326110175323047843)
            ·
              refine ⟨498562989165262984571765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332375326110175323047843 498562989165262984571765)
              ·
                refine ⟨46740280234243404803603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 498562989165262984571765 46740280234243404803603)
                ·
                  rfl

theorem cell19_153607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 5].length) (baseStart_153607 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_153607 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_153607 prefixEnd_153607 := by exact prefixLift 153607
  have htrace : WordTrace (prefixWord ++ tailWord_153607) baseStart_153607 baseEnd_153607 := by
    simpa [prefixWord, tailWord_153607, baseEnd_153607] using wordTrace_append hprefix tailTrace_153607
  have hstable : (prefixWord ++ tailWord_153607).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153607).length < 2 ^ (prefixWord ++ tailWord_153607).sum := by decide
  have hdescent : baseEnd_153607 < baseStart_153607 := by decide
  rcases family_descends (prefixWord ++ tailWord_153607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153620 : List Nat := [2, 4, 3, 2, 2, 1, 5]
def baseStart_153620 : Nat := 118140960795 + 153620 * 2 ^ 59
def prefixEnd_153620 : Nat := 4983230072969 + 3 ^ 40 * 153620 * 2
def baseEnd_153620 : Nat := 15581411979021075504893

theorem tailTrace_153620 : CollatzResearch.WordTrace tailWord_153620 prefixEnd_153620 15581411979021075504893 := by
  unfold tailWord_153620
  simp only [CollatzResearch.WordTrace]
  refine ⟨2801490851734225526169157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3735321135645634034892209 2801490851734225526169157)
  ·
    refine ⟨525279534700167286156717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2801490851734225526169157 525279534700167286156717)
    ·
      refine ⟨196979825512562732308769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 525279534700167286156717 196979825512562732308769)
      ·
        refine ⟨147734869134422049231577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196979825512562732308769 147734869134422049231577)
        ·
          refine ⟨110801151850816536923683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147734869134422049231577 110801151850816536923683)
          ·
            refine ⟨166201727776224805385525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110801151850816536923683 166201727776224805385525)
            ·
              refine ⟨15581411979021075504893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 166201727776224805385525 15581411979021075504893)
              ·
                rfl

theorem cell19_153620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 5].length) (baseStart_153620 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_153620 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_153620 prefixEnd_153620 := by exact prefixLift 153620
  have htrace : WordTrace (prefixWord ++ tailWord_153620) baseStart_153620 baseEnd_153620 := by
    simpa [prefixWord, tailWord_153620, baseEnd_153620] using wordTrace_append hprefix tailTrace_153620
  have hstable : (prefixWord ++ tailWord_153620).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153620).length < 2 ^ (prefixWord ++ tailWord_153620).sum := by decide
  have hdescent : baseEnd_153620 < baseStart_153620 := by decide
  rcases family_descends (prefixWord ++ tailWord_153620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153626 : List Nat := [3, 1, 1, 3, 1, 5, 5]
def baseStart_153626 : Nat := 118140960795 + 153626 * 2 ^ 59
def prefixEnd_153626 : Nat := 4983230072969 + 3 ^ 40 * 153626 * 2
def baseEnd_153626 : Nat := 15582020548685663460443

theorem tailTrace_153626 : CollatzResearch.WordTrace tailWord_153626 prefixEnd_153626 15582020548685663460443 := by
  unfold tailWord_153626
  simp only [CollatzResearch.WordTrace]
  refine ⟨1400800135361678519264183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3735467027631142718037821 1400800135361678519264183)
  ·
    refine ⟨2101200203042517778896275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1400800135361678519264183 2101200203042517778896275)
    ·
      refine ⟨3151800304563776668344413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2101200203042517778896275 3151800304563776668344413)
      ·
        refine ⟨1181925114211416250629155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3151800304563776668344413 1181925114211416250629155)
        ·
          refine ⟨1772887671317124375943733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1181925114211416250629155 1772887671317124375943733)
          ·
            refine ⟨166208219185980410244725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1772887671317124375943733 166208219185980410244725)
            ·
              refine ⟨15582020548685663460443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 166208219185980410244725 15582020548685663460443)
              ·
                rfl

theorem cell19_153626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 5].length) (baseStart_153626 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_153626 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_153626 prefixEnd_153626 := by exact prefixLift 153626
  have htrace : WordTrace (prefixWord ++ tailWord_153626) baseStart_153626 baseEnd_153626 := by
    simpa [prefixWord, tailWord_153626, baseEnd_153626] using wordTrace_append hprefix tailTrace_153626
  have hstable : (prefixWord ++ tailWord_153626).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153626).length < 2 ^ (prefixWord ++ tailWord_153626).sum := by decide
  have hdescent : baseEnd_153626 < baseStart_153626 := by decide
  rcases family_descends (prefixWord ++ tailWord_153626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153685 : List Nat := [1, 3, 2, 2, 1, 10]
def baseStart_153685 : Nat := 118140960795 + 153685 * 2 ^ 59
def prefixEnd_153685 : Nat := 4983230072969 + 3 ^ 40 * 153685 * 2
def baseEnd_153685 : Nat := 5196001605684703896673

theorem tailTrace_153685 : CollatzResearch.WordTrace tailWord_153685 prefixEnd_153685 5196001605684703896673 := by
  unfold tailWord_153685
  simp only [CollatzResearch.WordTrace]
  refine ⟨5605352448232967153454509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3736901632155311435636339 5605352448232967153454509)
  ·
    refine ⟨2102007168087362682545441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5605352448232967153454509 2102007168087362682545441)
    ·
      refine ⟨1576505376065522011909081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2102007168087362682545441 1576505376065522011909081)
      ·
        refine ⟨1182379032049141508931811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1576505376065522011909081 1182379032049141508931811)
        ·
          refine ⟨1773568548073712263397717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1182379032049141508931811 1773568548073712263397717)
          ·
            refine ⟨5196001605684703896673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1773568548073712263397717 5196001605684703896673)
            ·
              rfl

theorem cell19_153685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 10].length) (baseStart_153685 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_153685 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_153685 prefixEnd_153685 := by exact prefixLift 153685
  have htrace : WordTrace (prefixWord ++ tailWord_153685) baseStart_153685 baseEnd_153685 := by
    simpa [prefixWord, tailWord_153685, baseEnd_153685] using wordTrace_append hprefix tailTrace_153685
  have hstable : (prefixWord ++ tailWord_153685).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153685).length < 2 ^ (prefixWord ++ tailWord_153685).sum := by decide
  have hdescent : baseEnd_153685 < baseStart_153685 := by decide
  rcases family_descends (prefixWord ++ tailWord_153685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153694 : List Nat := [4, 4, 1, 1, 3, 1, 1, 4]
def baseStart_153694 : Nat := 118140960795 + 153694 * 2 ^ 59
def prefixEnd_153694 : Nat := 4983230072969 + 3 ^ 40 * 153694 * 2
def baseEnd_153694 : Nat := 46766753014652980870033

theorem tailTrace_153694 : CollatzResearch.WordTrace tailWord_153694 prefixEnd_153694 46766753014652980870033 := by
  unfold tailWord_153694
  simp only [CollatzResearch.WordTrace]
  refine ⟨700710088150045211316517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3737120470133574460354757 700710088150045211316517)
  ·
    refine ⟨131383141528133477121847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 700710088150045211316517 131383141528133477121847)
    ·
      refine ⟨197074712292200215682771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131383141528133477121847 197074712292200215682771)
      ·
        refine ⟨295612068438300323524157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197074712292200215682771 295612068438300323524157)
        ·
          refine ⟨110854525664362621321559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 295612068438300323524157 110854525664362621321559)
          ·
            refine ⟨166281788496543931982339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110854525664362621321559 166281788496543931982339)
            ·
              refine ⟨249422682744815897973509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166281788496543931982339 249422682744815897973509)
              ·
                refine ⟨46766753014652980870033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 249422682744815897973509 46766753014652980870033)
                ·
                  rfl

theorem cell19_153694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_153694 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_153694 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_153694 prefixEnd_153694 := by exact prefixLift 153694
  have htrace : WordTrace (prefixWord ++ tailWord_153694) baseStart_153694 baseEnd_153694 := by
    simpa [prefixWord, tailWord_153694, baseEnd_153694] using wordTrace_append hprefix tailTrace_153694
  have hstable : (prefixWord ++ tailWord_153694).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153694).length < 2 ^ (prefixWord ++ tailWord_153694).sum := by decide
  have hdescent : baseEnd_153694 < baseStart_153694 := by decide
  rcases family_descends (prefixWord ++ tailWord_153694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153698 : List Nat := [3, 3, 2, 2, 2, 2, 1, 4]
def baseStart_153698 : Nat := 118140960795 + 153698 * 2 ^ 59
def prefixEnd_153698 : Nat := 4983230072969 + 3 ^ 40 * 153698 * 2
def baseEnd_153698 : Nat := 46767970153982156781133

theorem tailTrace_153698 : CollatzResearch.WordTrace tailWord_153698 prefixEnd_153698 46767970153982156781133 := by
  unfold tailWord_153698
  simp only [CollatzResearch.WordTrace]
  refine ⟨1401456649296467593419437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3737217731457246915785165 1401456649296467593419437)
  ·
    refine ⟨525546243486175347532289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1401456649296467593419437 525546243486175347532289)
    ·
      refine ⟨394159682614631510649217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 525546243486175347532289 394159682614631510649217)
      ·
        refine ⟨295619761960973632986913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 394159682614631510649217 295619761960973632986913)
        ·
          refine ⟨221714821470730224740185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295619761960973632986913 221714821470730224740185)
          ·
            refine ⟨166286116103047668555139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221714821470730224740185 166286116103047668555139)
            ·
              refine ⟨249429174154571502832709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166286116103047668555139 249429174154571502832709)
              ·
                refine ⟨46767970153982156781133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 249429174154571502832709 46767970153982156781133)
                ·
                  rfl

theorem cell19_153698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_153698 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_153698 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_153698 prefixEnd_153698 := by exact prefixLift 153698
  have htrace : WordTrace (prefixWord ++ tailWord_153698) baseStart_153698 baseEnd_153698 := by
    simpa [prefixWord, tailWord_153698, baseEnd_153698] using wordTrace_append hprefix tailTrace_153698
  have hstable : (prefixWord ++ tailWord_153698).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153698).length < 2 ^ (prefixWord ++ tailWord_153698).sum := by decide
  have hdescent : baseEnd_153698 < baseStart_153698 := by decide
  rcases family_descends (prefixWord ++ tailWord_153698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153774 : List Nat := [4, 1, 4, 2, 1, 1, 1, 5]
def baseStart_153774 : Nat := 118140960795 + 153774 * 2 ^ 59
def prefixEnd_153774 : Nat := 4983230072969 + 3 ^ 40 * 153774 * 2
def baseEnd_153774 : Nat := 46791095801236499092037

theorem tailTrace_153774 : CollatzResearch.WordTrace tailWord_153774 prefixEnd_153774 46791095801236499092037 := by
  unfold tailWord_153774
  simp only [CollatzResearch.WordTrace]
  refine ⟨701074818113816919180547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3739065696607023568962917 701074818113816919180547)
  ·
    refine ⟨1051612227170725378770821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 701074818113816919180547 1051612227170725378770821)
    ·
      refine ⟨197177292594511008519529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1051612227170725378770821 197177292594511008519529)
      ·
        refine ⟨147882969445883256389647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197177292594511008519529 147882969445883256389647)
        ·
          refine ⟨221824454168824884584471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147882969445883256389647 221824454168824884584471)
          ·
            refine ⟨332736681253237326876707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221824454168824884584471 332736681253237326876707)
            ·
              refine ⟨499105021879855990315061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332736681253237326876707 499105021879855990315061)
              ·
                refine ⟨46791095801236499092037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 499105021879855990315061 46791095801236499092037)
                ·
                  rfl

theorem cell19_153774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_153774 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_153774 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_153774 prefixEnd_153774 := by exact prefixLift 153774
  have htrace : WordTrace (prefixWord ++ tailWord_153774) baseStart_153774 baseEnd_153774 := by
    simpa [prefixWord, tailWord_153774, baseEnd_153774] using wordTrace_append hprefix tailTrace_153774
  have hstable : (prefixWord ++ tailWord_153774).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153774).length < 2 ^ (prefixWord ++ tailWord_153774).sum := by decide
  have hdescent : baseEnd_153774 < baseStart_153774 := by decide
  rcases family_descends (prefixWord ++ tailWord_153774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153793 : List Nat := [1, 2, 6, 1, 3, 1, 5]
def baseStart_153793 : Nat := 118140960795 + 153793 * 2 ^ 59
def prefixEnd_153793 : Nat := 4983230072969 + 3 ^ 40 * 153793 * 2
def baseEnd_153793 : Nat := 15598959071016694889921

theorem tailTrace_153793 : CollatzResearch.WordTrace tailWord_153793 prefixEnd_153793 15598959071016694889921 := by
  unfold tailWord_153793
  simp only [CollatzResearch.WordTrace]
  refine ⟨5609291531841701598386033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3739527687894467732257355 5609291531841701598386033)
  ·
    refine ⟨4206968648881276198789525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5609291531841701598386033 4206968648881276198789525)
    ·
      refine ⟨197201655416309821818259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4206968648881276198789525 197201655416309821818259)
      ·
        refine ⟨295802483124464732727389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197201655416309821818259 295802483124464732727389)
        ·
          refine ⟨110925931171674274772771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 295802483124464732727389 110925931171674274772771)
          ·
            refine ⟨166388896757511412159157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110925931171674274772771 166388896757511412159157)
            ·
              refine ⟨15598959071016694889921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 166388896757511412159157 15598959071016694889921)
              ·
                rfl

theorem cell19_153793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 5].length) (baseStart_153793 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_153793 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_153793 prefixEnd_153793 := by exact prefixLift 153793
  have htrace : WordTrace (prefixWord ++ tailWord_153793) baseStart_153793 baseEnd_153793 := by
    simpa [prefixWord, tailWord_153793, baseEnd_153793] using wordTrace_append hprefix tailTrace_153793
  have hstable : (prefixWord ++ tailWord_153793).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153793).length < 2 ^ (prefixWord ++ tailWord_153793).sum := by decide
  have hdescent : baseEnd_153793 < baseStart_153793 := by decide
  rcases family_descends (prefixWord ++ tailWord_153793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153814 : List Nat := [5, 2, 1, 2, 1, 1, 1, 6]
def baseStart_153814 : Nat := 118140960795 + 153814 * 2 ^ 59
def prefixEnd_153814 : Nat := 4983230072969 + 3 ^ 40 * 153814 * 2
def baseEnd_153814 : Nat := 46803267194528258203039

theorem tailTrace_153814 : CollatzResearch.WordTrace tailWord_153814 prefixEnd_153814 46803267194528258203039 := by
  unfold tailWord_153814
  simp only [CollatzResearch.WordTrace]
  refine ⟨350628591547851386556281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3740038309843748123266997 350628591547851386556281)
  ·
    refine ⟨262971443660888539917211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 350628591547851386556281 262971443660888539917211)
    ·
      refine ⟨394457165491332809875817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262971443660888539917211 394457165491332809875817)
      ·
        refine ⟨295842874118499607406863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 394457165491332809875817 295842874118499607406863)
        ·
          refine ⟨443764311177749411110295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295842874118499607406863 443764311177749411110295)
          ·
            refine ⟨665646466766624116665443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 443764311177749411110295 665646466766624116665443)
            ·
              refine ⟨998469700149936174998165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 665646466766624116665443 998469700149936174998165)
              ·
                refine ⟨46803267194528258203039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 998469700149936174998165 46803267194528258203039)
                ·
                  rfl

theorem cell19_153814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_153814 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_153814 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_153814 prefixEnd_153814 := by exact prefixLift 153814
  have htrace : WordTrace (prefixWord ++ tailWord_153814) baseStart_153814 baseEnd_153814 := by
    simpa [prefixWord, tailWord_153814, baseEnd_153814] using wordTrace_append hprefix tailTrace_153814
  have hstable : (prefixWord ++ tailWord_153814).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153814).length < 2 ^ (prefixWord ++ tailWord_153814).sum := by decide
  have hdescent : baseEnd_153814 < baseStart_153814 := by decide
  rcases family_descends (prefixWord ++ tailWord_153814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153816 : List Nat := [2, 1, 2, 2, 4, 2, 2, 4]
def baseStart_153816 : Nat := 118140960795 + 153816 * 2 ^ 59
def prefixEnd_153816 : Nat := 4983230072969 + 3 ^ 40 * 153816 * 2
def baseEnd_153816 : Nat := 46803875764192846158589

theorem tailTrace_153816 : CollatzResearch.WordTrace tailWord_153816 prefixEnd_153816 46803875764192846158589 := by
  unfold tailWord_153816
  simp only [CollatzResearch.WordTrace]
  refine ⟨2805065205379188263236651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3740086940505584350982201 2805065205379188263236651)
  ·
    refine ⟨4207597808068782394854977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2805065205379188263236651 4207597808068782394854977)
    ·
      refine ⟨3155698356051586796141233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4207597808068782394854977 3155698356051586796141233)
      ·
        refine ⟨2366773767038690097105925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3155698356051586796141233 2366773767038690097105925)
        ·
          refine ⟨443770081319754393207361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2366773767038690097105925 443770081319754393207361)
          ·
            refine ⟨332827560989815794905521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 443770081319754393207361 332827560989815794905521)
            ·
              refine ⟨249620670742361846179141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 332827560989815794905521 249620670742361846179141)
              ·
                refine ⟨46803875764192846158589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 249620670742361846179141 46803875764192846158589)
                ·
                  rfl

theorem cell19_153816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 4].length) (baseStart_153816 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_153816 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_153816 prefixEnd_153816 := by exact prefixLift 153816
  have htrace : WordTrace (prefixWord ++ tailWord_153816) baseStart_153816 baseEnd_153816 := by
    simpa [prefixWord, tailWord_153816, baseEnd_153816] using wordTrace_append hprefix tailTrace_153816
  have hstable : (prefixWord ++ tailWord_153816).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153816).length < 2 ^ (prefixWord ++ tailWord_153816).sum := by decide
  have hdescent : baseEnd_153816 < baseStart_153816 := by decide
  rcases family_descends (prefixWord ++ tailWord_153816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153818 : List Nat := [3, 1, 1, 2, 2, 1, 3, 6]
def baseStart_153818 : Nat := 118140960795 + 153818 * 2 ^ 59
def prefixEnd_153818 : Nat := 4983230072969 + 3 ^ 40 * 153818 * 2
def baseEnd_153818 : Nat := 46804484333857434114139

theorem tailTrace_153818 : CollatzResearch.WordTrace tailWord_153818 prefixEnd_153818 46804484333857434114139 := by
  unfold tailWord_153818
  simp only [CollatzResearch.WordTrace]
  refine ⟨1402550839187782717011527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3740135571167420578697405 1402550839187782717011527)
  ·
    refine ⟨2103826258781674075517291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1402550839187782717011527 2103826258781674075517291)
    ·
      refine ⟨3155739388172511113275937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2103826258781674075517291 3155739388172511113275937)
      ·
        refine ⟨2366804541129383334956953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3155739388172511113275937 2366804541129383334956953)
        ·
          refine ⟨1775103405847037501217715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2366804541129383334956953 1775103405847037501217715)
          ·
            refine ⟨2662655108770556251826573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1775103405847037501217715 2662655108770556251826573)
            ·
              refine ⟨998495665788958594434965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2662655108770556251826573 998495665788958594434965)
              ·
                refine ⟨46804484333857434114139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 998495665788958594434965 46804484333857434114139)
                ·
                  rfl

theorem cell19_153818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_153818 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_153818 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_153818 prefixEnd_153818 := by exact prefixLift 153818
  have htrace : WordTrace (prefixWord ++ tailWord_153818) baseStart_153818 baseEnd_153818 := by
    simpa [prefixWord, tailWord_153818, baseEnd_153818] using wordTrace_append hprefix tailTrace_153818
  have hstable : (prefixWord ++ tailWord_153818).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153818).length < 2 ^ (prefixWord ++ tailWord_153818).sum := by decide
  have hdescent : baseEnd_153818 < baseStart_153818 := by decide
  rcases family_descends (prefixWord ++ tailWord_153818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153873 : List Nat := [1, 2, 2, 1, 1, 7, 1, 4]
def baseStart_153873 : Nat := 118140960795 + 153873 * 2 ^ 59
def prefixEnd_153873 : Nat := 4983230072969 + 3 ^ 40 * 153873 * 2
def baseEnd_153873 : Nat := 46821219999633602891767

theorem tailTrace_153873 : CollatzResearch.WordTrace tailWord_153873 prefixEnd_153873 46821219999633602891767 := by
  unfold tailWord_153873
  simp only [CollatzResearch.WordTrace]
  refine ⟨5612209371551875261298273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3741472914367916840865515 5612209371551875261298273)
  ·
    refine ⟨4209157028663906445973705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5612209371551875261298273 4209157028663906445973705)
    ·
      refine ⟨3156867771497929834480279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4209157028663906445973705 3156867771497929834480279)
      ·
        refine ⟨4735301657246894751720419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3156867771497929834480279 4735301657246894751720419)
        ·
          refine ⟨7102952485870342127580629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4735301657246894751720419 7102952485870342127580629)
          ·
            refine ⟨166475448887586143615171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 7102952485870342127580629 166475448887586143615171)
            ·
              refine ⟨249713173331379215422757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166475448887586143615171 249713173331379215422757)
              ·
                refine ⟨46821219999633602891767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 249713173331379215422757 46821219999633602891767)
                ·
                  rfl

theorem cell19_153873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 4].length) (baseStart_153873 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_153873 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_153873 prefixEnd_153873 := by exact prefixLift 153873
  have htrace : WordTrace (prefixWord ++ tailWord_153873) baseStart_153873 baseEnd_153873 := by
    simpa [prefixWord, tailWord_153873, baseEnd_153873] using wordTrace_append hprefix tailTrace_153873
  have hstable : (prefixWord ++ tailWord_153873).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153873).length < 2 ^ (prefixWord ++ tailWord_153873).sum := by decide
  have hdescent : baseEnd_153873 < baseStart_153873 := by decide
  rcases family_descends (prefixWord ++ tailWord_153873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153890 : List Nat := [3, 3, 1, 1, 3, 2, 3, 3]
def baseStart_153890 : Nat := 118140960795 + 153890 * 2 ^ 59
def prefixEnd_153890 : Nat := 4983230072969 + 3 ^ 40 * 153890 * 2
def baseEnd_153890 : Nat := 46826392841782600513943

theorem tailTrace_153890 : CollatzResearch.WordTrace tailWord_153890 prefixEnd_153890 46826392841782600513943 := by
  unfold tailWord_153890
  simp only [CollatzResearch.WordTrace]
  refine ⟨1403207353122571791166781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3741886274993524776444749 1403207353122571791166781)
  ·
    refine ⟨526202757420964421687543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1403207353122571791166781 526202757420964421687543)
    ·
      refine ⟨789304136131446632531315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 526202757420964421687543 789304136131446632531315)
      ·
        refine ⟨1183956204197169948796973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 789304136131446632531315 1183956204197169948796973)
        ·
          refine ⟨443983576573938730798865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1183956204197169948796973 443983576573938730798865)
          ·
            refine ⟨332987682430454048099149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 443983576573938730798865 332987682430454048099149)
            ·
              refine ⟨124870380911420268037181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 332987682430454048099149 124870380911420268037181)
              ·
                refine ⟨46826392841782600513943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124870380911420268037181 46826392841782600513943)
                ·
                  rfl

theorem cell19_153890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 3].length) (baseStart_153890 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_153890 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_153890 prefixEnd_153890 := by exact prefixLift 153890
  have htrace : WordTrace (prefixWord ++ tailWord_153890) baseStart_153890 baseEnd_153890 := by
    simpa [prefixWord, tailWord_153890, baseEnd_153890] using wordTrace_append hprefix tailTrace_153890
  have hstable : (prefixWord ++ tailWord_153890).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153890).length < 2 ^ (prefixWord ++ tailWord_153890).sum := by decide
  have hdescent : baseEnd_153890 < baseStart_153890 := by decide
  rcases family_descends (prefixWord ++ tailWord_153890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153932 : List Nat := [2, 2, 1, 3, 2, 1, 2, 6]
def baseStart_153932 : Nat := 118140960795 + 153932 * 2 ^ 59
def prefixEnd_153932 : Nat := 4983230072969 + 3 ^ 40 * 153932 * 2
def baseEnd_153932 : Nat := 46839172804738947580495

theorem tailTrace_153932 : CollatzResearch.WordTrace tailWord_153932 prefixEnd_153932 46839172804738947580495 := by
  unfold tailWord_153932
  simp only [CollatzResearch.WordTrace]
  refine ⟨2807180639169064168848025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3742907518892085558464033 2807180639169064168848025)
  ·
    refine ⟨2105385479376798126636019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2807180639169064168848025 2105385479376798126636019)
    ·
      refine ⟨3158078219065197189954029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2105385479376798126636019 3158078219065197189954029)
      ·
        refine ⟨1184279332149448946232761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3158078219065197189954029 1184279332149448946232761)
        ·
          refine ⟨888209499112086709674571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1184279332149448946232761 888209499112086709674571)
          ·
            refine ⟨1332314248668130064511857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 888209499112086709674571 1332314248668130064511857)
            ·
              refine ⟨999235686501097548383893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1332314248668130064511857 999235686501097548383893)
              ·
                refine ⟨46839172804738947580495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 999235686501097548383893 46839172804738947580495)
                ·
                  rfl

theorem cell19_153932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_153932 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_153932 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_153932 prefixEnd_153932 := by exact prefixLift 153932
  have htrace : WordTrace (prefixWord ++ tailWord_153932) baseStart_153932 baseEnd_153932 := by
    simpa [prefixWord, tailWord_153932, baseEnd_153932] using wordTrace_append hprefix tailTrace_153932
  have hstable : (prefixWord ++ tailWord_153932).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153932).length < 2 ^ (prefixWord ++ tailWord_153932).sum := by decide
  have hdescent : baseEnd_153932 < baseStart_153932 := by decide
  rcases family_descends (prefixWord ++ tailWord_153932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153970 : List Nat := [3, 2, 1, 2, 1, 3, 7]
def baseStart_153970 : Nat := 118140960795 + 153970 * 2 ^ 59
def prefixEnd_153970 : Nat := 4983230072969 + 3 ^ 40 * 153970 * 2
def baseEnd_153970 : Nat := 15616911876122039578649

theorem tailTrace_153970 : CollatzResearch.WordTrace tailWord_153970 prefixEnd_153970 15616911876122039578649 := by
  unfold tailWord_153970
  simp only [CollatzResearch.WordTrace]
  refine ⟨1403936813050115206894841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3743831501466973885052909 1403936813050115206894841)
  ·
    refine ⟨1052952609787586405171131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1403936813050115206894841 1052952609787586405171131)
    ·
      refine ⟨1579428914681379607756697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1052952609787586405171131 1579428914681379607756697)
      ·
        refine ⟨1184571686011034705817523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1579428914681379607756697 1184571686011034705817523)
        ·
          refine ⟨1776857529016552058726285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1184571686011034705817523 1776857529016552058726285)
          ·
            refine ⟨666321573381207022022357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1776857529016552058726285 666321573381207022022357)
            ·
              refine ⟨15616911876122039578649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 666321573381207022022357 15616911876122039578649)
              ·
                rfl

theorem cell19_153970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 7].length) (baseStart_153970 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_153970 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_153970 prefixEnd_153970 := by exact prefixLift 153970
  have htrace : WordTrace (prefixWord ++ tailWord_153970) baseStart_153970 baseEnd_153970 := by
    simpa [prefixWord, tailWord_153970, baseEnd_153970] using wordTrace_append hprefix tailTrace_153970
  have hstable : (prefixWord ++ tailWord_153970).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153970).length < 2 ^ (prefixWord ++ tailWord_153970).sum := by decide
  have hdescent : baseEnd_153970 < baseStart_153970 := by decide
  rcases family_descends (prefixWord ++ tailWord_153970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153987 : List Nat := [1, 1, 1, 3, 6, 1, 2, 4]
def baseStart_153987 : Nat := 118140960795 + 153987 * 2 ^ 59
def prefixEnd_153987 : Nat := 4983230072969 + 3 ^ 40 * 153987 * 2
def baseEnd_153987 : Nat := 46855908470515116358123

theorem tailTrace_153987 : CollatzResearch.WordTrace tailWord_153987 prefixEnd_153987 46855908470515116358123 := by
  unfold tailWord_153987
  simp only [CollatzResearch.WordTrace]
  refine ⟨5616367293138872730948215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3744244862092581820632143 5616367293138872730948215)
  ·
    refine ⟨8424550939708309096422323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5616367293138872730948215 8424550939708309096422323)
    ·
      refine ⟨12636826409562463644633485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8424550939708309096422323 12636826409562463644633485)
      ·
        refine ⟨4738809903585923866737557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12636826409562463644633485 4738809903585923866737557)
        ·
          refine ⟨222131714230590181253323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4738809903585923866737557 222131714230590181253323)
          ·
            refine ⟨333197571345885271879985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222131714230590181253323 333197571345885271879985)
            ·
              refine ⟨249898178509413953909989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 333197571345885271879985 249898178509413953909989)
              ·
                refine ⟨46855908470515116358123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 249898178509413953909989 46855908470515116358123)
                ·
                  rfl

theorem cell19_153987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 4].length) (baseStart_153987 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_153987 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_153987 prefixEnd_153987 := by exact prefixLift 153987
  have htrace : WordTrace (prefixWord ++ tailWord_153987) baseStart_153987 baseEnd_153987 := by
    simpa [prefixWord, tailWord_153987, baseEnd_153987] using wordTrace_append hprefix tailTrace_153987
  have hstable : (prefixWord ++ tailWord_153987).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153987).length < 2 ^ (prefixWord ++ tailWord_153987).sum := by decide
  have hdescent : baseEnd_153987 < baseStart_153987 := by decide
  rcases family_descends (prefixWord ++ tailWord_153987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154044 : List Nat := [2, 2, 2, 4, 1, 1, 3, 4]
def baseStart_154044 : Nat := 118140960795 + 154044 * 2 ^ 59
def prefixEnd_154044 : Nat := 4983230072969 + 3 ^ 40 * 154044 * 2
def baseEnd_154044 : Nat := 46873252705955873091301

theorem tailTrace_154044 : CollatzResearch.WordTrace tailWord_154044 prefixEnd_154044 46873252705955873091301 := by
  unfold tailWord_154044
  simp only [CollatzResearch.WordTrace]
  refine ⟨2809223126966185732886593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3745630835954914310515457 2809223126966185732886593)
  ·
    refine ⟨2106917345224639299664945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2809223126966185732886593 2106917345224639299664945)
    ·
      refine ⟨1580188008918479474748709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2106917345224639299664945 1580188008918479474748709)
      ·
        refine ⟨296285251672214901515383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1580188008918479474748709 296285251672214901515383)
        ·
          refine ⟨444427877508322352273075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296285251672214901515383 444427877508322352273075)
          ·
            refine ⟨666641816262483528409613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 444427877508322352273075 666641816262483528409613)
            ·
              refine ⟨249990681098431323153605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 666641816262483528409613 249990681098431323153605)
              ·
                refine ⟨46873252705955873091301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 249990681098431323153605 46873252705955873091301)
                ·
                  rfl

theorem cell19_154044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 4].length) (baseStart_154044 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_154044 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_154044 prefixEnd_154044 := by exact prefixLift 154044
  have htrace : WordTrace (prefixWord ++ tailWord_154044) baseStart_154044 baseEnd_154044 := by
    simpa [prefixWord, tailWord_154044, baseEnd_154044] using wordTrace_append hprefix tailTrace_154044
  have hstable : (prefixWord ++ tailWord_154044).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154044).length < 2 ^ (prefixWord ++ tailWord_154044).sum := by decide
  have hdescent : baseEnd_154044 < baseStart_154044 := by decide
  rcases family_descends (prefixWord ++ tailWord_154044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154114 : List Nat := [3, 4, 1, 2, 3, 1, 2, 3]
def baseStart_154114 : Nat := 118140960795 + 154114 * 2 ^ 59
def prefixEnd_154114 : Nat := 4983230072969 + 3 ^ 40 * 154114 * 2
def baseEnd_154114 : Nat := 46894552644216451535555

theorem tailTrace_154114 : CollatzResearch.WordTrace tailWord_154114 prefixEnd_154114 46894552644216451535555 := by
  unfold tailWord_154114
  simp only [CollatzResearch.WordTrace]
  refine ⟨1405249840919693355205349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3747332909119182280547597 1405249840919693355205349)
  ·
    refine ⟨263484345172442504101003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1405249840919693355205349 263484345172442504101003)
    ·
      refine ⟨395226517758663756151505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263484345172442504101003 395226517758663756151505)
      ·
        refine ⟨296419888318997817113629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 395226517758663756151505 296419888318997817113629)
        ·
          refine ⟨111157458119624181417611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 296419888318997817113629 111157458119624181417611)
          ·
            refine ⟨166736187179436272126417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111157458119624181417611 166736187179436272126417)
            ·
              refine ⟨125052140384577204094813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166736187179436272126417 125052140384577204094813)
              ·
                refine ⟨46894552644216451535555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125052140384577204094813 46894552644216451535555)
                ·
                  rfl

theorem cell19_154114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 3].length) (baseStart_154114 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_154114 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_154114 prefixEnd_154114 := by exact prefixLift 154114
  have htrace : WordTrace (prefixWord ++ tailWord_154114) baseStart_154114 baseEnd_154114 := by
    simpa [prefixWord, tailWord_154114, baseEnd_154114] using wordTrace_append hprefix tailTrace_154114
  have hstable : (prefixWord ++ tailWord_154114).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154114).length < 2 ^ (prefixWord ++ tailWord_154114).sum := by decide
  have hdescent : baseEnd_154114 < baseStart_154114 := by decide
  rcases family_descends (prefixWord ++ tailWord_154114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154122 : List Nat := [3, 1, 2, 2, 2, 1, 3, 5]
def baseStart_154122 : Nat := 118140960795 + 154122 * 2 ^ 59
def prefixEnd_154122 : Nat := 4983230072969 + 3 ^ 40 * 154122 * 2
def baseEnd_154122 : Nat := 46896986922874803357755

theorem tailTrace_154122 : CollatzResearch.WordTrace tailWord_154122 prefixEnd_154122 46896986922874803357755 := by
  unfold tailWord_154122
  simp only [CollatzResearch.WordTrace]
  refine ⟨1405322786912447696778155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3747527431766527191408413 1405322786912447696778155)
  ·
    refine ⟨2107984180368671545167233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1405322786912447696778155 2107984180368671545167233)
    ·
      refine ⟨1580988135276503658875425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2107984180368671545167233 1580988135276503658875425)
      ·
        refine ⟨1185741101457377744156569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1580988135276503658875425 1185741101457377744156569)
        ·
          refine ⟨889305826093033308117427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1185741101457377744156569 889305826093033308117427)
          ·
            refine ⟨1333958739139549962176141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 889305826093033308117427 1333958739139549962176141)
            ·
              refine ⟨500234527177331235816053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1333958739139549962176141 500234527177331235816053)
              ·
                refine ⟨46896986922874803357755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 500234527177331235816053 46896986922874803357755)
                ·
                  rfl

theorem cell19_154122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_154122 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_154122 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_154122 prefixEnd_154122 := by exact prefixLift 154122
  have htrace : WordTrace (prefixWord ++ tailWord_154122) baseStart_154122 baseEnd_154122 := by
    simpa [prefixWord, tailWord_154122, baseEnd_154122] using wordTrace_append hprefix tailTrace_154122
  have hstable : (prefixWord ++ tailWord_154122).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154122).length < 2 ^ (prefixWord ++ tailWord_154122).sum := by decide
  have hdescent : baseEnd_154122 < baseStart_154122 := by decide
  rcases family_descends (prefixWord ++ tailWord_154122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154141 : List Nat := [1, 4, 2, 2, 1, 2, 7]
def baseStart_154141 : Nat := 118140960795 + 154141 * 2 ^ 59
def prefixEnd_154141 : Nat := 4983230072969 + 3 ^ 40 * 154141 * 2
def baseEnd_154141 : Nat := 15634256111562796311827

theorem tailTrace_154141 : CollatzResearch.WordTrace tailWord_154141 prefixEnd_154141 15634256111562796311827 := by
  unfold tailWord_154141
  simp only [CollatzResearch.WordTrace]
  refine ⟨5621984134580957032054277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3747989423053971354702851 5621984134580957032054277)
  ·
    refine ⟨1054122025233929443510177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5621984134580957032054277 1054122025233929443510177)
    ·
      refine ⟨790591518925447082632633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1054122025233929443510177 790591518925447082632633)
      ·
        refine ⟨592943639194085311974475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 790591518925447082632633 592943639194085311974475)
        ·
          refine ⟨889415458791127967961713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 592943639194085311974475 889415458791127967961713)
          ·
            refine ⟨667061594093345975971285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 889415458791127967961713 667061594093345975971285)
            ·
              refine ⟨15634256111562796311827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 667061594093345975971285 15634256111562796311827)
              ·
                rfl

theorem cell19_154141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 7].length) (baseStart_154141 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_154141 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_154141 prefixEnd_154141 := by exact prefixLift 154141
  have htrace : WordTrace (prefixWord ++ tailWord_154141) baseStart_154141 baseEnd_154141 := by
    simpa [prefixWord, tailWord_154141, baseEnd_154141] using wordTrace_append hprefix tailTrace_154141
  have hstable : (prefixWord ++ tailWord_154141).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154141).length < 2 ^ (prefixWord ++ tailWord_154141).sum := by decide
  have hdescent : baseEnd_154141 < baseStart_154141 := by decide
  rcases family_descends (prefixWord ++ tailWord_154141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154213 : List Nat := [1, 3, 1, 3, 5, 1, 1, 4]
def baseStart_154213 : Nat := 118140960795 + 154213 * 2 ^ 59
def prefixEnd_154213 : Nat := 4983230072969 + 3 ^ 40 * 154213 * 2
def baseEnd_154213 : Nat := 46924676842613555335285

theorem tailTrace_154213 : CollatzResearch.WordTrace tailWord_154213 prefixEnd_154213 46924676842613555335285 := by
  unfold tailWord_154213
  simp only [CollatzResearch.WordTrace]
  refine ⟨5624610190320113328675293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3749740126880075552450195 5624610190320113328675293)
  ·
    refine ⟨2109228821370042498253235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5624610190320113328675293 2109228821370042498253235)
    ·
      refine ⟨3163843232055063747379853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2109228821370042498253235 3163843232055063747379853)
      ·
        refine ⟨1186441212020648905267445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3163843232055063747379853 1186441212020648905267445)
        ·
          refine ⟨111228863626935834868823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1186441212020648905267445 111228863626935834868823)
          ·
            refine ⟨166843295440403752303235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111228863626935834868823 166843295440403752303235)
            ·
              refine ⟨250264943160605628454853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166843295440403752303235 250264943160605628454853)
              ·
                refine ⟨46924676842613555335285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 250264943160605628454853 46924676842613555335285)
                ·
                  rfl

theorem cell19_154213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 4].length) (baseStart_154213 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_154213 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_154213 prefixEnd_154213 := by exact prefixLift 154213
  have htrace : WordTrace (prefixWord ++ tailWord_154213) baseStart_154213 baseEnd_154213 := by
    simpa [prefixWord, tailWord_154213, baseEnd_154213] using wordTrace_append hprefix tailTrace_154213
  have hstable : (prefixWord ++ tailWord_154213).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154213).length < 2 ^ (prefixWord ++ tailWord_154213).sum := by decide
  have hdescent : baseEnd_154213 < baseStart_154213 := by decide
  rcases family_descends (prefixWord ++ tailWord_154213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154219 : List Nat := [1, 1, 1, 1, 2, 2, 1, 10]
def baseStart_154219 : Nat := 118140960795 + 154219 * 2 ^ 59
def prefixEnd_154219 : Nat := 4983230072969 + 3 ^ 40 * 154219 * 2
def baseEnd_154219 : Nat := 46926502551607319201935

theorem tailTrace_154219 : CollatzResearch.WordTrace tailWord_154219 prefixEnd_154219 46926502551607319201935 := by
  unfold tailWord_154219
  simp only [CollatzResearch.WordTrace]
  refine ⟨5624829028298376353393711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3749886018865584235595807 5624829028298376353393711)
  ·
    refine ⟨8437243542447564530090567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5624829028298376353393711 8437243542447564530090567)
    ·
      refine ⟨12655865313671346795135851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8437243542447564530090567 12655865313671346795135851)
      ·
        refine ⟨18983797970507020192703777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12655865313671346795135851 18983797970507020192703777)
        ·
          refine ⟨14237848477880265144527833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18983797970507020192703777 14237848477880265144527833)
          ·
            refine ⟨10678386358410198858395875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14237848477880265144527833 10678386358410198858395875)
            ·
              refine ⟨16017579537615298287593813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10678386358410198858395875 16017579537615298287593813)
              ·
                refine ⟨46926502551607319201935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 16017579537615298287593813 46926502551607319201935)
                ·
                  rfl

theorem cell19_154219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 10].length) (baseStart_154219 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_154219 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_154219 prefixEnd_154219 := by exact prefixLift 154219
  have htrace : WordTrace (prefixWord ++ tailWord_154219) baseStart_154219 baseEnd_154219 := by
    simpa [prefixWord, tailWord_154219, baseEnd_154219] using wordTrace_append hprefix tailTrace_154219
  have hstable : (prefixWord ++ tailWord_154219).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154219).length < 2 ^ (prefixWord ++ tailWord_154219).sum := by decide
  have hdescent : baseEnd_154219 < baseStart_154219 := by decide
  rcases family_descends (prefixWord ++ tailWord_154219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154291 : List Nat := [1, 1, 1, 2, 3, 6, 2, 3]
def baseStart_154291 : Nat := 118140960795 + 154291 * 2 ^ 59
def prefixEnd_154291 : Nat := 4983230072969 + 3 ^ 40 * 154291 * 2
def baseEnd_154291 : Nat := 46948411059532485601739

theorem tailTrace_154291 : CollatzResearch.WordTrace tailWord_154291 prefixEnd_154291 46948411059532485601739 := by
  unfold tailWord_154291
  simp only [CollatzResearch.WordTrace]
  refine ⟨5627455084037532650014727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3751636722691688433343151 5627455084037532650014727)
  ·
    refine ⟨8441182626056298975022091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5627455084037532650014727 8441182626056298975022091)
    ·
      refine ⟨12661773939084448462533137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8441182626056298975022091 12661773939084448462533137)
      ·
        refine ⟨9496330454313336346899853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12661773939084448462533137 9496330454313336346899853)
        ·
          refine ⟨3561123920367501130087445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9496330454313336346899853 3561123920367501130087445)
          ·
            refine ⟨166927683767226615472849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3561123920367501130087445 166927683767226615472849)
            ·
              refine ⟨125195762825419961604637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166927683767226615472849 125195762825419961604637)
              ·
                refine ⟨46948411059532485601739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125195762825419961604637 46948411059532485601739)
                ·
                  rfl

theorem cell19_154291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 3].length) (baseStart_154291 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_154291 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_154291 prefixEnd_154291 := by exact prefixLift 154291
  have htrace : WordTrace (prefixWord ++ tailWord_154291) baseStart_154291 baseEnd_154291 := by
    simpa [prefixWord, tailWord_154291, baseEnd_154291] using wordTrace_append hprefix tailTrace_154291
  have hstable : (prefixWord ++ tailWord_154291).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154291).length < 2 ^ (prefixWord ++ tailWord_154291).sum := by decide
  have hdescent : baseEnd_154291 < baseStart_154291 := by decide
  rcases family_descends (prefixWord ++ tailWord_154291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154312 : List Nat := [2, 1, 3, 1, 2, 5, 5]
def baseStart_154312 : Nat := 118140960795 + 154312 * 2 ^ 59
def prefixEnd_154312 : Nat := 4983230072969 + 3 ^ 40 * 154312 * 2
def baseEnd_154312 : Nat := 15651600347003553045005

theorem tailTrace_154312 : CollatzResearch.WordTrace tailWord_154312 prefixEnd_154312 15651600347003553045005 := by
  unfold tailWord_154312
  simp only [CollatzResearch.WordTrace]
  refine ⟨2814110508480726618264595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3752147344640968824352793 2814110508480726618264595)
  ·
    refine ⟨4221165762721089927396893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2814110508480726618264595 4221165762721089927396893)
    ·
      refine ⟨1582937161020408722773835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4221165762721089927396893 1582937161020408722773835)
      ·
        refine ⟨2374405741530613084160753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1582937161020408722773835 2374405741530613084160753)
        ·
          refine ⟨1780804306147959813120565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2374405741530613084160753 1780804306147959813120565)
          ·
            refine ⟨166950403701371232480053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1780804306147959813120565 166950403701371232480053)
            ·
              refine ⟨15651600347003553045005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 166950403701371232480053 15651600347003553045005)
              ·
                rfl

theorem cell19_154312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 5].length) (baseStart_154312 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_154312 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_154312 prefixEnd_154312 := by exact prefixLift 154312
  have htrace : WordTrace (prefixWord ++ tailWord_154312) baseStart_154312 baseEnd_154312 := by
    simpa [prefixWord, tailWord_154312, baseEnd_154312] using wordTrace_append hprefix tailTrace_154312
  have hstable : (prefixWord ++ tailWord_154312).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154312).length < 2 ^ (prefixWord ++ tailWord_154312).sum := by decide
  have hdescent : baseEnd_154312 < baseStart_154312 := by decide
  rcases family_descends (prefixWord ++ tailWord_154312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154350 : List Nat := [4, 1, 2, 1, 1, 3, 2, 5]
def baseStart_154350 : Nat := 118140960795 + 154350 * 2 ^ 59
def prefixEnd_154350 : Nat := 4983230072969 + 3 ^ 40 * 154350 * 2
def baseEnd_154350 : Nat := 46966363864637830290467

theorem tailTrace_154350 : CollatzResearch.WordTrace tailWord_154350 prefixEnd_154350 46966363864637830290467 := by
  unfold tailWord_154350
  simp only [CollatzResearch.WordTrace]
  refine ⟨703700873852973215801563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3753071327215857150941669 703700873852973215801563)
  ·
    refine ⟨1055551310779459823702345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 703700873852973215801563 1055551310779459823702345)
    ·
      refine ⟨791663483084594867776759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1055551310779459823702345 791663483084594867776759)
      ·
        refine ⟨1187495224626892301665139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 791663483084594867776759 1187495224626892301665139)
        ·
          refine ⟨1781242836940338452497709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1187495224626892301665139 1781242836940338452497709)
          ·
            refine ⟨667966063852626919686641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1781242836940338452497709 667966063852626919686641)
            ·
              refine ⟨500974547889470189764981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 667966063852626919686641 500974547889470189764981)
              ·
                refine ⟨46966363864637830290467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 500974547889470189764981 46966363864637830290467)
                ·
                  rfl

theorem cell19_154350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_154350 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_154350 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_154350 prefixEnd_154350 := by exact prefixLift 154350
  have htrace : WordTrace (prefixWord ++ tailWord_154350) baseStart_154350 baseEnd_154350 := by
    simpa [prefixWord, tailWord_154350, baseEnd_154350] using wordTrace_append hprefix tailTrace_154350
  have hstable : (prefixWord ++ tailWord_154350).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154350).length < 2 ^ (prefixWord ++ tailWord_154350).sum := by decide
  have hdescent : baseEnd_154350 < baseStart_154350 := by decide
  rcases family_descends (prefixWord ++ tailWord_154350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154352 : List Nat := [2, 1, 1, 1, 3, 1, 3, 7]
def baseStart_154352 : Nat := 118140960795 + 154352 * 2 ^ 59
def prefixEnd_154352 : Nat := 4983230072969 + 3 ^ 40 * 154352 * 2
def baseEnd_154352 : Nat := 46966972434302418246017

theorem tailTrace_154352 : CollatzResearch.WordTrace tailWord_154352 prefixEnd_154352 46966972434302418246017 := by
  unfold tailWord_154352
  simp only [CollatzResearch.WordTrace]
  refine ⟨2814839968408270033992655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3753119957877693378656873 2814839968408270033992655)
  ·
    refine ⟨4222259952612405050988983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2814839968408270033992655 4222259952612405050988983)
    ·
      refine ⟨6333389928918607576483475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4222259952612405050988983 6333389928918607576483475)
      ·
        refine ⟨9500084893377911364725213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6333389928918607576483475 9500084893377911364725213)
        ·
          refine ⟨3562531835016716761771955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9500084893377911364725213 3562531835016716761771955)
          ·
            refine ⟨5343797752525075142657933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3562531835016716761771955 5343797752525075142657933)
            ·
              refine ⟨2003924157196903178496725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5343797752525075142657933 2003924157196903178496725)
              ·
                refine ⟨46966972434302418246017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2003924157196903178496725 46966972434302418246017)
                ·
                  rfl

theorem cell19_154352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_154352 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_154352 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_154352 prefixEnd_154352 := by exact prefixLift 154352
  have htrace : WordTrace (prefixWord ++ tailWord_154352) baseStart_154352 baseEnd_154352 := by
    simpa [prefixWord, tailWord_154352, baseEnd_154352] using wordTrace_append hprefix tailTrace_154352
  have hstable : (prefixWord ++ tailWord_154352).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154352).length < 2 ^ (prefixWord ++ tailWord_154352).sum := by decide
  have hdescent : baseEnd_154352 < baseStart_154352 := by decide
  rcases family_descends (prefixWord ++ tailWord_154352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154426 : List Nat := [3, 1, 1, 1, 6, 1, 6]
def baseStart_154426 : Nat := 118140960795 + 154426 * 2 ^ 59
def prefixEnd_154426 : Nat := 4983230072969 + 3 ^ 40 * 154426 * 2
def baseEnd_154426 : Nat := 15663163170630724200457

theorem tailTrace_154426 : CollatzResearch.WordTrace tailWord_154426 prefixEnd_154426 15663163170630724200457 := by
  unfold tailWord_154426
  simp only [CollatzResearch.WordTrace]
  refine ⟨1408094734637112676544783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3754919292365633804119421 1408094734637112676544783)
  ·
    refine ⟨2112142101955669014817175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1408094734637112676544783 2112142101955669014817175)
    ·
      refine ⟨3168213152933503522225763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2112142101955669014817175 3168213152933503522225763)
      ·
        refine ⟨4752319729400255283338645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3168213152933503522225763 4752319729400255283338645)
        ·
          refine ⟨222764987315636966406499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4752319729400255283338645 222764987315636966406499)
          ·
            refine ⟨334147480973455449609749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222764987315636966406499 334147480973455449609749)
            ·
              refine ⟨15663163170630724200457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 334147480973455449609749 15663163170630724200457)
              ·
                rfl

theorem cell19_154426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 6].length) (baseStart_154426 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_154426 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_154426 prefixEnd_154426 := by exact prefixLift 154426
  have htrace : WordTrace (prefixWord ++ tailWord_154426) baseStart_154426 baseEnd_154426 := by
    simpa [prefixWord, tailWord_154426, baseEnd_154426] using wordTrace_append hprefix tailTrace_154426
  have hstable : (prefixWord ++ tailWord_154426).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154426).length < 2 ^ (prefixWord ++ tailWord_154426).sum := by decide
  have hdescent : baseEnd_154426 < baseStart_154426 := by decide
  rcases family_descends (prefixWord ++ tailWord_154426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154460 : List Nat := [2, 2, 4, 2, 1, 3, 2, 3]
def baseStart_154460 : Nat := 118140960795 + 154460 * 2 ^ 59
def prefixEnd_154460 : Nat := 4983230072969 + 3 ^ 40 * 154460 * 2
def baseEnd_154460 : Nat := 46999835196190167845723

theorem tailTrace_154460 : CollatzResearch.WordTrace tailWord_154460 prefixEnd_154460 46999835196190167845723 := by
  unfold tailWord_154460
  simp only [CollatzResearch.WordTrace]
  refine ⟨2816809510212637256458417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3755746013616849675277889 2816809510212637256458417)
  ·
    refine ⟨2112607132659477942343813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2816809510212637256458417 2112607132659477942343813)
    ·
      refine ⟨396113837373652114189465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2112607132659477942343813 396113837373652114189465)
      ·
        refine ⟨297085378030239085642099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 396113837373652114189465 297085378030239085642099)
        ·
          refine ⟨445628067045358628463149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297085378030239085642099 445628067045358628463149)
          ·
            refine ⟨167110525142009485673681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 445628067045358628463149 167110525142009485673681)
            ·
              refine ⟨125332893856507114255261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167110525142009485673681 125332893856507114255261)
              ·
                refine ⟨46999835196190167845723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125332893856507114255261 46999835196190167845723)
                ·
                  rfl

theorem cell19_154460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 3].length) (baseStart_154460 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_154460 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_154460 prefixEnd_154460 := by exact prefixLift 154460
  have htrace : WordTrace (prefixWord ++ tailWord_154460) baseStart_154460 baseEnd_154460 := by
    simpa [prefixWord, tailWord_154460, baseEnd_154460] using wordTrace_append hprefix tailTrace_154460
  have hstable : (prefixWord ++ tailWord_154460).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154460).length < 2 ^ (prefixWord ++ tailWord_154460).sum := by decide
  have hdescent : baseEnd_154460 < baseStart_154460 := by decide
  rcases family_descends (prefixWord ++ tailWord_154460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154557 : List Nat := [1, 4, 1, 2, 4, 2, 1, 4]
def baseStart_154557 : Nat := 118140960795 + 154557 * 2 ^ 59
def prefixEnd_154557 : Nat := 4983230072969 + 3 ^ 40 * 154557 * 2
def baseEnd_154557 : Nat := 47029350824922683689903

theorem tailTrace_154557 : CollatzResearch.WordTrace tailWord_154557 prefixEnd_154557 47029350824922683689903 := by
  unfold tailWord_154557
  simp only [CollatzResearch.WordTrace]
  refine ⟨5637156901073860079197925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3758104600715906719465283 5637156901073860079197925)
  ·
    refine ⟨1056966918951348764849611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5637156901073860079197925 1056966918951348764849611)
    ·
      refine ⟨1585450378427023147274417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1056966918951348764849611 1585450378427023147274417)
      ·
        refine ⟨1189087783820267360455813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1585450378427023147274417 1189087783820267360455813)
        ·
          refine ⟨222953959466300130085465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1189087783820267360455813 222953959466300130085465)
          ·
            refine ⟨167215469599725097564099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222953959466300130085465 167215469599725097564099)
            ·
              refine ⟨250823204399587646346149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167215469599725097564099 250823204399587646346149)
              ·
                refine ⟨47029350824922683689903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 250823204399587646346149 47029350824922683689903)
                ·
                  rfl

theorem cell19_154557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 4].length) (baseStart_154557 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_154557 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_154557 prefixEnd_154557 := by exact prefixLift 154557
  have htrace : WordTrace (prefixWord ++ tailWord_154557) baseStart_154557 baseEnd_154557 := by
    simpa [prefixWord, tailWord_154557, baseEnd_154557] using wordTrace_append hprefix tailTrace_154557
  have hstable : (prefixWord ++ tailWord_154557).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154557).length < 2 ^ (prefixWord ++ tailWord_154557).sum := by decide
  have hdescent : baseEnd_154557 < baseStart_154557 := by decide
  rcases family_descends (prefixWord ++ tailWord_154557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154635 : List Nat := [1, 1, 1, 1, 6, 2, 4, 3]
def baseStart_154635 : Nat := 118140960795 + 154635 * 2 ^ 59
def prefixEnd_154635 : Nat := 4983230072969 + 3 ^ 40 * 154635 * 2
def baseEnd_154635 : Nat := 47053085041841613956357

theorem tailTrace_154635 : CollatzResearch.WordTrace tailWord_154635 prefixEnd_154635 47053085041841613956357 := by
  unfold tailWord_154635
  simp only [CollatzResearch.WordTrace]
  refine ⟨5640001794791279400537359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3760001196527519600358239 5640001794791279400537359)
  ·
    refine ⟨8460002692186919100806039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5640001794791279400537359 8460002692186919100806039)
    ·
      refine ⟨12690004038280378651209059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8460002692186919100806039 12690004038280378651209059)
      ·
        refine ⟨19035006057420567976813589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12690004038280378651209059 19035006057420567976813589)
        ·
          refine ⟨892265908941589123913137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19035006057420567976813589 892265908941589123913137)
          ·
            refine ⟨669199431706191842934853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 892265908941589123913137 669199431706191842934853)
            ·
              refine ⟨125474893444910970550285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 669199431706191842934853 125474893444910970550285)
              ·
                refine ⟨47053085041841613956357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125474893444910970550285 47053085041841613956357)
                ·
                  rfl

theorem cell19_154635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 3].length) (baseStart_154635 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_154635 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_154635 prefixEnd_154635 := by exact prefixLift 154635
  have htrace : WordTrace (prefixWord ++ tailWord_154635) baseStart_154635 baseEnd_154635 := by
    simpa [prefixWord, tailWord_154635, baseEnd_154635] using wordTrace_append hprefix tailTrace_154635
  have hstable : (prefixWord ++ tailWord_154635).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154635).length < 2 ^ (prefixWord ++ tailWord_154635).sum := by decide
  have hdescent : baseEnd_154635 < baseStart_154635 := by decide
  rcases family_descends (prefixWord ++ tailWord_154635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154652 : List Nat := [2, 2, 3, 1, 5, 1, 5]
def baseStart_154652 : Nat := 118140960795 + 154652 * 2 ^ 59
def prefixEnd_154652 : Nat := 4983230072969 + 3 ^ 40 * 154652 * 2
def baseEnd_154652 : Nat := 15686085961330203859511

theorem tailTrace_154652 : CollatzResearch.WordTrace tailWord_154652 prefixEnd_154652 15686085961330203859511 := by
  unfold tailWord_154652
  simp only [CollatzResearch.WordTrace]
  refine ⟨2820310917864845651953105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3760414557153127535937473 2820310917864845651953105)
  ·
    refine ⟨2115233188398634238964829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2820310917864845651953105 2115233188398634238964829)
    ·
      refine ⟨793212445649487839611811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2115233188398634238964829 793212445649487839611811)
      ·
        refine ⟨1189818668474231759417717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 793212445649487839611811 1189818668474231759417717)
        ·
          refine ⟨111545500169459227445411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1189818668474231759417717 111545500169459227445411)
          ·
            refine ⟨167318250254188841168117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111545500169459227445411 167318250254188841168117)
            ·
              refine ⟨15686085961330203859511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 167318250254188841168117 15686085961330203859511)
              ·
                rfl

theorem cell19_154652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 5].length) (baseStart_154652 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_154652 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_154652 prefixEnd_154652 := by exact prefixLift 154652
  have htrace : WordTrace (prefixWord ++ tailWord_154652) baseStart_154652 baseEnd_154652 := by
    simpa [prefixWord, tailWord_154652, baseEnd_154652] using wordTrace_append hprefix tailTrace_154652
  have hstable : (prefixWord ++ tailWord_154652).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154652).length < 2 ^ (prefixWord ++ tailWord_154652).sum := by decide
  have hdescent : baseEnd_154652 < baseStart_154652 := by decide
  rcases family_descends (prefixWord ++ tailWord_154652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154730 : List Nat := [3, 1, 3, 2, 2, 1, 3, 4]
def baseStart_154730 : Nat := 118140960795 + 154730 * 2 ^ 59
def prefixEnd_154730 : Nat := 4983230072969 + 3 ^ 40 * 154730 * 2
def baseEnd_154730 : Nat := 47081992100909541844987

theorem tailTrace_154730 : CollatzResearch.WordTrace tailWord_154730 prefixEnd_154730 47081992100909541844987 := by
  unfold tailWord_154730
  simp only [CollatzResearch.WordTrace]
  refine ⟨1410866682361777656311411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3762311152964740416830429 1410866682361777656311411)
  ·
    refine ⟨2116300023542666484467117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1410866682361777656311411 2116300023542666484467117)
    ·
      refine ⟨793612508828499931675169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2116300023542666484467117 793612508828499931675169)
      ·
        refine ⟨595209381621374948756377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 793612508828499931675169 595209381621374948756377)
        ·
          refine ⟨446407036216031211567283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 595209381621374948756377 446407036216031211567283)
          ·
            refine ⟨669610554324046817350925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 446407036216031211567283 669610554324046817350925)
            ·
              refine ⟨251103957871517556506597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 669610554324046817350925 251103957871517556506597)
              ·
                refine ⟨47081992100909541844987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 251103957871517556506597 47081992100909541844987)
                ·
                  rfl

theorem cell19_154730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_154730 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_154730 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_154730 prefixEnd_154730 := by exact prefixLift 154730
  have htrace : WordTrace (prefixWord ++ tailWord_154730) baseStart_154730 baseEnd_154730 := by
    simpa [prefixWord, tailWord_154730, baseEnd_154730] using wordTrace_append hprefix tailTrace_154730
  have hstable : (prefixWord ++ tailWord_154730).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154730).length < 2 ^ (prefixWord ++ tailWord_154730).sum := by decide
  have hdescent : baseEnd_154730 < baseStart_154730 := by decide
  rcases family_descends (prefixWord ++ tailWord_154730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154749 : List Nat := [1, 4, 1, 1, 3, 1, 5, 3]
def baseStart_154749 : Nat := 118140960795 + 154749 * 2 ^ 59
def prefixEnd_154749 : Nat := 4983230072969 + 3 ^ 40 * 154749 * 2
def baseEnd_154749 : Nat := 47087773512723127422713

theorem tailTrace_154749 : CollatzResearch.WordTrace tailWord_154749 prefixEnd_154749 47087773512723127422713 := by
  unfold tailWord_154749
  simp only [CollatzResearch.WordTrace]
  refine ⟨5644159716378276870187301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3762773144252184580124867 5644159716378276870187301)
  ·
    refine ⟨1058279946820926913160119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5644159716378276870187301 1058279946820926913160119)
    ·
      refine ⟨1587419920231390369740179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1058279946820926913160119 1587419920231390369740179)
      ·
        refine ⟨2381129880347085554610269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1587419920231390369740179 2381129880347085554610269)
        ·
          refine ⟨892923705130157082978851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2381129880347085554610269 892923705130157082978851)
          ·
            refine ⟨1339385557695235624468277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 892923705130157082978851 1339385557695235624468277)
            ·
              refine ⟨125567396033928339793901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1339385557695235624468277 125567396033928339793901)
              ·
                refine ⟨47087773512723127422713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125567396033928339793901 47087773512723127422713)
                ·
                  rfl

theorem cell19_154749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 3].length) (baseStart_154749 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_154749 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_154749 prefixEnd_154749 := by exact prefixLift 154749
  have htrace : WordTrace (prefixWord ++ tailWord_154749) baseStart_154749 baseEnd_154749 := by
    simpa [prefixWord, tailWord_154749, baseEnd_154749] using wordTrace_append hprefix tailTrace_154749
  have hstable : (prefixWord ++ tailWord_154749).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154749).length < 2 ^ (prefixWord ++ tailWord_154749).sum := by decide
  have hdescent : baseEnd_154749 < baseStart_154749 := by decide
  rcases family_descends (prefixWord ++ tailWord_154749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154882 : List Nat := [3, 4, 1, 1, 3, 7]
def baseStart_154882 : Nat := 118140960795 + 154882 * 2 ^ 59
def prefixEnd_154882 : Nat := 4983230072969 + 3 ^ 40 * 154882 * 2
def baseEnd_154882 : Nat := 5236471488379802940755

theorem tailTrace_154882 : CollatzResearch.WordTrace tailWord_154882 prefixEnd_154882 5236471488379802940755 := by
  unfold tailWord_154882
  simp only [CollatzResearch.WordTrace]
  refine ⟨1412252656224110146194725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3766007083264293723185933 1412252656224110146194725)
  ·
    refine ⟨264797373042020652411511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1412252656224110146194725 264797373042020652411511)
    ·
      refine ⟨397196059563030978617267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264797373042020652411511 397196059563030978617267)
      ·
        refine ⟨595794089344546467925901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 397196059563030978617267 595794089344546467925901)
        ·
          refine ⟨223422783504204925472213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 595794089344546467925901 223422783504204925472213)
          ·
            refine ⟨5236471488379802940755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 223422783504204925472213 5236471488379802940755)
            ·
              rfl

theorem cell19_154882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 7].length) (baseStart_154882 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_154882 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_154882 prefixEnd_154882 := by exact prefixLift 154882
  have htrace : WordTrace (prefixWord ++ tailWord_154882) baseStart_154882 baseEnd_154882 := by
    simpa [prefixWord, tailWord_154882, baseEnd_154882] using wordTrace_append hprefix tailTrace_154882
  have hstable : (prefixWord ++ tailWord_154882).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154882).length < 2 ^ (prefixWord ++ tailWord_154882).sum := by decide
  have hdescent : baseEnd_154882 < baseStart_154882 := by decide
  rcases family_descends (prefixWord ++ tailWord_154882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154884 : List Nat := [2, 3, 2, 2, 2, 8]
def baseStart_154884 : Nat := 118140960795 + 154884 * 2 ^ 59
def prefixEnd_154884 : Nat := 4983230072969 + 3 ^ 40 * 154884 * 2
def baseEnd_154884 : Nat := 5236539107231423824705

theorem tailTrace_154884 : CollatzResearch.WordTrace tailWord_154884 prefixEnd_154884 5236539107231423824705 := by
  unfold tailWord_154884
  simp only [CollatzResearch.WordTrace]
  refine ⟨2824541785444597463175853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3766055713926129950901137 2824541785444597463175853)
  ·
    refine ⟨1059203169541724048690945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2824541785444597463175853 1059203169541724048690945)
    ·
      refine ⟨794402377156293036518209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1059203169541724048690945 794402377156293036518209)
      ·
        refine ⟨595801782867219777388657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 794402377156293036518209 595801782867219777388657)
        ·
          refine ⟨446851337150414833041493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 595801782867219777388657 446851337150414833041493)
          ·
            refine ⟨5236539107231423824705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 446851337150414833041493 5236539107231423824705)
            ·
              rfl

theorem cell19_154884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 8].length) (baseStart_154884 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_154884 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_154884 prefixEnd_154884 := by exact prefixLift 154884
  have htrace : WordTrace (prefixWord ++ tailWord_154884) baseStart_154884 baseEnd_154884 := by
    simpa [prefixWord, tailWord_154884, baseEnd_154884] using wordTrace_append hprefix tailTrace_154884
  have hstable : (prefixWord ++ tailWord_154884).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154884).length < 2 ^ (prefixWord ++ tailWord_154884).sum := by decide
  have hdescent : baseEnd_154884 < baseStart_154884 := by decide
  rcases family_descends (prefixWord ++ tailWord_154884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154973 : List Nat := [1, 4, 5, 1, 1, 1, 1, 5]
def baseStart_154973 : Nat := 118140960795 + 154973 * 2 ^ 59
def prefixEnd_154973 : Nat := 4983230072969 + 3 ^ 40 * 154973 * 2
def baseEnd_154973 : Nat := 47155933315156978444325

theorem tailTrace_154973 : CollatzResearch.WordTrace tailWord_154973 prefixEnd_154973 47155933315156978444325 := by
  unfold tailWord_154973
  simp only [CollatzResearch.WordTrace]
  refine ⟨5652329667566763126341573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3768219778377842084227715 5652329667566763126341573)
  ·
    refine ⟨1059811812668768086189045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5652329667566763126341573 1059811812668768086189045)
    ·
      refine ⟨99357357437697008080223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1059811812668768086189045 99357357437697008080223)
      ·
        refine ⟨149036036156545512120335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99357357437697008080223 149036036156545512120335)
        ·
          refine ⟨223554054234818268180503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149036036156545512120335 223554054234818268180503)
          ·
            refine ⟨335331081352227402270755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223554054234818268180503 335331081352227402270755)
            ·
              refine ⟨502996622028341103406133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335331081352227402270755 502996622028341103406133)
              ·
                refine ⟨47155933315156978444325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 502996622028341103406133 47155933315156978444325)
                ·
                  rfl

theorem cell19_154973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 5].length) (baseStart_154973 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_154973 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_154973 prefixEnd_154973 := by exact prefixLift 154973
  have htrace : WordTrace (prefixWord ++ tailWord_154973) baseStart_154973 baseEnd_154973 := by
    simpa [prefixWord, tailWord_154973, baseEnd_154973] using wordTrace_append hprefix tailTrace_154973
  have hstable : (prefixWord ++ tailWord_154973).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154973).length < 2 ^ (prefixWord ++ tailWord_154973).sum := by decide
  have hdescent : baseEnd_154973 < baseStart_154973 := by decide
  rcases family_descends (prefixWord ++ tailWord_154973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154979 : List Nat := [1, 1, 1, 5, 2, 3, 1, 5]
def baseStart_154979 : Nat := 118140960795 + 154979 * 2 ^ 59
def prefixEnd_154979 : Nat := 4983230072969 + 3 ^ 40 * 154979 * 2
def baseEnd_154979 : Nat := 47157759024150742310975

theorem tailTrace_154979 : CollatzResearch.WordTrace tailWord_154979 prefixEnd_154979 47157759024150742310975 := by
  unfold tailWord_154979
  simp only [CollatzResearch.WordTrace]
  refine ⟨5652548505545026151059991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3768365670363350767373327 5652548505545026151059991)
  ·
    refine ⟨8478822758317539226589987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5652548505545026151059991 8478822758317539226589987)
    ·
      refine ⟨12718234137476308839884981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8478822758317539226589987 12718234137476308839884981)
      ·
        refine ⟨1192334450388403953739217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12718234137476308839884981 1192334450388403953739217)
        ·
          refine ⟨894250837791302965304413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1192334450388403953739217 894250837791302965304413)
          ·
            refine ⟨335344064171738611989155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 894250837791302965304413 335344064171738611989155)
            ·
              refine ⟨503016096257607917983733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335344064171738611989155 503016096257607917983733)
              ·
                refine ⟨47157759024150742310975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 503016096257607917983733 47157759024150742310975)
                ·
                  rfl

theorem cell19_154979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 5].length) (baseStart_154979 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_154979 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_154979 prefixEnd_154979 := by exact prefixLift 154979
  have htrace : WordTrace (prefixWord ++ tailWord_154979) baseStart_154979 baseEnd_154979 := by
    simpa [prefixWord, tailWord_154979, baseEnd_154979] using wordTrace_append hprefix tailTrace_154979
  have hstable : (prefixWord ++ tailWord_154979).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154979).length < 2 ^ (prefixWord ++ tailWord_154979).sum := by decide
  have hdescent : baseEnd_154979 < baseStart_154979 := by decide
  rcases family_descends (prefixWord ++ tailWord_154979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155095 : List Nat := [1, 1, 3, 2, 1, 1, 1, 9]
def baseStart_155095 : Nat := 118140960795 + 155095 * 2 ^ 59
def prefixEnd_155095 : Nat := 4983230072969 + 3 ^ 40 * 155095 * 2
def baseEnd_155095 : Nat := 47193056064696843732881

theorem tailTrace_155095 : CollatzResearch.WordTrace tailWord_155095 prefixEnd_155095 47193056064696843732881 := by
  unfold tailWord_155095
  simp only [CollatzResearch.WordTrace]
  refine ⟨5656779373124777962282739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3771186248749851974855159 5656779373124777962282739)
  ·
    refine ⟨8485169059687166943424109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5656779373124777962282739 8485169059687166943424109)
    ·
      refine ⟨3181938397382687603784041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8485169059687166943424109 3181938397382687603784041)
      ·
        refine ⟨2386453798037015702838031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3181938397382687603784041 2386453798037015702838031)
        ·
          refine ⟨3579680697055523554257047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2386453798037015702838031 3579680697055523554257047)
          ·
            refine ⟨5369521045583285331385571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3579680697055523554257047 5369521045583285331385571)
            ·
              refine ⟨8054281568374927997078357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5369521045583285331385571 8054281568374927997078357)
              ·
                refine ⟨47193056064696843732881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8054281568374927997078357 47193056064696843732881)
                ·
                  rfl

theorem cell19_155095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 9].length) (baseStart_155095 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_155095 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_155095 prefixEnd_155095 := by exact prefixLift 155095
  have htrace : WordTrace (prefixWord ++ tailWord_155095) baseStart_155095 baseEnd_155095 := by
    simpa [prefixWord, tailWord_155095, baseEnd_155095] using wordTrace_append hprefix tailTrace_155095
  have hstable : (prefixWord ++ tailWord_155095).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155095).length < 2 ^ (prefixWord ++ tailWord_155095).sum := by decide
  have hdescent : baseEnd_155095 < baseStart_155095 := by decide
  rcases family_descends (prefixWord ++ tailWord_155095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155169 : List Nat := [1, 2, 3, 2, 2, 4, 5]
def baseStart_155169 : Nat := 118140960795 + 155169 * 2 ^ 59
def prefixEnd_155169 : Nat := 4983230072969 + 3 ^ 40 * 155169 * 2
def baseEnd_155169 : Nat := 15738524380762199362745

theorem tailTrace_155169 : CollatzResearch.WordTrace tailWord_155169 prefixEnd_155169 15738524380762199362745 := by
  unfold tailWord_155169
  simp only [CollatzResearch.WordTrace]
  refine ⟨5659478374856688600476561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3772985583237792400317707 5659478374856688600476561)
  ·
    refine ⟨4244608781142516450357421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5659478374856688600476561 4244608781142516450357421)
    ·
      refine ⟨1591728292928443668884033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4244608781142516450357421 1591728292928443668884033)
      ·
        refine ⟨1193796219696332751663025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1591728292928443668884033 1193796219696332751663025)
        ·
          refine ⟨895347164772249563747269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1193796219696332751663025 895347164772249563747269)
          ·
            refine ⟨167877593394796793202613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 895347164772249563747269 167877593394796793202613)
            ·
              refine ⟨15738524380762199362745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 167877593394796793202613 15738524380762199362745)
              ·
                rfl

theorem cell19_155169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 5].length) (baseStart_155169 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_155169 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_155169 prefixEnd_155169 := by exact prefixLift 155169
  have htrace : WordTrace (prefixWord ++ tailWord_155169) baseStart_155169 baseEnd_155169 := by
    simpa [prefixWord, tailWord_155169, baseEnd_155169] using wordTrace_append hprefix tailTrace_155169
  have hstable : (prefixWord ++ tailWord_155169).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155169).length < 2 ^ (prefixWord ++ tailWord_155169).sum := by decide
  have hdescent : baseEnd_155169 < baseStart_155169 := by decide
  rcases family_descends (prefixWord ++ tailWord_155169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155222 : List Nat := [5, 2, 2, 2, 1, 7]
def baseStart_155222 : Nat := 118140960795 + 155222 * 2 ^ 59
def prefixEnd_155222 : Nat := 4983230072969 + 3 ^ 40 * 155222 * 2
def baseEnd_155222 : Nat := 5247966693155353212257

theorem tailTrace_155222 : CollatzResearch.WordTrace tailWord_155222 prefixEnd_155222 5247966693155353212257 := by
  unfold tailWord_155222
  simp only [CollatzResearch.WordTrace]
  refine ⟨353838215229042415759745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3774274295776452434770613 353838215229042415759745)
  ·
    refine ⟨265378661421781811819809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 353838215229042415759745 265378661421781811819809)
    ·
      refine ⟨199033996066336358864857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265378661421781811819809 199033996066336358864857)
      ·
        refine ⟨149275497049752269148643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199033996066336358864857 149275497049752269148643)
        ·
          refine ⟨223913245574628403722965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149275497049752269148643 223913245574628403722965)
          ·
            refine ⟨5247966693155353212257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 223913245574628403722965 5247966693155353212257)
            ·
              rfl

theorem cell19_155222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 7].length) (baseStart_155222 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_155222 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_155222 prefixEnd_155222 := by exact prefixLift 155222
  have htrace : WordTrace (prefixWord ++ tailWord_155222) baseStart_155222 baseEnd_155222 := by
    simpa [prefixWord, tailWord_155222, baseEnd_155222] using wordTrace_append hprefix tailTrace_155222
  have hstable : (prefixWord ++ tailWord_155222).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155222).length < 2 ^ (prefixWord ++ tailWord_155222).sum := by decide
  have hdescent : baseEnd_155222 < baseStart_155222 := by decide
  rcases family_descends (prefixWord ++ tailWord_155222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155264 : List Nat := [2, 1, 1, 2, 1, 4, 5, 3]
def baseStart_155264 : Nat := 118140960795 + 155264 * 2 ^ 59
def prefixEnd_155264 : Nat := 4983230072969 + 3 ^ 40 * 155264 * 2
def baseEnd_155264 : Nat := 47244480201354525976865

theorem tailTrace_155264 : CollatzResearch.WordTrace tailWord_155264 prefixEnd_155264 47244480201354525976865 := by
  unfold tailWord_155264
  simp only [CollatzResearch.WordTrace]
  refine ⟨2831471654756259912592423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3775295539675013216789897 2831471654756259912592423)
  ·
    refine ⟨4247207482134389868888635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2831471654756259912592423 4247207482134389868888635)
    ·
      refine ⟨6370811223201584803332953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4247207482134389868888635 6370811223201584803332953)
      ·
        refine ⟨4778108417401188602499715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6370811223201584803332953 4778108417401188602499715)
        ·
          refine ⟨7167162626101782903749573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4778108417401188602499715 7167162626101782903749573)
          ·
            refine ⟨1343842992394084294453045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7167162626101782903749573 1343842992394084294453045)
            ·
              refine ⟨125985280536945402604973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1343842992394084294453045 125985280536945402604973)
              ·
                refine ⟨47244480201354525976865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125985280536945402604973 47244480201354525976865)
                ·
                  rfl

theorem cell19_155264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 3].length) (baseStart_155264 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_155264 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_155264 prefixEnd_155264 := by exact prefixLift 155264
  have htrace : WordTrace (prefixWord ++ tailWord_155264) baseStart_155264 baseEnd_155264 := by
    simpa [prefixWord, tailWord_155264, baseEnd_155264] using wordTrace_append hprefix tailTrace_155264
  have hstable : (prefixWord ++ tailWord_155264).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155264).length < 2 ^ (prefixWord ++ tailWord_155264).sum := by decide
  have hdescent : baseEnd_155264 < baseStart_155264 := by decide
  rcases family_descends (prefixWord ++ tailWord_155264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155317 : List Nat := [1, 3, 3, 3, 2, 2, 2, 3]
def baseStart_155317 : Nat := 118140960795 + 155317 * 2 ^ 59
def prefixEnd_155317 : Nat := 4983230072969 + 3 ^ 40 * 155317 * 2
def baseEnd_155317 : Nat := 47260607297466106798943

theorem tailTrace_155317 : CollatzResearch.WordTrace tailWord_155317 prefixEnd_155317 47260607297466106798943 := by
  unfold tailWord_155317
  simp only [CollatzResearch.WordTrace]
  refine ⟨5664876378320509876864205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3776584252213673251242803 5664876378320509876864205)
  ·
    refine ⟨2124328641870191203824077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5664876378320509876864205 2124328641870191203824077)
    ·
      refine ⟨796623240701321701434029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2124328641870191203824077 796623240701321701434029)
      ·
        refine ⟨298733715262995638037761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 796623240701321701434029 298733715262995638037761)
        ·
          refine ⟨224050286447246728528321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298733715262995638037761 224050286447246728528321)
          ·
            refine ⟨168037714835435046396241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224050286447246728528321 168037714835435046396241)
            ·
              refine ⟨126028286126576284797181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168037714835435046396241 126028286126576284797181)
              ·
                refine ⟨47260607297466106798943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126028286126576284797181 47260607297466106798943)
                ·
                  rfl

theorem cell19_155317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 3].length) (baseStart_155317 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_155317 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_155317 prefixEnd_155317 := by exact prefixLift 155317
  have htrace : WordTrace (prefixWord ++ tailWord_155317) baseStart_155317 baseEnd_155317 := by
    simpa [prefixWord, tailWord_155317, baseEnd_155317] using wordTrace_append hprefix tailTrace_155317
  have hstable : (prefixWord ++ tailWord_155317).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155317).length < 2 ^ (prefixWord ++ tailWord_155317).sum := by decide
  have hdescent : baseEnd_155317 < baseStart_155317 := by decide
  rcases family_descends (prefixWord ++ tailWord_155317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155319 : List Nat := [1, 1, 3, 1, 5, 3, 2, 3]
def baseStart_155319 : Nat := 118140960795 + 155319 * 2 ^ 59
def prefixEnd_155319 : Nat := 4983230072969 + 3 ^ 40 * 155319 * 2
def baseEnd_155319 : Nat := 47261215867130694754493

theorem tailTrace_155319 : CollatzResearch.WordTrace tailWord_155319 prefixEnd_155319 47261215867130694754493 := by
  unfold tailWord_155319
  simp only [CollatzResearch.WordTrace]
  refine ⟨5664949324313264218437011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3776632882875509478958007 5664949324313264218437011)
  ·
    refine ⟨8497423986469896327655517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5664949324313264218437011 8497423986469896327655517)
    ·
      refine ⟨3186533994926211122870819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8497423986469896327655517 3186533994926211122870819)
      ·
        refine ⟨4779800992389316684306229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3186533994926211122870819 4779800992389316684306229)
        ·
          refine ⟨448106343036498439153709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4779800992389316684306229 448106343036498439153709)
          ·
            refine ⟨168039878638686914682641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 448106343036498439153709 168039878638686914682641)
            ·
              refine ⟨126029908979015186011981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168039878638686914682641 126029908979015186011981)
              ·
                refine ⟨47261215867130694754493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126029908979015186011981 47261215867130694754493)
                ·
                  rfl

theorem cell19_155319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 3].length) (baseStart_155319 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_155319 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_155319 prefixEnd_155319 := by exact prefixLift 155319
  have htrace : WordTrace (prefixWord ++ tailWord_155319) baseStart_155319 baseEnd_155319 := by
    simpa [prefixWord, tailWord_155319, baseEnd_155319] using wordTrace_append hprefix tailTrace_155319
  have hstable : (prefixWord ++ tailWord_155319).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155319).length < 2 ^ (prefixWord ++ tailWord_155319).sum := by decide
  have hdescent : baseEnd_155319 < baseStart_155319 := by decide
  rcases family_descends (prefixWord ++ tailWord_155319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155321 : List Nat := [1, 2, 1, 4, 1, 1, 6, 3]
def baseStart_155321 : Nat := 118140960795 + 155321 * 2 ^ 59
def prefixEnd_155321 : Nat := 4983230072969 + 3 ^ 40 * 155321 * 2
def baseEnd_155321 : Nat := 47261824436795282710043

theorem tailTrace_155321 : CollatzResearch.WordTrace tailWord_155321 prefixEnd_155321 47261824436795282710043 := by
  unfold tailWord_155321
  simp only [CollatzResearch.WordTrace]
  refine ⟨5665022270306018560009817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3776681513537345706673211 5665022270306018560009817)
  ·
    refine ⟨4248766702729513920007363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5665022270306018560009817 4248766702729513920007363)
    ·
      refine ⟨6373150054094270880011045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4248766702729513920007363 6373150054094270880011045)
      ·
        refine ⟨1194965635142675790002071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6373150054094270880011045 1194965635142675790002071)
        ·
          refine ⟨1792448452714013685003107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1194965635142675790002071 1792448452714013685003107)
          ·
            refine ⟨2688672679071020527504661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1792448452714013685003107 2688672679071020527504661)
            ·
              refine ⟨126031531831454087226781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2688672679071020527504661 126031531831454087226781)
              ·
                refine ⟨47261824436795282710043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126031531831454087226781 47261824436795282710043)
                ·
                  rfl

theorem cell19_155321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 3].length) (baseStart_155321 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_155321 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_155321 prefixEnd_155321 := by exact prefixLift 155321
  have htrace : WordTrace (prefixWord ++ tailWord_155321) baseStart_155321 baseEnd_155321 := by
    simpa [prefixWord, tailWord_155321, baseEnd_155321] using wordTrace_append hprefix tailTrace_155321
  have hstable : (prefixWord ++ tailWord_155321).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155321).length < 2 ^ (prefixWord ++ tailWord_155321).sum := by decide
  have hdescent : baseEnd_155321 < baseStart_155321 := by decide
  rcases family_descends (prefixWord ++ tailWord_155321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155338 : List Nat := [3, 1, 2, 1, 6, 1, 5]
def baseStart_155338 : Nat := 118140960795 + 155338 * 2 ^ 59
def prefixEnd_155338 : Nat := 4983230072969 + 3 ^ 40 * 155338 * 2
def baseEnd_155338 : Nat := 15755665759648093444073

theorem tailTrace_155338 : CollatzResearch.WordTrace tailWord_155338 prefixEnd_155338 15755665759648093444073 := by
  unfold tailWord_155338
  simp only [CollatzResearch.WordTrace]
  refine ⟨1416410577811107615844667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3777094874162953642252445 1416410577811107615844667)
  ·
    refine ⟨2124615866716661423767001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1416410577811107615844667 2124615866716661423767001)
    ·
      refine ⟨1593461900037496067825251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2124615866716661423767001 1593461900037496067825251)
      ·
        refine ⟨2390192850056244101737877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1593461900037496067825251 2390192850056244101737877)
        ·
          refine ⟨112040289846386442268963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2390192850056244101737877 112040289846386442268963)
          ·
            refine ⟨168060434769579663403445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112040289846386442268963 168060434769579663403445)
            ·
              refine ⟨15755665759648093444073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 168060434769579663403445 15755665759648093444073)
              ·
                rfl

theorem cell19_155338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 5].length) (baseStart_155338 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_155338 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_155338 prefixEnd_155338 := by exact prefixLift 155338
  have htrace : WordTrace (prefixWord ++ tailWord_155338) baseStart_155338 baseEnd_155338 := by
    simpa [prefixWord, tailWord_155338, baseEnd_155338] using wordTrace_append hprefix tailTrace_155338
  have hstable : (prefixWord ++ tailWord_155338).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155338).length < 2 ^ (prefixWord ++ tailWord_155338).sum := by decide
  have hdescent : baseEnd_155338 < baseStart_155338 := by decide
  rcases family_descends (prefixWord ++ tailWord_155338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155399 : List Nat := [1, 1, 4, 4, 9]
def baseStart_155399 : Nat := 118140960795 + 155399 * 2 ^ 59
def prefixEnd_155399 : Nat := 4983230072969 + 3 ^ 40 * 155399 * 2
def baseEnd_155399 : Nat := 1751316987174600480611

theorem tailTrace_155399 : CollatzResearch.WordTrace tailWord_155399 prefixEnd_155399 1751316987174600480611 := by
  unfold tailWord_155399
  simp only [CollatzResearch.WordTrace]
  refine ⟨5667867164023437881349251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3778578109348958587566167 5667867164023437881349251)
  ·
    refine ⟨8501800746035156822023877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5667867164023437881349251 8501800746035156822023877)
    ·
      refine ⟨1594087639881591904129477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8501800746035156822023877 1594087639881591904129477)
      ·
        refine ⟨298891432477798482024277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1594087639881591904129477 298891432477798482024277)
        ·
          refine ⟨1751316987174600480611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 298891432477798482024277 1751316987174600480611)
          ·
            rfl

theorem cell19_155399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 9].length) (baseStart_155399 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_155399 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_155399 prefixEnd_155399 := by exact prefixLift 155399
  have htrace : WordTrace (prefixWord ++ tailWord_155399) baseStart_155399 baseEnd_155399 := by
    simpa [prefixWord, tailWord_155399, baseEnd_155399] using wordTrace_append hprefix tailTrace_155399
  have hstable : (prefixWord ++ tailWord_155399).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155399).length < 2 ^ (prefixWord ++ tailWord_155399).sum := by decide
  have hdescent : baseEnd_155399 < baseStart_155399 := by decide
  rcases family_descends (prefixWord ++ tailWord_155399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155454 : List Nat := [4, 2, 1, 2, 2, 2, 6]
def baseStart_155454 : Nat := 118140960795 + 155454 * 2 ^ 59
def prefixEnd_155454 : Nat := 4983230072969 + 3 ^ 40 * 155454 * 2
def baseEnd_155454 : Nat := 15767431439830127251375

theorem tailTrace_155454 : CollatzResearch.WordTrace tailWord_155454 prefixEnd_155454 15767431439830127251375 := by
  unfold tailWord_155454
  simp only [CollatzResearch.WordTrace]
  refine ⟨708734147353022784325177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3779915452549454849734277 708734147353022784325177)
  ·
    refine ⟨531550610514767088243883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 708734147353022784325177 531550610514767088243883)
    ·
      refine ⟨797325915772150632365825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 531550610514767088243883 797325915772150632365825)
      ·
        refine ⟨597994436829112974274369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 797325915772150632365825 597994436829112974274369)
        ·
          refine ⟨448495827621834730705777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 597994436829112974274369 448495827621834730705777)
          ·
            refine ⟨336371870716376048029333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 448495827621834730705777 336371870716376048029333)
            ·
              refine ⟨15767431439830127251375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 336371870716376048029333 15767431439830127251375)
              ·
                rfl

theorem cell19_155454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 6].length) (baseStart_155454 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_155454 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_155454 prefixEnd_155454 := by exact prefixLift 155454
  have htrace : WordTrace (prefixWord ++ tailWord_155454) baseStart_155454 baseEnd_155454 := by
    simpa [prefixWord, tailWord_155454, baseEnd_155454] using wordTrace_append hprefix tailTrace_155454
  have hstable : (prefixWord ++ tailWord_155454).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155454).length < 2 ^ (prefixWord ++ tailWord_155454).sum := by decide
  have hdescent : baseEnd_155454 < baseStart_155454 := by decide
  rcases family_descends (prefixWord ++ tailWord_155454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155490 : List Nat := [3, 3, 2, 1, 2, 1, 4, 3]
def baseStart_155490 : Nat := 118140960795 + 155490 * 2 ^ 59
def prefixEnd_155490 : Nat := 4983230072969 + 3 ^ 40 * 155490 * 2
def baseEnd_155490 : Nat := 47313248573452964954027

theorem tailTrace_155490 : CollatzResearch.WordTrace tailWord_155490 prefixEnd_155490 47313248573452964954027 := by
  unfold tailWord_155490
  simp only [CollatzResearch.WordTrace]
  refine ⟨1417796551673440105727981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3780790804462506948607949 1417796551673440105727981)
  ·
    refine ⟨531673706877540039647993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1417796551673440105727981 531673706877540039647993)
    ·
      refine ⟨398755280158155029735995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 531673706877540039647993 398755280158155029735995)
      ·
        refine ⟨598132920237232544603993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398755280158155029735995 598132920237232544603993)
        ·
          refine ⟨448599690177924408452995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 598132920237232544603993 448599690177924408452995)
          ·
            refine ⟨672899535266886612679493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 448599690177924408452995 672899535266886612679493)
            ·
              refine ⟨126168662862541239877405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 672899535266886612679493 126168662862541239877405)
              ·
                refine ⟨47313248573452964954027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126168662862541239877405 47313248573452964954027)
                ·
                  rfl

theorem cell19_155490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 3].length) (baseStart_155490 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_155490 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_155490 prefixEnd_155490 := by exact prefixLift 155490
  have htrace : WordTrace (prefixWord ++ tailWord_155490) baseStart_155490 baseEnd_155490 := by
    simpa [prefixWord, tailWord_155490, baseEnd_155490] using wordTrace_append hprefix tailTrace_155490
  have hstable : (prefixWord ++ tailWord_155490).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155490).length < 2 ^ (prefixWord ++ tailWord_155490).sum := by decide
  have hdescent : baseEnd_155490 < baseStart_155490 := by decide
  rcases family_descends (prefixWord ++ tailWord_155490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155492 : List Nat := [2, 3, 1, 1, 5, 1, 1, 5]
def baseStart_155492 : Nat := 118140960795 + 155492 * 2 ^ 59
def prefixEnd_155492 : Nat := 4983230072969 + 3 ^ 40 * 155492 * 2
def baseEnd_155492 : Nat := 47313857143117552909577

theorem tailTrace_155492 : CollatzResearch.WordTrace tailWord_155492 prefixEnd_155492 47313857143117552909577 := by
  unfold tailWord_155492
  simp only [CollatzResearch.WordTrace]
  refine ⟨2835629576343257382242365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3780839435124343176323153 2835629576343257382242365)
  ·
    refine ⟨1063361091128721518340887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2835629576343257382242365 1063361091128721518340887)
    ·
      refine ⟨1595041636693082277511331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1063361091128721518340887 1595041636693082277511331)
      ·
        refine ⟨2392562455039623416266997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1595041636693082277511331 2392562455039623416266997)
        ·
          refine ⟨224302730159964695275031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2392562455039623416266997 224302730159964695275031)
          ·
            refine ⟨336454095239947042912547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224302730159964695275031 336454095239947042912547)
            ·
              refine ⟨504681142859920564368821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336454095239947042912547 504681142859920564368821)
              ·
                refine ⟨47313857143117552909577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 504681142859920564368821 47313857143117552909577)
                ·
                  rfl

theorem cell19_155492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 5].length) (baseStart_155492 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_155492 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_155492 prefixEnd_155492 := by exact prefixLift 155492
  have htrace : WordTrace (prefixWord ++ tailWord_155492) baseStart_155492 baseEnd_155492 := by
    simpa [prefixWord, tailWord_155492, baseEnd_155492] using wordTrace_append hprefix tailTrace_155492
  have hstable : (prefixWord ++ tailWord_155492).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155492).length < 2 ^ (prefixWord ++ tailWord_155492).sum := by decide
  have hdescent : baseEnd_155492 < baseStart_155492 := by decide
  rcases family_descends (prefixWord ++ tailWord_155492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155566 : List Nat := [4, 1, 5, 1, 8]
def baseStart_155566 : Nat := 118140960795 + 155566 * 2 ^ 59
def prefixEnd_155566 : Nat := 4983230072969 + 3 ^ 40 * 155566 * 2
def baseEnd_155566 : Nat := 1753199045211381750553

theorem tailTrace_155566 : CollatzResearch.WordTrace tailWord_155566 prefixEnd_155566 1753199045211381750553 := by
  unfold tailWord_155566
  simp only [CollatzResearch.WordTrace]
  refine ⟨709244769302303175334819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3782638769612283601785701 709244769302303175334819)
  ·
    refine ⟨1063867153953454763002229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 709244769302303175334819 1063867153953454763002229)
    ·
      refine ⟨99737545683136384031459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1063867153953454763002229 99737545683136384031459)
      ·
        refine ⟨149606318524704576047189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99737545683136384031459 149606318524704576047189)
        ·
          refine ⟨1753199045211381750553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 149606318524704576047189 1753199045211381750553)
          ·
            rfl

theorem cell19_155566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 8].length) (baseStart_155566 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_155566 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_155566 prefixEnd_155566 := by exact prefixLift 155566
  have htrace : WordTrace (prefixWord ++ tailWord_155566) baseStart_155566 baseEnd_155566 := by
    simpa [prefixWord, tailWord_155566, baseEnd_155566] using wordTrace_append hprefix tailTrace_155566
  have hstable : (prefixWord ++ tailWord_155566).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155566).length < 2 ^ (prefixWord ++ tailWord_155566).sum := by decide
  have hdescent : baseEnd_155566 < baseStart_155566 := by decide
  rcases family_descends (prefixWord ++ tailWord_155566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155760 : List Nat := [2, 1, 1, 1, 5, 2, 3, 4]
def baseStart_155760 : Nat := 118140960795 + 155760 * 2 ^ 59
def prefixEnd_155760 : Nat := 4983230072969 + 3 ^ 40 * 155760 * 2
def baseEnd_155760 : Nat := 47395405478172338953291

theorem tailTrace_155760 : CollatzResearch.WordTrace tailWord_155760 prefixEnd_155760 47395405478172338953291 := by
  unfold tailWord_155760
  simp only [CollatzResearch.WordTrace]
  refine ⟨2840516957857798267620367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3787355943810397690160489 2840516957857798267620367)
  ·
    refine ⟨4260775436786697401430551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2840516957857798267620367 4260775436786697401430551)
    ·
      refine ⟨6391163155180046102145827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4260775436786697401430551 6391163155180046102145827)
      ·
        refine ⟨9586744732770069153218741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6391163155180046102145827 9586744732770069153218741)
        ·
          refine ⟨898757318697193983114257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9586744732770069153218741 898757318697193983114257)
          ·
            refine ⟨674067989022895487335693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 898757318697193983114257 674067989022895487335693)
            ·
              refine ⟨252775495883585807750885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 674067989022895487335693 252775495883585807750885)
              ·
                refine ⟨47395405478172338953291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 252775495883585807750885 47395405478172338953291)
                ·
                  rfl

theorem cell19_155760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 4].length) (baseStart_155760 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_155760 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_155760 prefixEnd_155760 := by exact prefixLift 155760
  have htrace : WordTrace (prefixWord ++ tailWord_155760) baseStart_155760 baseEnd_155760 := by
    simpa [prefixWord, tailWord_155760, baseEnd_155760] using wordTrace_append hprefix tailTrace_155760
  have hstable : (prefixWord ++ tailWord_155760).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155760).length < 2 ^ (prefixWord ++ tailWord_155760).sum := by decide
  have hdescent : baseEnd_155760 < baseStart_155760 := by decide
  rcases family_descends (prefixWord ++ tailWord_155760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155857 : List Nat := [1, 2, 2, 1, 2, 2, 9]
def baseStart_155857 : Nat := 118140960795 + 155857 * 2 ^ 59
def prefixEnd_155857 : Nat := 4983230072969 + 3 ^ 40 * 155857 * 2
def baseEnd_155857 : Nat := 15808307035634951599157

theorem tailTrace_155857 : CollatzResearch.WordTrace tailWord_155857 prefixEnd_155857 15808307035634951599157 := by
  unfold tailWord_155857
  simp only [CollatzResearch.WordTrace]
  refine ⟨5684571796364182101521825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3789714530909454734347883 5684571796364182101521825)
  ·
    refine ⟨4263428847273136576141369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5684571796364182101521825 4263428847273136576141369)
    ·
      refine ⟨3197571635454852432106027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4263428847273136576141369 3197571635454852432106027)
      ·
        refine ⟨4796357453182278648159041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3197571635454852432106027 4796357453182278648159041)
        ·
          refine ⟨3597268089886708986119281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4796357453182278648159041 3597268089886708986119281)
          ·
            refine ⟨2697951067415031739589461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3597268089886708986119281 2697951067415031739589461)
            ·
              refine ⟨15808307035634951599157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2697951067415031739589461 15808307035634951599157)
              ·
                rfl

theorem cell19_155857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 9].length) (baseStart_155857 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_155857 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_155857 prefixEnd_155857 := by exact prefixLift 155857
  have htrace : WordTrace (prefixWord ++ tailWord_155857) baseStart_155857 baseEnd_155857 := by
    simpa [prefixWord, tailWord_155857, baseEnd_155857] using wordTrace_append hprefix tailTrace_155857
  have hstable : (prefixWord ++ tailWord_155857).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155857).length < 2 ^ (prefixWord ++ tailWord_155857).sum := by decide
  have hdescent : baseEnd_155857 < baseStart_155857 := by decide
  rcases family_descends (prefixWord ++ tailWord_155857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155946 : List Nat := [3, 1, 4, 2, 2, 1, 3, 3]
def baseStart_155946 : Nat := 118140960795 + 155946 * 2 ^ 59
def prefixEnd_155946 : Nat := 4983230072969 + 3 ^ 40 * 155946 * 2
def baseEnd_155946 : Nat := 47452002456979018819451

theorem tailTrace_155946 : CollatzResearch.WordTrace tailWord_155946 prefixEnd_155946 47452002456979018819451 := by
  unfold tailWord_155946
  simp only [CollatzResearch.WordTrace]
  refine ⟨1421954473260437575377923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3791878595361166867674461 1421954473260437575377923)
  ·
    refine ⟨2132931709890656363066885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1421954473260437575377923 2132931709890656363066885)
    ·
      refine ⟨399924695604498068075041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2132931709890656363066885 399924695604498068075041)
      ·
        refine ⟨299943521703373551056281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 399924695604498068075041 299943521703373551056281)
        ·
          refine ⟨224957641277530163292211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 299943521703373551056281 224957641277530163292211)
          ·
            refine ⟨337436461916295244938317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224957641277530163292211 337436461916295244938317)
            ·
              refine ⟨126538673218610716851869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 337436461916295244938317 126538673218610716851869)
              ·
                refine ⟨47452002456979018819451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126538673218610716851869 47452002456979018819451)
                ·
                  rfl

theorem cell19_155946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 3].length) (baseStart_155946 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_155946 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_155946 prefixEnd_155946 := by exact prefixLift 155946
  have htrace : WordTrace (prefixWord ++ tailWord_155946) baseStart_155946 baseEnd_155946 := by
    simpa [prefixWord, tailWord_155946, baseEnd_155946] using wordTrace_append hprefix tailTrace_155946
  have hstable : (prefixWord ++ tailWord_155946).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155946).length < 2 ^ (prefixWord ++ tailWord_155946).sum := by decide
  have hdescent : baseEnd_155946 < baseStart_155946 := by decide
  rcases family_descends (prefixWord ++ tailWord_155946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156005 : List Nat := [1, 3, 1, 3, 1, 5, 2, 3]
def baseStart_156005 : Nat := 118140960795 + 156005 * 2 ^ 59
def prefixEnd_156005 : Nat := 4983230072969 + 3 ^ 40 * 156005 * 2
def baseEnd_156005 : Nat := 47469955262084363508179

theorem tailTrace_156005 : CollatzResearch.WordTrace tailWord_156005 prefixEnd_156005 47469955262084363508179 := by
  unfold tailWord_156005
  simp only [CollatzResearch.WordTrace]
  refine ⟨5689969799828003377909469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3793313199885335585272979 5689969799828003377909469)
  ·
    refine ⟨2133738674935501266716051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5689969799828003377909469 2133738674935501266716051)
    ·
      refine ⟨3200608012403251900074077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2133738674935501266716051 3200608012403251900074077)
      ·
        refine ⟨1200228004651219462527779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3200608012403251900074077 1200228004651219462527779)
        ·
          refine ⟨1800342006976829193791669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1200228004651219462527779 1800342006976829193791669)
          ·
            refine ⟨168782063154077736917969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1800342006976829193791669 168782063154077736917969)
            ·
              refine ⟨126586547365558302688477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168782063154077736917969 126586547365558302688477)
              ·
                refine ⟨47469955262084363508179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126586547365558302688477 47469955262084363508179)
                ·
                  rfl

theorem cell19_156005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 3].length) (baseStart_156005 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_156005 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_156005 prefixEnd_156005 := by exact prefixLift 156005
  have htrace : WordTrace (prefixWord ++ tailWord_156005) baseStart_156005 baseEnd_156005 := by
    simpa [prefixWord, tailWord_156005, baseEnd_156005] using wordTrace_append hprefix tailTrace_156005
  have hstable : (prefixWord ++ tailWord_156005).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156005).length < 2 ^ (prefixWord ++ tailWord_156005).sum := by decide
  have hdescent : baseEnd_156005 < baseStart_156005 := by decide
  rcases family_descends (prefixWord ++ tailWord_156005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156007 : List Nat := [1, 1, 5, 1, 3, 2, 1, 5]
def baseStart_156007 : Nat := 118140960795 + 156007 * 2 ^ 59
def prefixEnd_156007 : Nat := 4983230072969 + 3 ^ 40 * 156007 * 2
def baseEnd_156007 : Nat := 47470563831748951463729

theorem tailTrace_156007 : CollatzResearch.WordTrace tailWord_156007 prefixEnd_156007 47470563831748951463729 := by
  unfold tailWord_156007
  simp only [CollatzResearch.WordTrace]
  refine ⟨5690042745820757719482275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3793361830547171812988183 5690042745820757719482275)
  ·
    refine ⟨8535064118731136579223413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5690042745820757719482275 8535064118731136579223413)
    ·
      refine ⟨800162261131044054302195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8535064118731136579223413 800162261131044054302195)
      ·
        refine ⟨1200243391696566081453293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 800162261131044054302195 1200243391696566081453293)
        ·
          refine ⟨450091271886212280544985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1200243391696566081453293 450091271886212280544985)
          ·
            refine ⟨337568453914659210408739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 450091271886212280544985 337568453914659210408739)
            ·
              refine ⟨506352680871988815613109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 337568453914659210408739 506352680871988815613109)
              ·
                refine ⟨47470563831748951463729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 506352680871988815613109 47470563831748951463729)
                ·
                  rfl

theorem cell19_156007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 5].length) (baseStart_156007 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_156007 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_156007 prefixEnd_156007 := by exact prefixLift 156007
  have htrace : WordTrace (prefixWord ++ tailWord_156007) baseStart_156007 baseEnd_156007 := by
    simpa [prefixWord, tailWord_156007, baseEnd_156007] using wordTrace_append hprefix tailTrace_156007
  have hstable : (prefixWord ++ tailWord_156007).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156007).length < 2 ^ (prefixWord ++ tailWord_156007).sum := by decide
  have hdescent : baseEnd_156007 < baseStart_156007 := by decide
  rcases family_descends (prefixWord ++ tailWord_156007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156009 : List Nat := [1, 2, 1, 1, 1, 3, 5, 5]
def baseStart_156009 : Nat := 118140960795 + 156009 * 2 ^ 59
def prefixEnd_156009 : Nat := 4983230072969 + 3 ^ 40 * 156009 * 2
def baseEnd_156009 : Nat := 47471172401413539419279

theorem tailTrace_156009 : CollatzResearch.WordTrace tailWord_156009 prefixEnd_156009 47471172401413539419279 := by
  unfold tailWord_156009
  simp only [CollatzResearch.WordTrace]
  refine ⟨5690115691813512061055081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3793410461209008040703387 5690115691813512061055081)
  ·
    refine ⟨4267586768860134045791311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5690115691813512061055081 4267586768860134045791311)
    ·
      refine ⟨6401380153290201068686967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4267586768860134045791311 6401380153290201068686967)
      ·
        refine ⟨9602070229935301603030451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6401380153290201068686967 9602070229935301603030451)
        ·
          refine ⟨14403105344902952404545677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9602070229935301603030451 14403105344902952404545677)
          ·
            refine ⟨5401164504338607151704629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14403105344902952404545677 5401164504338607151704629)
            ·
              refine ⟨506359172281744420472309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5401164504338607151704629 506359172281744420472309)
              ·
                refine ⟨47471172401413539419279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 506359172281744420472309 47471172401413539419279)
                ·
                  rfl

theorem cell19_156009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 5].length) (baseStart_156009 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_156009 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_156009 prefixEnd_156009 := by exact prefixLift 156009
  have htrace : WordTrace (prefixWord ++ tailWord_156009) baseStart_156009 baseEnd_156009 := by
    simpa [prefixWord, tailWord_156009, baseEnd_156009] using wordTrace_append hprefix tailTrace_156009
  have hstable : (prefixWord ++ tailWord_156009).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156009).length < 2 ^ (prefixWord ++ tailWord_156009).sum := by decide
  have hdescent : baseEnd_156009 < baseStart_156009 := by decide
  rcases family_descends (prefixWord ++ tailWord_156009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156022 : List Nat := [5, 1, 1, 4, 1, 2, 5]
def baseStart_156022 : Nat := 118140960795 + 156022 * 2 ^ 59
def prefixEnd_156022 : Nat := 4983230072969 + 3 ^ 40 * 156022 * 2
def baseEnd_156022 : Nat := 15825042701411120376785

theorem tailTrace_156022 : CollatzResearch.WordTrace tailWord_156022 prefixEnd_156022 15825042701411120376785 := by
  unfold tailWord_156022
  simp only [CollatzResearch.WordTrace]
  refine ⟨355661865047900955079895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3793726560510943520852213 355661865047900955079895)
  ·
    refine ⟨533492797571851432619843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 355661865047900955079895 533492797571851432619843)
    ·
      refine ⟨800239196357777148929765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 533492797571851432619843 800239196357777148929765)
      ·
        refine ⟨150044849317083215424331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 800239196357777148929765 150044849317083215424331)
        ·
          refine ⟨225067273975624823136497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150044849317083215424331 225067273975624823136497)
          ·
            refine ⟨168800455481718617352373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225067273975624823136497 168800455481718617352373)
            ·
              refine ⟨15825042701411120376785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 168800455481718617352373 15825042701411120376785)
              ·
                rfl

theorem cell19_156022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 5].length) (baseStart_156022 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_156022 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_156022 prefixEnd_156022 := by exact prefixLift 156022
  have htrace : WordTrace (prefixWord ++ tailWord_156022) baseStart_156022 baseEnd_156022 := by
    simpa [prefixWord, tailWord_156022, baseEnd_156022] using wordTrace_append hprefix tailTrace_156022
  have hstable : (prefixWord ++ tailWord_156022).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156022).length < 2 ^ (prefixWord ++ tailWord_156022).sum := by decide
  have hdescent : baseEnd_156022 < baseStart_156022 := by decide
  rcases family_descends (prefixWord ++ tailWord_156022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156062 : List Nat := [4, 3, 1, 2, 1, 1, 2, 5]
def baseStart_156062 : Nat := 118140960795 + 156062 * 2 ^ 59
def prefixEnd_156062 : Nat := 4983230072969 + 3 ^ 40 * 156062 * 2
def baseEnd_156062 : Nat := 47487299497525120241357

theorem tailTrace_156062 : CollatzResearch.WordTrace tailWord_156062 prefixEnd_156062 47487299497525120241357 := by
  unfold tailWord_156062
  simp only [CollatzResearch.WordTrace]
  refine ⟨711506095077687764091805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3794699173747668075156293 711506095077687764091805)
  ·
    refine ⟨266814785654132911534427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 711506095077687764091805 266814785654132911534427)
    ·
      refine ⟨400222178481199367301641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266814785654132911534427 400222178481199367301641)
      ·
        refine ⟨300166633860899525476231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 400222178481199367301641 300166633860899525476231)
        ·
          refine ⟨450249950791349288214347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300166633860899525476231 450249950791349288214347)
          ·
            refine ⟨675374926187023932321521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450249950791349288214347 675374926187023932321521)
            ·
              refine ⟨506531194640267949241141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 675374926187023932321521 506531194640267949241141)
              ·
                refine ⟨47487299497525120241357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 506531194640267949241141 47487299497525120241357)
                ·
                  rfl

theorem cell19_156062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_156062 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_156062 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_156062 prefixEnd_156062 := by exact prefixLift 156062
  have htrace : WordTrace (prefixWord ++ tailWord_156062) baseStart_156062 baseEnd_156062 := by
    simpa [prefixWord, tailWord_156062, baseEnd_156062] using wordTrace_append hprefix tailTrace_156062
  have hstable : (prefixWord ++ tailWord_156062).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156062).length < 2 ^ (prefixWord ++ tailWord_156062).sum := by decide
  have hdescent : baseEnd_156062 < baseStart_156062 := by decide
  rcases family_descends (prefixWord ++ tailWord_156062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156085 : List Nat := [1, 3, 3, 2, 10]
def baseStart_156085 : Nat := 118140960795 + 156085 * 2 ^ 59
def prefixEnd_156085 : Nat := 4983230072969 + 3 ^ 40 * 156085 * 2
def baseEnd_156085 : Nat := 1759048075876588212229

theorem tailTrace_156085 : CollatzResearch.WordTrace tailWord_156085 prefixEnd_156085 1759048075876588212229 := by
  unfold tailWord_156085
  simp only [CollatzResearch.WordTrace]
  refine ⟨5692887639538177040821709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3795258426358784693881139 5692887639538177040821709)
  ·
    refine ⟨2134832864826816390308141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5692887639538177040821709 2134832864826816390308141)
    ·
      refine ⟨800562324310056146365553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2134832864826816390308141 800562324310056146365553)
      ·
        refine ⟨600421743232542109774165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 800562324310056146365553 600421743232542109774165)
        ·
          refine ⟨1759048075876588212229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 600421743232542109774165 1759048075876588212229)
          ·
            rfl

theorem cell19_156085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 10].length) (baseStart_156085 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_156085 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_156085 prefixEnd_156085 := by exact prefixLift 156085
  have htrace : WordTrace (prefixWord ++ tailWord_156085) baseStart_156085 baseEnd_156085 := by
    simpa [prefixWord, tailWord_156085, baseEnd_156085] using wordTrace_append hprefix tailTrace_156085
  have hstable : (prefixWord ++ tailWord_156085).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156085).length < 2 ^ (prefixWord ++ tailWord_156085).sum := by decide
  have hdescent : baseEnd_156085 < baseStart_156085 := by decide
  rcases family_descends (prefixWord ++ tailWord_156085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156121 : List Nat := [1, 2, 1, 2, 4, 1, 5, 3]
def baseStart_156121 : Nat := 118140960795 + 156121 * 2 ^ 59
def prefixEnd_156121 : Nat := 4983230072969 + 3 ^ 40 * 156121 * 2
def baseEnd_156121 : Nat := 47505252302630464930085

theorem tailTrace_156121 : CollatzResearch.WordTrace tailWord_156121 prefixEnd_156121 47505252302630464930085 := by
  unfold tailWord_156121
  simp only [CollatzResearch.WordTrace]
  refine ⟨5694200667407755189132217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3796133778271836792754811 5694200667407755189132217)
  ·
    refine ⟨4270650500555816391849163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5694200667407755189132217 4270650500555816391849163)
    ·
      refine ⟨6405975750833724587773745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4270650500555816391849163 6405975750833724587773745)
      ·
        refine ⟨4804481813125293440830309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6405975750833724587773745 4804481813125293440830309)
        ·
          refine ⟨900840339960992520155683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4804481813125293440830309 900840339960992520155683)
          ·
            refine ⟨1351260509941488780233525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 900840339960992520155683 1351260509941488780233525)
            ·
              refine ⟨126680672807014573146893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1351260509941488780233525 126680672807014573146893)
              ·
                refine ⟨47505252302630464930085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126680672807014573146893 47505252302630464930085)
                ·
                  rfl

theorem cell19_156121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 3].length) (baseStart_156121 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_156121 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_156121 prefixEnd_156121 := by exact prefixLift 156121
  have htrace : WordTrace (prefixWord ++ tailWord_156121) baseStart_156121 baseEnd_156121 := by
    simpa [prefixWord, tailWord_156121, baseEnd_156121] using wordTrace_append hprefix tailTrace_156121
  have hstable : (prefixWord ++ tailWord_156121).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156121).length < 2 ^ (prefixWord ++ tailWord_156121).sum := by decide
  have hdescent : baseEnd_156121 < baseStart_156121 := by decide
  rcases family_descends (prefixWord ++ tailWord_156121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156212 : List Nat := [2, 5, 1, 3, 1, 1, 2, 4]
def baseStart_156212 : Nat := 118140960795 + 156212 * 2 ^ 59
def prefixEnd_156212 : Nat := 4983230072969 + 3 ^ 40 * 156212 * 2
def baseEnd_156212 : Nat := 47532942222369216907615

theorem tailTrace_156212 : CollatzResearch.WordTrace tailWord_156212 prefixEnd_156212 47532942222369216907615 := by
  unfold tailWord_156212
  simp only [CollatzResearch.WordTrace]
  refine ⟨2848759855039038865347445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3798346473385385153796593 2848759855039038865347445)
  ·
    refine ⟨267071236409909893626323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2848759855039038865347445 267071236409909893626323)
    ·
      refine ⟨400606854614864840439485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267071236409909893626323 400606854614864840439485)
      ·
        refine ⟨150227570480574315164807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 400606854614864840439485 150227570480574315164807)
        ·
          refine ⟨225341355720861472747211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150227570480574315164807 225341355720861472747211)
          ·
            refine ⟨338012033581292209120817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225341355720861472747211 338012033581292209120817)
            ·
              refine ⟨253509025185969156840613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 338012033581292209120817 253509025185969156840613)
              ·
                refine ⟨47532942222369216907615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 253509025185969156840613 47532942222369216907615)
                ·
                  rfl

theorem cell19_156212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 4].length) (baseStart_156212 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_156212 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_156212 prefixEnd_156212 := by exact prefixLift 156212
  have htrace : WordTrace (prefixWord ++ tailWord_156212) baseStart_156212 baseEnd_156212 := by
    simpa [prefixWord, tailWord_156212, baseEnd_156212] using wordTrace_append hprefix tailTrace_156212
  have hstable : (prefixWord ++ tailWord_156212).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156212).length < 2 ^ (prefixWord ++ tailWord_156212).sum := by decide
  have hdescent : baseEnd_156212 < baseStart_156212 := by decide
  rcases family_descends (prefixWord ++ tailWord_156212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156214 : List Nat := [5, 1, 2, 1, 2, 2, 2, 4]
def baseStart_156214 : Nat := 118140960795 + 156214 * 2 ^ 59
def prefixEnd_156214 : Nat := 4983230072969 + 3 ^ 40 * 156214 * 2
def baseEnd_156214 : Nat := 47533550792033804863165

theorem tailTrace_156214 : CollatzResearch.WordTrace tailWord_156214 prefixEnd_156214 47533550792033804863165 := by
  unfold tailWord_156214
  simp only [CollatzResearch.WordTrace]
  refine ⟨356099541004427004516731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3798395104047221381511797 356099541004427004516731)
  ·
    refine ⟨534149311506640506775097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 356099541004427004516731 534149311506640506775097)
    ·
      refine ⟨400611983629980380081323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 534149311506640506775097 400611983629980380081323)
      ·
        refine ⟨600917975444970570121985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400611983629980380081323 600917975444970570121985)
        ·
          refine ⟨450688481583727927591489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 600917975444970570121985 450688481583727927591489)
          ·
            refine ⟨338016361187795945693617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 450688481583727927591489 338016361187795945693617)
            ·
              refine ⟨253512270890846959270213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 338016361187795945693617 253512270890846959270213)
              ·
                refine ⟨47533550792033804863165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 253512270890846959270213 47533550792033804863165)
                ·
                  rfl

theorem cell19_156214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_156214 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_156214 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_156214 prefixEnd_156214 := by exact prefixLift 156214
  have htrace : WordTrace (prefixWord ++ tailWord_156214) baseStart_156214 baseEnd_156214 := by
    simpa [prefixWord, tailWord_156214, baseEnd_156214] using wordTrace_append hprefix tailTrace_156214
  have hstable : (prefixWord ++ tailWord_156214).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156214).length < 2 ^ (prefixWord ++ tailWord_156214).sum := by decide
  have hdescent : baseEnd_156214 < baseStart_156214 := by decide
  rcases family_descends (prefixWord ++ tailWord_156214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156218 : List Nat := [3, 1, 1, 1, 3, 3, 1, 6]
def baseStart_156218 : Nat := 118140960795 + 156218 * 2 ^ 59
def prefixEnd_156218 : Nat := 4983230072969 + 3 ^ 40 * 156218 * 2
def baseEnd_156218 : Nat := 47534767931362980774265

theorem tailTrace_156218 : CollatzResearch.WordTrace tailWord_156218 prefixEnd_156218 47534767931362980774265 := by
  unfold tailWord_156218
  simp only [CollatzResearch.WordTrace]
  refine ⟨1424434637014085188853327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3798492365370893836942205 1424434637014085188853327)
  ·
    refine ⟨2136651955521127783279991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1424434637014085188853327 2136651955521127783279991)
    ·
      refine ⟨3204977933281691674919987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2136651955521127783279991 3204977933281691674919987)
      ·
        refine ⟨4807466899922537512379981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3204977933281691674919987 4807466899922537512379981)
        ·
          refine ⟨1802800087470951567142493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4807466899922537512379981 1802800087470951567142493)
          ·
            refine ⟨676050032801606837678435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1802800087470951567142493 676050032801606837678435)
            ·
              refine ⟨1014075049202410256517653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 676050032801606837678435 1014075049202410256517653)
              ·
                refine ⟨47534767931362980774265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1014075049202410256517653 47534767931362980774265)
                ·
                  rfl

theorem cell19_156218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_156218 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_156218 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_156218 prefixEnd_156218 := by exact prefixLift 156218
  have htrace : WordTrace (prefixWord ++ tailWord_156218) baseStart_156218 baseEnd_156218 := by
    simpa [prefixWord, tailWord_156218, baseEnd_156218] using wordTrace_append hprefix tailTrace_156218
  have hstable : (prefixWord ++ tailWord_156218).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156218).length < 2 ^ (prefixWord ++ tailWord_156218).sum := by decide
  have hdescent : baseEnd_156218 < baseStart_156218 := by decide
  rcases family_descends (prefixWord ++ tailWord_156218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156349 : List Nat := [1, 4, 1, 2, 1, 3, 4, 3]
def baseStart_156349 : Nat := 118140960795 + 156349 * 2 ^ 59
def prefixEnd_156349 : Nat := 4983230072969 + 3 ^ 40 * 156349 * 2
def baseEnd_156349 : Nat := 47574629244393491862797

theorem tailTrace_156349 : CollatzResearch.WordTrace tailWord_156349 prefixEnd_156349 47574629244393491862797 := by
  unfold tailWord_156349
  simp only [CollatzResearch.WordTrace]
  refine ⟨5702516510581750128432101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3801677673721166752288067 5702516510581750128432101)
  ·
    refine ⟨1069221845734078149081019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5702516510581750128432101 1069221845734078149081019)
    ·
      refine ⟨1603832768601117223621529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1069221845734078149081019 1603832768601117223621529)
      ·
        refine ⟨1202874576450837917716147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1603832768601117223621529 1202874576450837917716147)
        ·
          refine ⟨1804311864676256876574221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1202874576450837917716147 1804311864676256876574221)
          ·
            refine ⟨676616949253596328715333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1804311864676256876574221 676616949253596328715333)
            ·
              refine ⟨126865677985049311634125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 676616949253596328715333 126865677985049311634125)
              ·
                refine ⟨47574629244393491862797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126865677985049311634125 47574629244393491862797)
                ·
                  rfl

theorem cell19_156349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 3].length) (baseStart_156349 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_156349 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_156349 prefixEnd_156349 := by exact prefixLift 156349
  have htrace : WordTrace (prefixWord ++ tailWord_156349) baseStart_156349 baseEnd_156349 := by
    simpa [prefixWord, tailWord_156349, baseEnd_156349] using wordTrace_append hprefix tailTrace_156349
  have hstable : (prefixWord ++ tailWord_156349).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156349).length < 2 ^ (prefixWord ++ tailWord_156349).sum := by decide
  have hdescent : baseEnd_156349 < baseStart_156349 := by decide
  rcases family_descends (prefixWord ++ tailWord_156349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156351 : List Nat := [1, 1, 2, 2, 2, 5, 1, 5]
def baseStart_156351 : Nat := 118140960795 + 156351 * 2 ^ 59
def prefixEnd_156351 : Nat := 4983230072969 + 3 ^ 40 * 156351 * 2
def baseEnd_156351 : Nat := 47575237814058079818347

theorem tailTrace_156351 : CollatzResearch.WordTrace tailWord_156351 prefixEnd_156351 47575237814058079818347 := by
  unfold tailWord_156351
  simp only [CollatzResearch.WordTrace]
  refine ⟨5702589456574504470004907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3801726304383002980003271 5702589456574504470004907)
  ·
    refine ⟨8553884184861756705007361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5702589456574504470004907 8553884184861756705007361)
    ·
      refine ⟨6415413138646317528755521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8553884184861756705007361 6415413138646317528755521)
      ·
        refine ⟨4811559853984738146566641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6415413138646317528755521 4811559853984738146566641)
        ·
          refine ⟨3608669890488553609924981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4811559853984738146566641 3608669890488553609924981)
          ·
            refine ⟨338312802233301900930467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3608669890488553609924981 338312802233301900930467)
            ·
              refine ⟨507469203349952851395701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 338312802233301900930467 507469203349952851395701)
              ·
                refine ⟨47575237814058079818347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 507469203349952851395701 47575237814058079818347)
                ·
                  rfl

theorem cell19_156351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 5].length) (baseStart_156351 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_156351 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_156351 prefixEnd_156351 := by exact prefixLift 156351
  have htrace : WordTrace (prefixWord ++ tailWord_156351) baseStart_156351 baseEnd_156351 := by
    simpa [prefixWord, tailWord_156351, baseEnd_156351] using wordTrace_append hprefix tailTrace_156351
  have hstable : (prefixWord ++ tailWord_156351).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156351).length < 2 ^ (prefixWord ++ tailWord_156351).sum := by decide
  have hdescent : baseEnd_156351 < baseStart_156351 := by decide
  rcases family_descends (prefixWord ++ tailWord_156351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156387 : List Nat := [1, 1, 1, 7, 1, 2, 2, 4]
def baseStart_156387 : Nat := 118140960795 + 156387 * 2 ^ 59
def prefixEnd_156387 : Nat := 4983230072969 + 3 ^ 40 * 156387 * 2
def baseEnd_156387 : Nat := 47586192068020663018249

theorem tailTrace_156387 : CollatzResearch.WordTrace tailWord_156387 prefixEnd_156387 47586192068020663018249 := by
  unfold tailWord_156387
  simp only [CollatzResearch.WordTrace]
  refine ⟨5703902484444082618315415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3802601656296055078876943 5703902484444082618315415)
  ·
    refine ⟨8555853726666123927473123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5703902484444082618315415 8555853726666123927473123)
    ·
      refine ⟨12833780589999185891209685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8555853726666123927473123 12833780589999185891209685)
      ·
        refine ⟨300791732578105919325227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 12833780589999185891209685 300791732578105919325227)
        ·
          refine ⟨451187598867158878987841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300791732578105919325227 451187598867158878987841)
          ·
            refine ⟨338390699150369159240881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 451187598867158878987841 338390699150369159240881)
            ·
              refine ⟨253793024362776869430661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 338390699150369159240881 253793024362776869430661)
              ·
                refine ⟨47586192068020663018249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 253793024362776869430661 47586192068020663018249)
                ·
                  rfl

theorem cell19_156387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 4].length) (baseStart_156387 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_156387 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_156387 prefixEnd_156387 := by exact prefixLift 156387
  have htrace : WordTrace (prefixWord ++ tailWord_156387) baseStart_156387 baseEnd_156387 := by
    simpa [prefixWord, tailWord_156387, baseEnd_156387] using wordTrace_append hprefix tailTrace_156387
  have hstable : (prefixWord ++ tailWord_156387).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156387).length < 2 ^ (prefixWord ++ tailWord_156387).sum := by decide
  have hdescent : baseEnd_156387 < baseStart_156387 := by decide
  rcases family_descends (prefixWord ++ tailWord_156387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156389 : List Nat := [1, 3, 1, 4, 1, 2, 1, 6]
def baseStart_156389 : Nat := 118140960795 + 156389 * 2 ^ 59
def prefixEnd_156389 : Nat := 4983230072969 + 3 ^ 40 * 156389 * 2
def baseEnd_156389 : Nat := 47586800637685250973799

theorem tailTrace_156389 : CollatzResearch.WordTrace tailWord_156389 prefixEnd_156389 47586800637685250973799 := by
  unfold tailWord_156389
  simp only [CollatzResearch.WordTrace]
  refine ⟨5703975430436836959888221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3802650286957891306592147 5703975430436836959888221)
  ·
    refine ⟨2138990786413813859958083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5703975430436836959888221 2138990786413813859958083)
    ·
      refine ⟨3208486179620720789937125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2138990786413813859958083 3208486179620720789937125)
      ·
        refine ⟨601591158678885148113211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3208486179620720789937125 601591158678885148113211)
        ·
          refine ⟨902386738018327722169817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 601591158678885148113211 902386738018327722169817)
          ·
            refine ⟨676790053513745791627363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 902386738018327722169817 676790053513745791627363)
            ·
              refine ⟨1015185080270618687441045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 676790053513745791627363 1015185080270618687441045)
              ·
                refine ⟨47586800637685250973799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1015185080270618687441045 47586800637685250973799)
                ·
                  rfl

theorem cell19_156389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 6].length) (baseStart_156389 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_156389 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_156389 prefixEnd_156389 := by exact prefixLift 156389
  have htrace : WordTrace (prefixWord ++ tailWord_156389) baseStart_156389 baseEnd_156389 := by
    simpa [prefixWord, tailWord_156389, baseEnd_156389] using wordTrace_append hprefix tailTrace_156389
  have hstable : (prefixWord ++ tailWord_156389).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156389).length < 2 ^ (prefixWord ++ tailWord_156389).sum := by decide
  have hdescent : baseEnd_156389 < baseStart_156389 := by decide
  rcases family_descends (prefixWord ++ tailWord_156389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156444 : List Nat := [2, 2, 3, 1, 1, 5, 1, 4]
def baseStart_156444 : Nat := 118140960795 + 156444 * 2 ^ 59
def prefixEnd_156444 : Nat := 4983230072969 + 3 ^ 40 * 156444 * 2
def baseEnd_156444 : Nat := 47603536303461419751427

theorem tailTrace_156444 : CollatzResearch.WordTrace tailWord_156444 prefixEnd_156444 47603536303461419751427 := by
  unfold tailWord_156444
  simp only [CollatzResearch.WordTrace]
  refine ⟨2852990722618790676570193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3803987630158387568760257 2852990722618790676570193)
  ·
    refine ⟨2139743041964093007427645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2852990722618790676570193 2139743041964093007427645)
    ·
      refine ⟨802403640736534877785367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2139743041964093007427645 802403640736534877785367)
      ·
        refine ⟨1203605461104802316678051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 802403640736534877785367 1203605461104802316678051)
        ·
          refine ⟨1805408191657203475017077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1203605461104802316678051 1805408191657203475017077)
          ·
            refine ⟨169257017967862825782851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1805408191657203475017077 169257017967862825782851)
            ·
              refine ⟨253885526951794238674277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169257017967862825782851 253885526951794238674277)
              ·
                refine ⟨47603536303461419751427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 253885526951794238674277 47603536303461419751427)
                ·
                  rfl

theorem cell19_156444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 4].length) (baseStart_156444 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_156444 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_156444 prefixEnd_156444 := by exact prefixLift 156444
  have htrace : WordTrace (prefixWord ++ tailWord_156444) baseStart_156444 baseEnd_156444 := by
    simpa [prefixWord, tailWord_156444, baseEnd_156444] using wordTrace_append hprefix tailTrace_156444
  have hstable : (prefixWord ++ tailWord_156444).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156444).length < 2 ^ (prefixWord ++ tailWord_156444).sum := by decide
  have hdescent : baseEnd_156444 < baseStart_156444 := by decide
  rcases family_descends (prefixWord ++ tailWord_156444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156520 : List Nat := [2, 1, 4, 2, 1, 2, 4, 3]
def baseStart_156520 : Nat := 118140960795 + 156520 * 2 ^ 59
def prefixEnd_156520 : Nat := 4983230072969 + 3 ^ 40 * 156520 * 2
def baseEnd_156520 : Nat := 47626661950715762062331

theorem tailTrace_156520 : CollatzResearch.WordTrace tailWord_156520 prefixEnd_156520 47626661950715762062331 := by
  unfold tailWord_156520
  simp only [CollatzResearch.WordTrace]
  refine ⟨2854376696481123166453507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3805835595308164221938009 2854376696481123166453507)
  ·
    refine ⟨4281565044721684749680261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2854376696481123166453507 4281565044721684749680261)
    ·
      refine ⟨802793445885315890565049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4281565044721684749680261 802793445885315890565049)
      ·
        refine ⟨602095084413986917923787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 802793445885315890565049 602095084413986917923787)
        ·
          refine ⟨903142626620980376885681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 602095084413986917923787 903142626620980376885681)
          ·
            refine ⟨677356969965735282664261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 903142626620980376885681 677356969965735282664261)
            ·
              refine ⟨127004431868575365499549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 677356969965735282664261 127004431868575365499549)
              ·
                refine ⟨47626661950715762062331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127004431868575365499549 47626661950715762062331)
                ·
                  rfl

theorem cell19_156520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 3].length) (baseStart_156520 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_156520 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_156520 prefixEnd_156520 := by exact prefixLift 156520
  have htrace : WordTrace (prefixWord ++ tailWord_156520) baseStart_156520 baseEnd_156520 := by
    simpa [prefixWord, tailWord_156520, baseEnd_156520] using wordTrace_append hprefix tailTrace_156520
  have hstable : (prefixWord ++ tailWord_156520).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156520).length < 2 ^ (prefixWord ++ tailWord_156520).sum := by decide
  have hdescent : baseEnd_156520 < baseStart_156520 := by decide
  rcases family_descends (prefixWord ++ tailWord_156520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156543 : List Nat := [1, 1, 2, 2, 1, 1, 11]
def baseStart_156543 : Nat := 118140960795 + 156543 * 2 ^ 59
def prefixEnd_156543 : Nat := 4983230072969 + 3 ^ 40 * 156543 * 2
def baseEnd_156543 : Nat := 15877886833952841183719

theorem tailTrace_156543 : CollatzResearch.WordTrace tailWord_156543 prefixEnd_156543 15877886833952841183719 := by
  unfold tailWord_156543
  simp only [CollatzResearch.WordTrace]
  refine ⟨5709592271878921260994283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3806394847919280840662855 5709592271878921260994283)
  ·
    refine ⟨8564388407818381891491425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5709592271878921260994283 8564388407818381891491425)
    ·
      refine ⟨6423291305863786418618569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8564388407818381891491425 6423291305863786418618569)
      ·
        refine ⟨4817468479397839813963927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6423291305863786418618569 4817468479397839813963927)
        ·
          refine ⟨7226202719096759720945891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4817468479397839813963927 7226202719096759720945891)
          ·
            refine ⟨10839304078645139581418837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7226202719096759720945891 10839304078645139581418837)
            ·
              refine ⟨15877886833952841183719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 10839304078645139581418837 15877886833952841183719)
              ·
                rfl

theorem cell19_156543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 11].length) (baseStart_156543 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_156543 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_156543 prefixEnd_156543 := by exact prefixLift 156543
  have htrace : WordTrace (prefixWord ++ tailWord_156543) baseStart_156543 baseEnd_156543 := by
    simpa [prefixWord, tailWord_156543, baseEnd_156543] using wordTrace_append hprefix tailTrace_156543
  have hstable : (prefixWord ++ tailWord_156543).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156543).length < 2 ^ (prefixWord ++ tailWord_156543).sum := by decide
  have hdescent : baseEnd_156543 < baseStart_156543 := by decide
  rcases family_descends (prefixWord ++ tailWord_156543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156596 : List Nat := [2, 5, 2, 1, 1, 8]
def baseStart_156596 : Nat := 118140960795 + 156596 * 2 ^ 59
def prefixEnd_156596 : Nat := 4983230072969 + 3 ^ 40 * 156596 * 2
def baseEnd_156596 : Nat := 5294420844218900485915

theorem tailTrace_156596 : CollatzResearch.WordTrace tailWord_156596 prefixEnd_156596 5294420844218900485915 := by
  unfold tailWord_156596
  simp only [CollatzResearch.WordTrace]
  refine ⟨2855762670343455656336821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3807683560457940875115761 2855762670343455656336821)
  ·
    refine ⟨267727750344698967781577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2855762670343455656336821 267727750344698967781577)
    ·
      refine ⟨200795812758524225836183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267727750344698967781577 200795812758524225836183)
      ·
        refine ⟨301193719137786338754275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200795812758524225836183 301193719137786338754275)
        ·
          refine ⟨451790578706679508131413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301193719137786338754275 451790578706679508131413)
          ·
            refine ⟨5294420844218900485915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 451790578706679508131413 5294420844218900485915)
            ·
              rfl

theorem cell19_156596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 8].length) (baseStart_156596 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_156596 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_156596 prefixEnd_156596 := by exact prefixLift 156596
  have htrace : WordTrace (prefixWord ++ tailWord_156596) baseStart_156596 baseEnd_156596 := by
    simpa [prefixWord, tailWord_156596, baseEnd_156596] using wordTrace_append hprefix tailTrace_156596
  have hstable : (prefixWord ++ tailWord_156596).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156596).length < 2 ^ (prefixWord ++ tailWord_156596).sum := by decide
  have hdescent : baseEnd_156596 < baseStart_156596 := by decide
  rcases family_descends (prefixWord ++ tailWord_156596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156600 : List Nat := [2, 1, 2, 1, 2, 11]
def baseStart_156600 : Nat := 118140960795 + 156600 * 2 ^ 59
def prefixEnd_156600 : Nat := 4983230072969 + 3 ^ 40 * 156600 * 2
def baseEnd_156600 : Nat := 5294556081922142253815

theorem tailTrace_156600 : CollatzResearch.WordTrace tailWord_156600 prefixEnd_156600 5294556081922142253815 := by
  unfold tailWord_156600
  simp only [CollatzResearch.WordTrace]
  refine ⟨2855835616336209997909627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3807780821781613330546169 2855835616336209997909627)
  ·
    refine ⟨4283753424504314996864441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2855835616336209997909627 4283753424504314996864441)
    ·
      refine ⟨3212815068378236247648331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4283753424504314996864441 3212815068378236247648331)
      ·
        refine ⟨4819222602567354371472497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3212815068378236247648331 4819222602567354371472497)
        ·
          refine ⟨3614416951925515778604373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4819222602567354371472497 3614416951925515778604373)
          ·
            refine ⟨5294556081922142253815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3614416951925515778604373 5294556081922142253815)
            ·
              rfl

theorem cell19_156600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 11].length) (baseStart_156600 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_156600 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_156600 prefixEnd_156600 := by exact prefixLift 156600
  have htrace : WordTrace (prefixWord ++ tailWord_156600) baseStart_156600 baseEnd_156600 := by
    simpa [prefixWord, tailWord_156600, baseEnd_156600] using wordTrace_append hprefix tailTrace_156600
  have hstable : (prefixWord ++ tailWord_156600).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156600).length < 2 ^ (prefixWord ++ tailWord_156600).sum := by decide
  have hdescent : baseEnd_156600 < baseStart_156600 := by decide
  rcases family_descends (prefixWord ++ tailWord_156600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156634 : List Nat := [3, 1, 1, 2, 4, 2, 3, 3]
def baseStart_156634 : Nat := 118140960795 + 156634 * 2 ^ 59
def prefixEnd_156634 : Nat := 4983230072969 + 3 ^ 40 * 156634 * 2
def baseEnd_156634 : Nat := 47661350421597275528687

theorem tailTrace_156634 : CollatzResearch.WordTrace tailWord_156634 prefixEnd_156634 47661350421597275528687 := by
  unfold tailWord_156634
  simp only [CollatzResearch.WordTrace]
  refine ⟨1428227828637310950639239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3808607543032829201704637 1428227828637310950639239)
  ·
    refine ⟨2142341742955966425958859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1428227828637310950639239 2142341742955966425958859)
    ·
      refine ⟨3213512614433949638938289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2142341742955966425958859 3213512614433949638938289)
      ·
        refine ⟨2410134460825462229203717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3213512614433949638938289 2410134460825462229203717)
        ·
          refine ⟨451900211404774167975697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2410134460825462229203717 451900211404774167975697)
          ·
            refine ⟨338925158553580625981773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 451900211404774167975697 338925158553580625981773)
            ·
              refine ⟨127096934457592734743165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 338925158553580625981773 127096934457592734743165)
              ·
                refine ⟨47661350421597275528687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127096934457592734743165 47661350421597275528687)
                ·
                  rfl

theorem cell19_156634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 3].length) (baseStart_156634 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_156634 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_156634 prefixEnd_156634 := by exact prefixLift 156634
  have htrace : WordTrace (prefixWord ++ tailWord_156634) baseStart_156634 baseEnd_156634 := by
    simpa [prefixWord, tailWord_156634, baseEnd_156634] using wordTrace_append hprefix tailTrace_156634
  have hstable : (prefixWord ++ tailWord_156634).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156634).length < 2 ^ (prefixWord ++ tailWord_156634).sum := by decide
  have hdescent : baseEnd_156634 < baseStart_156634 := by decide
  rcases family_descends (prefixWord ++ tailWord_156634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156693 : List Nat := [1, 3, 2, 1, 4, 2, 1, 5]
def baseStart_156693 : Nat := 118140960795 + 156693 * 2 ^ 59
def prefixEnd_156693 : Nat := 4983230072969 + 3 ^ 40 * 156693 * 2
def baseEnd_156693 : Nat := 47679303226702620217415

theorem tailTrace_156693 : CollatzResearch.WordTrace tailWord_156693 prefixEnd_156693 47679303226702620217415 := by
  unfold tailWord_156693
  simp only [CollatzResearch.WordTrace]
  refine ⟨5715063221335496878954733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3810042147556997919303155 5715063221335496878954733)
  ·
    refine ⟨2143148708000811329608025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5715063221335496878954733 2143148708000811329608025)
    ·
      refine ⟨1607361531000608497206019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2143148708000811329608025 1607361531000608497206019)
      ·
        refine ⟨2411042296500912745809029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1607361531000608497206019 2411042296500912745809029)
        ·
          refine ⟨452070430593921139839193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2411042296500912745809029 452070430593921139839193)
          ·
            refine ⟨339052822945440854879395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 452070430593921139839193 339052822945440854879395)
            ·
              refine ⟨508579234418161282319093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339052822945440854879395 508579234418161282319093)
              ·
                refine ⟨47679303226702620217415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 508579234418161282319093 47679303226702620217415)
                ·
                  rfl

theorem cell19_156693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 5].length) (baseStart_156693 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_156693 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_156693 prefixEnd_156693 := by exact prefixLift 156693
  have htrace : WordTrace (prefixWord ++ tailWord_156693) baseStart_156693 baseEnd_156693 := by
    simpa [prefixWord, tailWord_156693, baseEnd_156693] using wordTrace_append hprefix tailTrace_156693
  have hstable : (prefixWord ++ tailWord_156693).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156693).length < 2 ^ (prefixWord ++ tailWord_156693).sum := by decide
  have hdescent : baseEnd_156693 < baseStart_156693 := by decide
  rcases family_descends (prefixWord ++ tailWord_156693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156805 : List Nat := [1, 3, 1, 1, 6, 1, 3, 3]
def baseStart_156805 : Nat := 118140960795 + 156805 * 2 ^ 59
def prefixEnd_156805 : Nat := 4983230072969 + 3 ^ 40 * 156805 * 2
def baseEnd_156805 : Nat := 47713383127919545728221

theorem tailTrace_156805 : CollatzResearch.WordTrace tailWord_156805 prefixEnd_156805 47713383127919545728221 := by
  unfold tailWord_156805
  simp only [CollatzResearch.WordTrace]
  refine ⟨5719148196929740007031869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3812765464619826671354579 5719148196929740007031869)
  ·
    refine ⟨2144680573848652502636951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5719148196929740007031869 2144680573848652502636951)
    ·
      refine ⟨3217020860772978753955427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2144680573848652502636951 3217020860772978753955427)
      ·
        refine ⟨4825531291159468130933141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3217020860772978753955427 4825531291159468130933141)
        ·
          refine ⟨226196779273100068637491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4825531291159468130933141 226196779273100068637491)
          ·
            refine ⟨339295168909650102956237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226196779273100068637491 339295168909650102956237)
            ·
              refine ⟨127235688341118788608589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 339295168909650102956237 127235688341118788608589)
              ·
                refine ⟨47713383127919545728221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127235688341118788608589 47713383127919545728221)
                ·
                  rfl

theorem cell19_156805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 3].length) (baseStart_156805 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_156805 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_156805 prefixEnd_156805 := by exact prefixLift 156805
  have htrace : WordTrace (prefixWord ++ tailWord_156805) baseStart_156805 baseEnd_156805 := by
    simpa [prefixWord, tailWord_156805, baseEnd_156805] using wordTrace_append hprefix tailTrace_156805
  have hstable : (prefixWord ++ tailWord_156805).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156805).length < 2 ^ (prefixWord ++ tailWord_156805).sum := by decide
  have hdescent : baseEnd_156805 < baseStart_156805 := by decide
  rcases family_descends (prefixWord ++ tailWord_156805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156826 : List Nat := [3, 1, 1, 5, 1, 2, 6]
def baseStart_156826 : Nat := 118140960795 + 156826 * 2 ^ 59
def prefixEnd_156826 : Nat := 4983230072969 + 3 ^ 40 * 156826 * 2
def baseEnd_156826 : Nat := 15906591036465906420499

theorem tailTrace_156826 : CollatzResearch.WordTrace tailWord_156826 prefixEnd_156826 15906591036465906420499 := by
  unfold tailWord_156826
  simp only [CollatzResearch.WordTrace]
  refine ⟨1429978532463415148386583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3813276086569107062364221 1429978532463415148386583)
  ·
    refine ⟨2144967798695122722579875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1429978532463415148386583 2144967798695122722579875)
    ·
      refine ⟨3217451698042684083869813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2144967798695122722579875 3217451698042684083869813)
      ·
        refine ⟨301636096691501632862795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3217451698042684083869813 301636096691501632862795)
        ·
          refine ⟨452454145037252449294193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301636096691501632862795 452454145037252449294193)
          ·
            refine ⟨339340608777939336970645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 452454145037252449294193 339340608777939336970645)
            ·
              refine ⟨15906591036465906420499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 339340608777939336970645 15906591036465906420499)
              ·
                rfl

theorem cell19_156826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 6].length) (baseStart_156826 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_156826 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_156826 prefixEnd_156826 := by exact prefixLift 156826
  have htrace : WordTrace (prefixWord ++ tailWord_156826) baseStart_156826 baseEnd_156826 := by
    simpa [prefixWord, tailWord_156826, baseEnd_156826] using wordTrace_append hprefix tailTrace_156826
  have hstable : (prefixWord ++ tailWord_156826).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156826).length < 2 ^ (prefixWord ++ tailWord_156826).sum := by decide
  have hdescent : baseEnd_156826 < baseStart_156826 := by decide
  rcases family_descends (prefixWord ++ tailWord_156826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156862 : List Nat := [4, 2, 1, 1, 3, 1, 4, 3]
def baseStart_156862 : Nat := 118140960795 + 156862 * 2 ^ 59
def prefixEnd_156862 : Nat := 4983230072969 + 3 ^ 40 * 156862 * 2
def baseEnd_156862 : Nat := 47730727363360302461399

theorem tailTrace_156862 : CollatzResearch.WordTrace tailWord_156862 prefixEnd_156862 47730727363360302461399 := by
  unfold tailWord_156862
  simp only [CollatzResearch.WordTrace]
  refine ⟨715153394715404842732105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3814151438482159161237893 715153394715404842732105)
  ·
    refine ⟨536365046036553632049079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 715153394715404842732105 536365046036553632049079)
    ·
      refine ⟨804547569054830448073619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 536365046036553632049079 804547569054830448073619)
      ·
        refine ⟨1206821353582245672110429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 804547569054830448073619 1206821353582245672110429)
        ·
          refine ⟨452558007593342127041411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1206821353582245672110429 452558007593342127041411)
          ·
            refine ⟨678837011390013190562117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452558007593342127041411 678837011390013190562117)
            ·
              refine ⟨127281939635627473230397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 678837011390013190562117 127281939635627473230397)
              ·
                refine ⟨47730727363360302461399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127281939635627473230397 47730727363360302461399)
                ·
                  rfl

theorem cell19_156862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_156862 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_156862 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_156862 prefixEnd_156862 := by exact prefixLift 156862
  have htrace : WordTrace (prefixWord ++ tailWord_156862) baseStart_156862 baseEnd_156862 := by
    simpa [prefixWord, tailWord_156862, baseEnd_156862] using wordTrace_append hprefix tailTrace_156862
  have hstable : (prefixWord ++ tailWord_156862).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156862).length < 2 ^ (prefixWord ++ tailWord_156862).sum := by decide
  have hdescent : baseEnd_156862 < baseStart_156862 := by decide
  rcases family_descends (prefixWord ++ tailWord_156862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156864 : List Nat := [2, 1, 1, 2, 6, 1, 1, 5]
def baseStart_156864 : Nat := 118140960795 + 156864 * 2 ^ 59
def prefixEnd_156864 : Nat := 4983230072969 + 3 ^ 40 * 156864 * 2
def baseEnd_156864 : Nat := 47731335933024890416949

theorem tailTrace_156864 : CollatzResearch.WordTrace tailWord_156864 prefixEnd_156864 47731335933024890416949 := by
  unfold tailWord_156864
  simp only [CollatzResearch.WordTrace]
  refine ⟨2860650051857996541714823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3814200069143995388953097 2860650051857996541714823)
  ·
    refine ⟨4290975077786994812572235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2860650051857996541714823 4290975077786994812572235)
    ·
      refine ⟨6436462616680492218858353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4290975077786994812572235 6436462616680492218858353)
      ·
        refine ⟨4827346962510369164143765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6436462616680492218858353 4827346962510369164143765)
        ·
          refine ⟨226281888867673554569239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4827346962510369164143765 226281888867673554569239)
          ·
            refine ⟨339422833301510331853859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226281888867673554569239 339422833301510331853859)
            ·
              refine ⟨509134249952265497780789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339422833301510331853859 509134249952265497780789)
              ·
                refine ⟨47731335933024890416949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 509134249952265497780789 47731335933024890416949)
                ·
                  rfl

theorem cell19_156864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 5].length) (baseStart_156864 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_156864 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_156864 prefixEnd_156864 := by exact prefixLift 156864
  have htrace : WordTrace (prefixWord ++ tailWord_156864) baseStart_156864 baseEnd_156864 := by
    simpa [prefixWord, tailWord_156864, baseEnd_156864] using wordTrace_append hprefix tailTrace_156864
  have hstable : (prefixWord ++ tailWord_156864).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156864).length < 2 ^ (prefixWord ++ tailWord_156864).sum := by decide
  have hdescent : baseEnd_156864 < baseStart_156864 := by decide
  rcases family_descends (prefixWord ++ tailWord_156864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156877 : List Nat := [1, 6, 2, 2, 2, 1, 5]
def baseStart_156877 : Nat := 118140960795 + 156877 * 2 ^ 59
def prefixEnd_156877 : Nat := 4983230072969 + 3 ^ 40 * 156877 * 2
def baseEnd_156877 : Nat := 15911763878614904042675

theorem tailTrace_156877 : CollatzResearch.WordTrace tailWord_156877 prefixEnd_156877 15911763878614904042675 := by
  unfold tailWord_156877
  simp only [CollatzResearch.WordTrace]
  refine ⟨5721774252668896303652885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3814516168445930869101923 5721774252668896303652885)
  ·
    refine ⟨268208168093854514233729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5721774252668896303652885 268208168093854514233729)
    ·
      refine ⟨201156126070390885675297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268208168093854514233729 201156126070390885675297)
      ·
        refine ⟨150867094552793164256473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201156126070390885675297 150867094552793164256473)
        ·
          refine ⟨113150320914594873192355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150867094552793164256473 113150320914594873192355)
          ·
            refine ⟨169725481371892309788533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113150320914594873192355 169725481371892309788533)
            ·
              refine ⟨15911763878614904042675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 169725481371892309788533 15911763878614904042675)
              ·
                rfl

theorem cell19_156877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 5].length) (baseStart_156877 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_156877 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_156877 prefixEnd_156877 := by exact prefixLift 156877
  have htrace : WordTrace (prefixWord ++ tailWord_156877) baseStart_156877 baseEnd_156877 := by
    simpa [prefixWord, tailWord_156877, baseEnd_156877] using wordTrace_append hprefix tailTrace_156877
  have hstable : (prefixWord ++ tailWord_156877).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156877).length < 2 ^ (prefixWord ++ tailWord_156877).sum := by decide
  have hdescent : baseEnd_156877 < baseStart_156877 := by decide
  rcases family_descends (prefixWord ++ tailWord_156877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156942 : List Nat := [4, 1, 1, 2, 1, 10]
def baseStart_156942 : Nat := 118140960795 + 156942 * 2 ^ 59
def prefixEnd_156942 : Nat := 4983230072969 + 3 ^ 40 * 156942 * 2
def baseEnd_156942 : Nat := 5306118905549313409267

theorem tailTrace_156942 : CollatzResearch.WordTrace tailWord_156942 prefixEnd_156942 5306118905549313409267 := by
  unfold tailWord_156942
  simp only [CollatzResearch.WordTrace]
  refine ⟨715518124679176550596135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3816096664955608269846053 715518124679176550596135)
  ·
    refine ⟨1073277187018764825894203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 715518124679176550596135 1073277187018764825894203)
    ·
      refine ⟨1609915780528147238841305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1073277187018764825894203 1609915780528147238841305)
      ·
        refine ⟨1207436835396110429130979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1609915780528147238841305 1207436835396110429130979)
        ·
          refine ⟨1811155253094165643696469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1207436835396110429130979 1811155253094165643696469)
          ·
            refine ⟨5306118905549313409267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1811155253094165643696469 5306118905549313409267)
            ·
              rfl

theorem cell19_156942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 10].length) (baseStart_156942 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_156942 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_156942 prefixEnd_156942 := by exact prefixLift 156942
  have htrace : WordTrace (prefixWord ++ tailWord_156942) baseStart_156942 baseEnd_156942 := by
    simpa [prefixWord, tailWord_156942, baseEnd_156942] using wordTrace_append hprefix tailTrace_156942
  have hstable : (prefixWord ++ tailWord_156942).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156942).length < 2 ^ (prefixWord ++ tailWord_156942).sum := by decide
  have hdescent : baseEnd_156942 < baseStart_156942 := by decide
  rcases family_descends (prefixWord ++ tailWord_156942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156957 : List Nat := [1, 4, 2, 3, 1, 3, 1, 4]
def baseStart_156957 : Nat := 118140960795 + 156957 * 2 ^ 59
def prefixEnd_156957 : Nat := 4983230072969 + 3 ^ 40 * 156957 * 2
def baseEnd_156957 : Nat := 47759634422428230350029

theorem tailTrace_156957 : CollatzResearch.WordTrace tailWord_156957 prefixEnd_156957 47759634422428230350029 := by
  unfold tailWord_156957
  simp only [CollatzResearch.WordTrace]
  refine ⟨5724692092379069966565125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3816461394919379977710083 5724692092379069966565125)
  ·
    refine ⟨1073379767321075618730961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5724692092379069966565125 1073379767321075618730961)
    ·
      refine ⟨805034825490806714048221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1073379767321075618730961 805034825490806714048221)
      ·
        refine ⟨301888059559052517768083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 805034825490806714048221 301888059559052517768083)
        ·
          refine ⟨452832089338578776652125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301888059559052517768083 452832089338578776652125)
          ·
            refine ⟨169812033501967041244547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 452832089338578776652125 169812033501967041244547)
            ·
              refine ⟨254718050252950561866821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169812033501967041244547 254718050252950561866821)
              ·
                refine ⟨47759634422428230350029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 254718050252950561866821 47759634422428230350029)
                ·
                  rfl

theorem cell19_156957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 4].length) (baseStart_156957 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_156957 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_156957 prefixEnd_156957 := by exact prefixLift 156957
  have htrace : WordTrace (prefixWord ++ tailWord_156957) baseStart_156957 baseEnd_156957 := by
    simpa [prefixWord, tailWord_156957, baseEnd_156957] using wordTrace_append hprefix tailTrace_156957
  have hstable : (prefixWord ++ tailWord_156957).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156957).length < 2 ^ (prefixWord ++ tailWord_156957).sum := by decide
  have hdescent : baseEnd_156957 < baseStart_156957 := by decide
  rcases family_descends (prefixWord ++ tailWord_156957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156999 : List Nat := [1, 1, 4, 1, 2, 4, 6]
def baseStart_156999 : Nat := 118140960795 + 156999 * 2 ^ 59
def prefixEnd_156999 : Nat := 4983230072969 + 3 ^ 40 * 156999 * 2
def baseEnd_156999 : Nat := 15924138128461525805527

theorem tailTrace_156999 : CollatzResearch.WordTrace tailWord_156999 prefixEnd_156999 15924138128461525805527 := by
  unfold tailWord_156999
  simp only [CollatzResearch.WordTrace]
  refine ⟨5726223958226911139594051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3817482638817940759729367 5726223958226911139594051)
  ·
    refine ⟨8589335937340366709391077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5726223958226911139594051 8589335937340366709391077)
    ·
      refine ⟨1610500488251318758010827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8589335937340366709391077 1610500488251318758010827)
      ·
        refine ⟨2415750732376978137016241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1610500488251318758010827 2415750732376978137016241)
        ·
          refine ⟨1811813049282733602762181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2415750732376978137016241 1811813049282733602762181)
          ·
            refine ⟨339714946740512550517909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1811813049282733602762181 339714946740512550517909)
            ·
              refine ⟨15924138128461525805527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 339714946740512550517909 15924138128461525805527)
              ·
                rfl

theorem cell19_156999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 6].length) (baseStart_156999 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_156999 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_156999 prefixEnd_156999 := by exact prefixLift 156999
  have htrace : WordTrace (prefixWord ++ tailWord_156999) baseStart_156999 baseEnd_156999 := by
    simpa [prefixWord, tailWord_156999, baseEnd_156999] using wordTrace_append hprefix tailTrace_156999
  have hstable : (prefixWord ++ tailWord_156999).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156999).length < 2 ^ (prefixWord ++ tailWord_156999).sum := by decide
  have hdescent : baseEnd_156999 < baseStart_156999 := by decide
  rcases family_descends (prefixWord ++ tailWord_156999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157031 : List Nat := [1, 1, 5, 1, 5, 1, 2, 3]
def baseStart_157031 : Nat := 118140960795 + 157031 * 2 ^ 59
def prefixEnd_157031 : Nat := 4983230072969 + 3 ^ 40 * 157031 * 2
def baseEnd_157031 : Nat := 47782151500017984705383

theorem tailTrace_157031 : CollatzResearch.WordTrace tailWord_157031 prefixEnd_157031 47782151500017984705383 := by
  unfold tailWord_157031
  simp only [CollatzResearch.WordTrace]
  refine ⟨5727391094110980604758947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3818260729407320403172631 5727391094110980604758947)
  ·
    refine ⟨8591086641166470907138421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5727391094110980604758947 8591086641166470907138421)
    ·
      refine ⟨805414372609356647544227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8591086641166470907138421 805414372609356647544227)
      ·
        refine ⟨1208121558914034971316341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 805414372609356647544227 1208121558914034971316341)
        ·
          refine ⟨113261396148190778560907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1208121558914034971316341 113261396148190778560907)
          ·
            refine ⟨169892094222286167841361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113261396148190778560907 169892094222286167841361)
            ·
              refine ⟨127419070666714625881021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169892094222286167841361 127419070666714625881021)
              ·
                refine ⟨47782151500017984705383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127419070666714625881021 47782151500017984705383)
                ·
                  rfl

theorem cell19_157031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 3].length) (baseStart_157031 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_157031 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_157031 prefixEnd_157031 := by exact prefixLift 157031
  have htrace : WordTrace (prefixWord ++ tailWord_157031) baseStart_157031 baseEnd_157031 := by
    simpa [prefixWord, tailWord_157031, baseEnd_157031] using wordTrace_append hprefix tailTrace_157031
  have hstable : (prefixWord ++ tailWord_157031).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157031).length < 2 ^ (prefixWord ++ tailWord_157031).sum := by decide
  have hdescent : baseEnd_157031 < baseStart_157031 := by decide
  rcases family_descends (prefixWord ++ tailWord_157031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157113 : List Nat := [1, 2, 1, 4, 4, 7]
def baseStart_157113 : Nat := 118140960795 + 157113 * 2 ^ 59
def prefixEnd_157113 : Nat := 4983230072969 + 3 ^ 40 * 157113 * 2
def baseEnd_157113 : Nat := 5311900317362898986993

theorem tailTrace_157113 : CollatzResearch.WordTrace tailWord_157113 prefixEnd_157113 5311900317362898986993 := by
  unfold tailWord_157113
  simp only [CollatzResearch.WordTrace]
  refine ⟨5730381879813908609243993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3820254586542605739495995 5730381879813908609243993)
  ·
    refine ⟨4297786409860431456932995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5730381879813908609243993 4297786409860431456932995)
    ·
      refine ⟨6446679614790647185399493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4297786409860431456932995 6446679614790647185399493)
      ·
        refine ⟨1208752427773246347262405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6446679614790647185399493 1208752427773246347262405)
        ·
          refine ⟨226641080207483690111701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1208752427773246347262405 226641080207483690111701)
          ·
            refine ⟨5311900317362898986993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 226641080207483690111701 5311900317362898986993)
            ·
              rfl

theorem cell19_157113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 7].length) (baseStart_157113 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_157113 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_157113 prefixEnd_157113 := by exact prefixLift 157113
  have htrace : WordTrace (prefixWord ++ tailWord_157113) baseStart_157113 baseEnd_157113 := by
    simpa [prefixWord, tailWord_157113, baseEnd_157113] using wordTrace_append hprefix tailTrace_157113
  have hstable : (prefixWord ++ tailWord_157113).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157113).length < 2 ^ (prefixWord ++ tailWord_157113).sum := by decide
  have hdescent : baseEnd_157113 < baseStart_157113 := by decide
  rcases family_descends (prefixWord ++ tailWord_157113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157122 : List Nat := [3, 5, 2, 1, 1, 2, 1, 4]
def baseStart_157122 : Nat := 118140960795 + 157122 * 2 ^ 59
def prefixEnd_157122 : Nat := 4983230072969 + 3 ^ 40 * 157122 * 2
def baseEnd_157122 : Nat := 47809841419756736682913

theorem tailTrace_157122 : CollatzResearch.WordTrace tailWord_157122 prefixEnd_157122 47809841419756736682913 := by
  unfold tailWord_157122
  simp only [CollatzResearch.WordTrace]
  refine ⟨1432677534195325786580405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3820473424520868764214413 1432677534195325786580405)
  ·
    refine ⟨134313518830811792491913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1432677534195325786580405 134313518830811792491913)
    ·
      refine ⟨100735139123108844368935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134313518830811792491913 100735139123108844368935)
      ·
        refine ⟨151102708684663266553403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100735139123108844368935 151102708684663266553403)
        ·
          refine ⟨226654063026994899830105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151102708684663266553403 226654063026994899830105)
          ·
            refine ⟨169990547270246174872579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226654063026994899830105 169990547270246174872579)
            ·
              refine ⟨254985820905369262308869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169990547270246174872579 254985820905369262308869)
              ·
                refine ⟨47809841419756736682913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 254985820905369262308869 47809841419756736682913)
                ·
                  rfl

theorem cell19_157122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 4].length) (baseStart_157122 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_157122 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_157122 prefixEnd_157122 := by exact prefixLift 157122
  have htrace : WordTrace (prefixWord ++ tailWord_157122) baseStart_157122 baseEnd_157122 := by
    simpa [prefixWord, tailWord_157122, baseEnd_157122] using wordTrace_append hprefix tailTrace_157122
  have hstable : (prefixWord ++ tailWord_157122).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157122).length < 2 ^ (prefixWord ++ tailWord_157122).sum := by decide
  have hdescent : baseEnd_157122 < baseStart_157122 := by decide
  rcases family_descends (prefixWord ++ tailWord_157122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157130 : List Nat := [3, 1, 2, 1, 2, 5, 1, 4]
def baseStart_157130 : Nat := 118140960795 + 157130 * 2 ^ 59
def prefixEnd_157130 : Nat := 4983230072969 + 3 ^ 40 * 157130 * 2
def baseEnd_157130 : Nat := 47812275698415088505113

theorem tailTrace_157130 : CollatzResearch.WordTrace tailWord_157130 prefixEnd_157130 47812275698415088505113 := by
  unfold tailWord_157130
  simp only [CollatzResearch.WordTrace]
  refine ⟨1432750480188080128153211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3820667947168213675075229 1432750480188080128153211)
  ·
    refine ⟨2149125720282120192229817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1432750480188080128153211 2149125720282120192229817)
    ·
      refine ⟨1611844290211590144172363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2149125720282120192229817 1611844290211590144172363)
      ·
        refine ⟨2417766435317385216258545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1611844290211590144172363 2417766435317385216258545)
        ·
          refine ⟨1813324826488038912193909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2417766435317385216258545 1813324826488038912193909)
          ·
            refine ⟨169999202483253648018179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1813324826488038912193909 169999202483253648018179)
            ·
              refine ⟨254998803724880472027269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169999202483253648018179 254998803724880472027269)
              ·
                refine ⟨47812275698415088505113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 254998803724880472027269 47812275698415088505113)
                ·
                  rfl

theorem cell19_157130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_157130 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_157130 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_157130 prefixEnd_157130 := by exact prefixLift 157130
  have htrace : WordTrace (prefixWord ++ tailWord_157130) baseStart_157130 baseEnd_157130 := by
    simpa [prefixWord, tailWord_157130, baseEnd_157130] using wordTrace_append hprefix tailTrace_157130
  have hstable : (prefixWord ++ tailWord_157130).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157130).length < 2 ^ (prefixWord ++ tailWord_157130).sum := by decide
  have hdescent : baseEnd_157130 < baseStart_157130 := by decide
  rcases family_descends (prefixWord ++ tailWord_157130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157204 : List Nat := [2, 4, 3, 1, 2, 1, 1, 5]
def baseStart_157204 : Nat := 118140960795 + 157204 * 2 ^ 59
def prefixEnd_157204 : Nat := 4983230072969 + 3 ^ 40 * 157204 * 2
def baseEnd_157204 : Nat := 47834792776004842860467

theorem tailTrace_157204 : CollatzResearch.WordTrace tailWord_157204 prefixEnd_157204 47834792776004842860467 := by
  unfold tailWord_157204
  simp only [CollatzResearch.WordTrace]
  refine ⟨2866850461242115575403333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3822467281656154100537777 2866850461242115575403333)
  ·
    refine ⟨537534461482896670388125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2866850461242115575403333 537534461482896670388125)
    ·
      refine ⟨201575423056086251395547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 537534461482896670388125 201575423056086251395547)
      ·
        refine ⟨302363134584129377093321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201575423056086251395547 302363134584129377093321)
        ·
          refine ⟨226772350938097032819991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 302363134584129377093321 226772350938097032819991)
          ·
            refine ⟨340158526407145549229987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226772350938097032819991 340158526407145549229987)
            ·
              refine ⟨510237789610718323844981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 340158526407145549229987 510237789610718323844981)
              ·
                refine ⟨47834792776004842860467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 510237789610718323844981 47834792776004842860467)
                ·
                  rfl

theorem cell19_157204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 5].length) (baseStart_157204 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_157204 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_157204 prefixEnd_157204 := by exact prefixLift 157204
  have htrace : WordTrace (prefixWord ++ tailWord_157204) baseStart_157204 baseEnd_157204 := by
    simpa [prefixWord, tailWord_157204, baseEnd_157204] using wordTrace_append hprefix tailTrace_157204
  have hstable : (prefixWord ++ tailWord_157204).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157204).length < 2 ^ (prefixWord ++ tailWord_157204).sum := by decide
  have hdescent : baseEnd_157204 < baseStart_157204 := by decide
  rcases family_descends (prefixWord ++ tailWord_157204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157244 : List Nat := [2, 2, 2, 2, 4, 1, 2, 4]
def baseStart_157244 : Nat := 118140960795 + 157244 * 2 ^ 59
def prefixEnd_157244 : Nat := 4983230072969 + 3 ^ 40 * 157244 * 2
def baseEnd_157244 : Nat := 47846964169296601971469

theorem tailTrace_157244 : CollatzResearch.WordTrace tailWord_157244 prefixEnd_157244 47846964169296601971469 := by
  unfold tailWord_157244
  simp only [CollatzResearch.WordTrace]
  refine ⟨2867579921169658991131393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3823439894892878654841857 2867579921169658991131393)
  ·
    refine ⟨2150684940877244243348545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2867579921169658991131393 2150684940877244243348545)
    ·
      refine ⟨1613013705657933182511409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2150684940877244243348545 1613013705657933182511409)
      ·
        refine ⟨1209760279243449886883557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1613013705657933182511409 1209760279243449886883557)
        ·
          refine ⟨226830052358146853790667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1209760279243449886883557 226830052358146853790667)
          ·
            refine ⟨340245078537220280686001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226830052358146853790667 340245078537220280686001)
            ·
              refine ⟨255183808902915210514501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 340245078537220280686001 255183808902915210514501)
              ·
                refine ⟨47846964169296601971469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 255183808902915210514501 47846964169296601971469)
                ·
                  rfl

theorem cell19_157244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 4].length) (baseStart_157244 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_157244 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_157244 prefixEnd_157244 := by exact prefixLift 157244
  have htrace : WordTrace (prefixWord ++ tailWord_157244) baseStart_157244 baseEnd_157244 := by
    simpa [prefixWord, tailWord_157244, baseEnd_157244] using wordTrace_append hprefix tailTrace_157244
  have hstable : (prefixWord ++ tailWord_157244).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157244).length < 2 ^ (prefixWord ++ tailWord_157244).sum := by decide
  have hdescent : baseEnd_157244 < baseStart_157244 := by decide
  rcases family_descends (prefixWord ++ tailWord_157244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157301 : List Nat := [1, 3, 4, 2, 1, 1, 3, 4]
def baseStart_157301 : Nat := 118140960795 + 157301 * 2 ^ 59
def prefixEnd_157301 : Nat := 4983230072969 + 3 ^ 40 * 157301 * 2
def baseEnd_157301 : Nat := 47864308404737358704647

theorem tailTrace_157301 : CollatzResearch.WordTrace tailWord_157301 prefixEnd_157301 47864308404737358704647 := by
  unfold tailWord_157301
  simp only [CollatzResearch.WordTrace]
  refine ⟨5737238803132816717087757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3824825868755211144725171 5737238803132816717087757)
  ·
    refine ⟨2151464551174806268907909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5737238803132816717087757 2151464551174806268907909)
    ·
      refine ⟨403399603345276175420233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2151464551174806268907909 403399603345276175420233)
      ·
        refine ⟨302549702508957131565175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 403399603345276175420233 302549702508957131565175)
        ·
          refine ⟨453824553763435697347763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302549702508957131565175 453824553763435697347763)
          ·
            refine ⟨680736830645153546021645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 453824553763435697347763 680736830645153546021645)
            ·
              refine ⟨255276311491932579758117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 680736830645153546021645 255276311491932579758117)
              ·
                refine ⟨47864308404737358704647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 255276311491932579758117 47864308404737358704647)
                ·
                  rfl

theorem cell19_157301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 4].length) (baseStart_157301 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_157301 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_157301 prefixEnd_157301 := by exact prefixLift 157301
  have htrace : WordTrace (prefixWord ++ tailWord_157301) baseStart_157301 baseEnd_157301 := by
    simpa [prefixWord, tailWord_157301, baseEnd_157301] using wordTrace_append hprefix tailTrace_157301
  have hstable : (prefixWord ++ tailWord_157301).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157301).length < 2 ^ (prefixWord ++ tailWord_157301).sum := by decide
  have hdescent : baseEnd_157301 < baseStart_157301 := by decide
  rcases family_descends (prefixWord ++ tailWord_157301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157381 : List Nat := [1, 3, 1, 1, 1, 1, 2, 9]
def baseStart_157381 : Nat := 118140960795 + 157381 * 2 ^ 59
def prefixEnd_157381 : Nat := 4983230072969 + 3 ^ 40 * 157381 * 2
def baseEnd_157381 : Nat := 47888651191320876926651

theorem tailTrace_157381 : CollatzResearch.WordTrace tailWord_157381 prefixEnd_157381 47888651191320876926651 := by
  unfold tailWord_157381
  simp only [CollatzResearch.WordTrace]
  refine ⟨5740156642842990379999997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3826771095228660253333331 5740156642842990379999997)
  ·
    refine ⟨2152558741066121392499999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5740156642842990379999997 2152558741066121392499999)
    ·
      refine ⟨3228838111599182088749999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2152558741066121392499999 3228838111599182088749999)
      ·
        refine ⟨4843257167398773133124999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3228838111599182088749999 4843257167398773133124999)
        ·
          refine ⟨7264885751098159699687499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4843257167398773133124999 7264885751098159699687499)
          ·
            refine ⟨10897328626647239549531249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7264885751098159699687499 10897328626647239549531249)
            ·
              refine ⟨8172996469985429662148437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10897328626647239549531249 8172996469985429662148437)
              ·
                refine ⟨47888651191320876926651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8172996469985429662148437 47888651191320876926651)
                ·
                  rfl

theorem cell19_157381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 9].length) (baseStart_157381 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_157381 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_157381 prefixEnd_157381 := by exact prefixLift 157381
  have htrace : WordTrace (prefixWord ++ tailWord_157381) baseStart_157381 baseEnd_157381 := by
    simpa [prefixWord, tailWord_157381, baseEnd_157381] using wordTrace_append hprefix tailTrace_157381
  have hstable : (prefixWord ++ tailWord_157381).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157381).length < 2 ^ (prefixWord ++ tailWord_157381).sum := by decide
  have hdescent : baseEnd_157381 < baseStart_157381 := by decide
  rcases family_descends (prefixWord ++ tailWord_157381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157396 : List Nat := [2, 4, 1, 3, 1, 3, 5]
def baseStart_157396 : Nat := 118140960795 + 157396 * 2 ^ 59
def prefixEnd_157396 : Nat := 4983230072969 + 3 ^ 40 * 157396 * 2
def baseEnd_157396 : Nat := 15964405154601762197759

theorem tailTrace_157396 : CollatzResearch.WordTrace tailWord_157396 prefixEnd_157396 15964405154601762197759 := by
  unfold tailWord_157396
  simp only [CollatzResearch.WordTrace]
  refine ⟨2870351868894323970898021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3827135825192431961197361 2870351868894323970898021)
  ·
    refine ⟨538190975417685744543379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2870351868894323970898021 538190975417685744543379)
    ·
      refine ⟨807286463126528616815069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 538190975417685744543379 807286463126528616815069)
      ·
        refine ⟨302732423672448231305651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 807286463126528616815069 302732423672448231305651)
        ·
          refine ⟨454098635508672346958477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302732423672448231305651 454098635508672346958477)
          ·
            refine ⟨170286988315752130109429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 454098635508672346958477 170286988315752130109429)
            ·
              refine ⟨15964405154601762197759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 170286988315752130109429 15964405154601762197759)
              ·
                rfl

theorem cell19_157396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 5].length) (baseStart_157396 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_157396 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_157396 prefixEnd_157396 := by exact prefixLift 157396
  have htrace : WordTrace (prefixWord ++ tailWord_157396) baseStart_157396 baseEnd_157396 := by
    simpa [prefixWord, tailWord_157396, baseEnd_157396] using wordTrace_append hprefix tailTrace_157396
  have hstable : (prefixWord ++ tailWord_157396).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157396).length < 2 ^ (prefixWord ++ tailWord_157396).sum := by decide
  have hdescent : baseEnd_157396 < baseStart_157396 := by decide
  rcases family_descends (prefixWord ++ tailWord_157396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157419 : List Nat := [1, 1, 1, 1, 2, 4, 3, 6]
def baseStart_157419 : Nat := 118140960795 + 157419 * 2 ^ 59
def prefixEnd_157419 : Nat := 4983230072969 + 3 ^ 40 * 157419 * 2
def baseEnd_157419 : Nat := 47900214014948048082103

theorem tailTrace_157419 : CollatzResearch.WordTrace tailWord_157419 prefixEnd_157419 47900214014948048082103 := by
  unfold tailWord_157419
  simp only [CollatzResearch.WordTrace]
  refine ⟨5741542616705322869883311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3827695077803548579922207 5741542616705322869883311)
  ·
    refine ⟨8612313925057984304824967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5741542616705322869883311 8612313925057984304824967)
    ·
      refine ⟨12918470887586976457237451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8612313925057984304824967 12918470887586976457237451)
      ·
        refine ⟨19377706331380464685856177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12918470887586976457237451 19377706331380464685856177)
        ·
          refine ⟨14533279748535348514392133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19377706331380464685856177 14533279748535348514392133)
          ·
            refine ⟨2724989952850377846448525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14533279748535348514392133 2724989952850377846448525)
            ·
              refine ⟨1021871232318891692418197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2724989952850377846448525 1021871232318891692418197)
              ·
                refine ⟨47900214014948048082103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1021871232318891692418197 47900214014948048082103)
                ·
                  rfl

theorem cell19_157419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 6].length) (baseStart_157419 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_157419 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_157419 prefixEnd_157419 := by exact prefixLift 157419
  have htrace : WordTrace (prefixWord ++ tailWord_157419) baseStart_157419 baseEnd_157419 := by
    simpa [prefixWord, tailWord_157419, baseEnd_157419] using wordTrace_append hprefix tailTrace_157419
  have hstable : (prefixWord ++ tailWord_157419).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157419).length < 2 ^ (prefixWord ++ tailWord_157419).sum := by decide
  have hdescent : baseEnd_157419 < baseStart_157419 := by decide
  rcases family_descends (prefixWord ++ tailWord_157419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157491 : List Nat := [1, 1, 1, 2, 7, 1, 3, 3]
def baseStart_157491 : Nat := 118140960795 + 157491 * 2 ^ 59
def prefixEnd_157491 : Nat := 4983230072969 + 3 ^ 40 * 157491 * 2
def baseEnd_157491 : Nat := 47922122522873214481907

theorem tailTrace_157491 : CollatzResearch.WordTrace tailWord_157491 prefixEnd_157491 47922122522873214481907 := by
  unfold tailWord_157491
  simp only [CollatzResearch.WordTrace]
  refine ⟨5744168672444479166504327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3829445781629652777669551 5744168672444479166504327)
  ·
    refine ⟨8616253008666718749756491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5744168672444479166504327 8616253008666718749756491)
    ·
      refine ⟨12924379513000078124634737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8616253008666718749756491 12924379513000078124634737)
      ·
        refine ⟨9693284634750058593476053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12924379513000078124634737 9693284634750058593476053)
        ·
          refine ⟨227186358626954498284595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 9693284634750058593476053 227186358626954498284595)
          ·
            refine ⟨340779537940431747426893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227186358626954498284595 340779537940431747426893)
            ·
              refine ⟨127792326727661905285085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 340779537940431747426893 127792326727661905285085)
              ·
                refine ⟨47922122522873214481907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127792326727661905285085 47922122522873214481907)
                ·
                  rfl

theorem cell19_157491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 3].length) (baseStart_157491 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_157491 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_157491 prefixEnd_157491 := by exact prefixLift 157491
  have htrace : WordTrace (prefixWord ++ tailWord_157491) baseStart_157491 baseEnd_157491 := by
    simpa [prefixWord, tailWord_157491, baseEnd_157491] using wordTrace_append hprefix tailTrace_157491
  have hstable : (prefixWord ++ tailWord_157491).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157491).length < 2 ^ (prefixWord ++ tailWord_157491).sum := by decide
  have hdescent : baseEnd_157491 < baseStart_157491 := by decide
  rcases family_descends (prefixWord ++ tailWord_157491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157514 : List Nat := [3, 1, 2, 1, 1, 1, 10]
def baseStart_157514 : Nat := 118140960795 + 157514 * 2 ^ 59
def prefixEnd_157514 : Nat := 4983230072969 + 3 ^ 40 * 157514 * 2
def baseEnd_157514 : Nat := 15976373691338658656911

theorem tailTrace_157514 : CollatzResearch.WordTrace tailWord_157514 prefixEnd_157514 15976373691338658656911 := by
  unfold tailWord_157514
  simp only [CollatzResearch.WordTrace]
  refine ⟨1436251887840288523647899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3830005034240769396394397 1436251887840288523647899)
  ·
    refine ⟨2154377831760432785471849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1436251887840288523647899 2154377831760432785471849)
    ·
      refine ⟨1615783373820324589103887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2154377831760432785471849 1615783373820324589103887)
      ·
        refine ⟨2423675060730486883655831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1615783373820324589103887 2423675060730486883655831)
        ·
          refine ⟨3635512591095730325483747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2423675060730486883655831 3635512591095730325483747)
          ·
            refine ⟨5453268886643595488225621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3635512591095730325483747 5453268886643595488225621)
            ·
              refine ⟨15976373691338658656911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5453268886643595488225621 15976373691338658656911)
              ·
                rfl

theorem cell19_157514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 10].length) (baseStart_157514 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_157514 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_157514 prefixEnd_157514 := by exact prefixLift 157514
  have htrace : WordTrace (prefixWord ++ tailWord_157514) baseStart_157514 baseEnd_157514 := by
    simpa [prefixWord, tailWord_157514, baseEnd_157514] using wordTrace_append hprefix tailTrace_157514
  have hstable : (prefixWord ++ tailWord_157514).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157514).length < 2 ^ (prefixWord ++ tailWord_157514).sum := by decide
  have hdescent : baseEnd_157514 < baseStart_157514 := by decide
  rcases family_descends (prefixWord ++ tailWord_157514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157548 : List Nat := [2, 2, 1, 1, 4, 4, 2, 3]
def baseStart_157548 : Nat := 118140960795 + 157548 * 2 ^ 59
def prefixEnd_157548 : Nat := 4983230072969 + 3 ^ 40 * 157548 * 2
def baseEnd_157548 : Nat := 47939466758313971215085

theorem tailTrace_157548 : CollatzResearch.WordTrace tailWord_157548 prefixEnd_157548 47939466758313971215085 := by
  unfold tailWord_157548
  simp only [CollatzResearch.WordTrace]
  refine ⟨2873123816618988950664649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3830831755491985267552865 2873123816618988950664649)
  ·
    refine ⟨2154842862464241712998487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2873123816618988950664649 2154842862464241712998487)
    ·
      refine ⟨3232264293696362569497731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2154842862464241712998487 3232264293696362569497731)
      ·
        refine ⟨4848396440544543854246597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3232264293696362569497731 4848396440544543854246597)
        ·
          refine ⟨909074332602101972671237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4848396440544543854246597 909074332602101972671237)
          ·
            refine ⟨170451437362894119875857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 909074332602101972671237 170451437362894119875857)
            ·
              refine ⟨127838578022170589906893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170451437362894119875857 127838578022170589906893)
              ·
                refine ⟨47939466758313971215085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127838578022170589906893 47939466758313971215085)
                ·
                  rfl

theorem cell19_157548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 3].length) (baseStart_157548 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_157548 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_157548 prefixEnd_157548 := by exact prefixLift 157548
  have htrace : WordTrace (prefixWord ++ tailWord_157548) baseStart_157548 baseEnd_157548 := by
    simpa [prefixWord, tailWord_157548, baseEnd_157548] using wordTrace_append hprefix tailTrace_157548
  have hstable : (prefixWord ++ tailWord_157548).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157548).length < 2 ^ (prefixWord ++ tailWord_157548).sum := by decide
  have hdescent : baseEnd_157548 < baseStart_157548 := by decide
  rcases family_descends (prefixWord ++ tailWord_157548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157571 : List Nat := [1, 1, 1, 3, 4, 2, 7]
def baseStart_157571 : Nat := 118140960795 + 157571 * 2 ^ 59
def prefixEnd_157571 : Nat := 4983230072969 + 3 ^ 40 * 157571 * 2
def baseEnd_157571 : Nat := 15982155103152244234637

theorem tailTrace_157571 : CollatzResearch.WordTrace tailWord_157571 prefixEnd_157571 15982155103152244234637 := by
  unfold tailWord_157571
  simp only [CollatzResearch.WordTrace]
  refine ⟨5747086512154652829416567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3831391008103101886277711 5747086512154652829416567)
  ·
    refine ⟨8620629768231979244124851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5747086512154652829416567 8620629768231979244124851)
    ·
      refine ⟨12930944652347968866187277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8620629768231979244124851 12930944652347968866187277)
      ·
        refine ⟨4849104244630488324820229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12930944652347968866187277 4849104244630488324820229)
        ·
          refine ⟨909207045868216560903793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4849104244630488324820229 909207045868216560903793)
          ·
            refine ⟨681905284401162420677845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 909207045868216560903793 681905284401162420677845)
            ·
              refine ⟨15982155103152244234637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 681905284401162420677845 15982155103152244234637)
              ·
                rfl

theorem cell19_157571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 7].length) (baseStart_157571 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_157571 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_157571 prefixEnd_157571 := by exact prefixLift 157571
  have htrace : WordTrace (prefixWord ++ tailWord_157571) baseStart_157571 baseEnd_157571 := by
    simpa [prefixWord, tailWord_157571, baseEnd_157571] using wordTrace_append hprefix tailTrace_157571
  have hstable : (prefixWord ++ tailWord_157571).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157571).length < 2 ^ (prefixWord ++ tailWord_157571).sum := by decide
  have hdescent : baseEnd_157571 < baseStart_157571 := by decide
  rcases family_descends (prefixWord ++ tailWord_157571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157586 : List Nat := [3, 2, 3, 2, 1, 2, 2, 4]
def baseStart_157586 : Nat := 118140960795 + 157586 * 2 ^ 59
def prefixEnd_157586 : Nat := 4983230072969 + 3 ^ 40 * 157586 * 2
def baseEnd_157586 : Nat := 47951029581941142370537

theorem tailTrace_157586 : CollatzResearch.WordTrace tailWord_157586 prefixEnd_157586 47951029581941142370537 := by
  unfold tailWord_157586
  simp only [CollatzResearch.WordTrace]
  refine ⟨1436908401775077597803153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3831755738066873594141741 1436908401775077597803153)
  ·
    refine ⟨1077681301331308198352365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1436908401775077597803153 1077681301331308198352365)
    ·
      refine ⟨404130487999240574382137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1077681301331308198352365 404130487999240574382137)
      ·
        refine ⟨303097865999430430786603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 404130487999240574382137 303097865999430430786603)
        ·
          refine ⟨454646798999145646179905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303097865999430430786603 454646798999145646179905)
          ·
            refine ⟨340985099249359234634929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 454646798999145646179905 340985099249359234634929)
            ·
              refine ⟨255738824437019425976197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 340985099249359234634929 255738824437019425976197)
              ·
                refine ⟨47951029581941142370537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 255738824437019425976197 47951029581941142370537)
                ·
                  rfl

theorem cell19_157586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_157586 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_157586 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_157586 prefixEnd_157586 := by exact prefixLift 157586
  have htrace : WordTrace (prefixWord ++ tailWord_157586) baseStart_157586 baseEnd_157586 := by
    simpa [prefixWord, tailWord_157586, baseEnd_157586] using wordTrace_append hprefix tailTrace_157586
  have hstable : (prefixWord ++ tailWord_157586).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157586).length < 2 ^ (prefixWord ++ tailWord_157586).sum := by decide
  have hdescent : baseEnd_157586 < baseStart_157586 := by decide
  rcases family_descends (prefixWord ++ tailWord_157586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157588 : List Nat := [2, 4, 2, 1, 1, 2, 1, 6]
def baseStart_157588 : Nat := 118140960795 + 157588 * 2 ^ 59
def prefixEnd_157588 : Nat := 4983230072969 + 3 ^ 40 * 157588 * 2
def baseEnd_157588 : Nat := 47951638151605730326087

theorem tailTrace_157588 : CollatzResearch.WordTrace tailWord_157588 prefixEnd_157588 47951638151605730326087 := by
  unfold tailWord_157588
  simp only [CollatzResearch.WordTrace]
  refine ⟨2873853276546532366392709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3831804368728709821856945 2873853276546532366392709)
  ·
    refine ⟨538847489352474818698633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2873853276546532366392709 538847489352474818698633)
    ·
      refine ⟨404135617014356114023975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 538847489352474818698633 404135617014356114023975)
      ·
        refine ⟨606203425521534171035963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 404135617014356114023975 606203425521534171035963)
        ·
          refine ⟨909305138282301256553945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 606203425521534171035963 909305138282301256553945)
          ·
            refine ⟨681978853711725942415459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 909305138282301256553945 681978853711725942415459)
            ·
              refine ⟨1022968280567588913623189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 681978853711725942415459 1022968280567588913623189)
              ·
                refine ⟨47951638151605730326087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1022968280567588913623189 47951638151605730326087)
                ·
                  rfl

theorem cell19_157588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 6].length) (baseStart_157588 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_157588 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_157588 prefixEnd_157588 := by exact prefixLift 157588
  have htrace : WordTrace (prefixWord ++ tailWord_157588) baseStart_157588 baseEnd_157588 := by
    simpa [prefixWord, tailWord_157588, baseEnd_157588] using wordTrace_append hprefix tailTrace_157588
  have hstable : (prefixWord ++ tailWord_157588).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157588).length < 2 ^ (prefixWord ++ tailWord_157588).sum := by decide
  have hdescent : baseEnd_157588 < baseStart_157588 := by decide
  rcases family_descends (prefixWord ++ tailWord_157588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157607 : List Nat := [1, 1, 6, 1, 2, 1, 2, 5]
def baseStart_157607 : Nat := 118140960795 + 157607 * 2 ^ 59
def prefixEnd_157607 : Nat := 4983230072969 + 3 ^ 40 * 157607 * 2
def baseEnd_157607 : Nat := 47957419563419315903813

theorem tailTrace_157607 : CollatzResearch.WordTrace tailWord_157607 prefixEnd_157607 47957419563419315903813 := by
  unfold tailWord_157607
  simp only [CollatzResearch.WordTrace]
  refine ⟨5748399540024230977727075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3832266360016153985151383 5748399540024230977727075)
  ·
    refine ⟨8622599310036346466590613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5748399540024230977727075 8622599310036346466590613)
    ·
      refine ⟨404184342657953740621435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8622599310036346466590613 404184342657953740621435)
      ·
        refine ⟨606276513986930610932153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 404184342657953740621435 606276513986930610932153)
        ·
          refine ⟨454707385490197958199115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 606276513986930610932153 454707385490197958199115)
          ·
            refine ⟨682061078235296937298673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454707385490197958199115 682061078235296937298673)
            ·
              refine ⟨511545808676472702974005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 682061078235296937298673 511545808676472702974005)
              ·
                refine ⟨47957419563419315903813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 511545808676472702974005 47957419563419315903813)
                ·
                  rfl

theorem cell19_157607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 5].length) (baseStart_157607 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_157607 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_157607 prefixEnd_157607 := by exact prefixLift 157607
  have htrace : WordTrace (prefixWord ++ tailWord_157607) baseStart_157607 baseEnd_157607 := by
    simpa [prefixWord, tailWord_157607, baseEnd_157607] using wordTrace_append hprefix tailTrace_157607
  have hstable : (prefixWord ++ tailWord_157607).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157607).length < 2 ^ (prefixWord ++ tailWord_157607).sum := by decide
  have hdescent : baseEnd_157607 < baseStart_157607 := by decide
  rcases family_descends (prefixWord ++ tailWord_157607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157704 : List Nat := [2, 1, 3, 2, 1, 2, 2, 6]
def baseStart_157704 : Nat := 118140960795 + 157704 * 2 ^ 59
def prefixEnd_157704 : Nat := 4983230072969 + 3 ^ 40 * 157704 * 2
def baseEnd_157704 : Nat := 47986935192151831747993

theorem tailTrace_157704 : CollatzResearch.WordTrace tailWord_157704 prefixEnd_157704 47986935192151831747993 := by
  unfold tailWord_157704
  simp only [CollatzResearch.WordTrace]
  refine ⟨2875968710336408272004083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3834624947115211029338777 2875968710336408272004083)
  ·
    refine ⟨4313953065504612408006125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2875968710336408272004083 4313953065504612408006125)
    ·
      refine ⟨1617732399564229653002297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4313953065504612408006125 1617732399564229653002297)
      ·
        refine ⟨1213299299673172239751723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1617732399564229653002297 1213299299673172239751723)
        ·
          refine ⟨1819948949509758359627585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1213299299673172239751723 1819948949509758359627585)
          ·
            refine ⟨1364961712132318769720689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1819948949509758359627585 1364961712132318769720689)
            ·
              refine ⟨1023721284099239077290517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1364961712132318769720689 1023721284099239077290517)
              ·
                refine ⟨47986935192151831747993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1023721284099239077290517 47986935192151831747993)
                ·
                  rfl

theorem cell19_157704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_157704 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_157704 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_157704 prefixEnd_157704 := by exact prefixLift 157704
  have htrace : WordTrace (prefixWord ++ tailWord_157704) baseStart_157704 baseEnd_157704 := by
    simpa [prefixWord, tailWord_157704, baseEnd_157704] using wordTrace_append hprefix tailTrace_157704
  have hstable : (prefixWord ++ tailWord_157704).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157704).length < 2 ^ (prefixWord ++ tailWord_157704).sum := by decide
  have hdescent : baseEnd_157704 < baseStart_157704 := by decide
  rcases family_descends (prefixWord ++ tailWord_157704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157717 : List Nat := [1, 3, 2, 1, 6, 1, 2, 3]
def baseStart_157717 : Nat := 118140960795 + 157717 * 2 ^ 59
def prefixEnd_157717 : Nat := 4983230072969 + 3 ^ 40 * 157717 * 2
def baseEnd_157717 : Nat := 47990890894971653459069

theorem tailTrace_157717 : CollatzResearch.WordTrace tailWord_157717 prefixEnd_157717 47990890894971653459069 := by
  unfold tailWord_157717
  simp only [CollatzResearch.WordTrace]
  refine ⟨5752411569625719764231405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3834941046417146509487603 5752411569625719764231405)
  ·
    refine ⟨2157154338609644911586777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5752411569625719764231405 2157154338609644911586777)
    ·
      refine ⟨1617865753957233683690083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2157154338609644911586777 1617865753957233683690083)
      ·
        refine ⟨2426798630935850525535125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1617865753957233683690083 2426798630935850525535125)
        ·
          refine ⟨113756185825117993384459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2426798630935850525535125 113756185825117993384459)
          ·
            refine ⟨170634278737676990076689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113756185825117993384459 170634278737676990076689)
            ·
              refine ⟨127975709053257742557517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170634278737676990076689 127975709053257742557517)
              ·
                refine ⟨47990890894971653459069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127975709053257742557517 47990890894971653459069)
                ·
                  rfl

theorem cell19_157717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 3].length) (baseStart_157717 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_157717 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_157717 prefixEnd_157717 := by exact prefixLift 157717
  have htrace : WordTrace (prefixWord ++ tailWord_157717) baseStart_157717 baseEnd_157717 := by
    simpa [prefixWord, tailWord_157717, baseEnd_157717] using wordTrace_append hprefix tailTrace_157717
  have hstable : (prefixWord ++ tailWord_157717).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157717).length < 2 ^ (prefixWord ++ tailWord_157717).sum := by decide
  have hdescent : baseEnd_157717 < baseStart_157717 := by decide
  rcases family_descends (prefixWord ++ tailWord_157717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157736 : List Nat := [2, 1, 5, 3, 2, 1, 5]
def baseStart_157736 : Nat := 118140960795 + 157736 * 2 ^ 59
def prefixEnd_157736 : Nat := 4983230072969 + 3 ^ 40 * 157736 * 2
def baseEnd_157736 : Nat := 15998890768928413012265

theorem tailTrace_157736 : CollatzResearch.WordTrace tailWord_157736 prefixEnd_157736 15998890768928413012265 := by
  unfold tailWord_157736
  simp only [CollatzResearch.WordTrace]
  refine ⟨2876552278278443004586531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3835403037704590672782041 2876552278278443004586531)
  ·
    refine ⟨4314828417417664506879797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2876552278278443004586531 4314828417417664506879797)
    ·
      refine ⟨404515164132906047519981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4314828417417664506879797 404515164132906047519981)
      ·
        refine ⟨151693186549839767819993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 404515164132906047519981 151693186549839767819993)
        ·
          refine ⟨113769889912379825864995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151693186549839767819993 113769889912379825864995)
          ·
            refine ⟨170654834868569738797493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113769889912379825864995 170654834868569738797493)
            ·
              refine ⟨15998890768928413012265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 170654834868569738797493 15998890768928413012265)
              ·
                rfl

theorem cell19_157736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 5].length) (baseStart_157736 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_157736 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_157736 prefixEnd_157736 := by exact prefixLift 157736
  have htrace : WordTrace (prefixWord ++ tailWord_157736) baseStart_157736 baseEnd_157736 := by
    simpa [prefixWord, tailWord_157736, baseEnd_157736] using wordTrace_append hprefix tailTrace_157736
  have hstable : (prefixWord ++ tailWord_157736).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157736).length < 2 ^ (prefixWord ++ tailWord_157736).sum := by decide
  have hdescent : baseEnd_157736 < baseStart_157736 := by decide
  rcases family_descends (prefixWord ++ tailWord_157736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157814 : List Nat := [5, 1, 1, 2, 1, 4, 1, 4]
def baseStart_157814 : Nat := 118140960795 + 157814 * 2 ^ 59
def prefixEnd_157814 : Nat := 4983230072969 + 3 ^ 40 * 157814 * 2
def baseEnd_157814 : Nat := 48020406523704169303249

theorem tailTrace_157814 : CollatzResearch.WordTrace tailWord_157814 prefixEnd_157814 48020406523704169303249 := by
  unfold tailWord_157814
  simp only [CollatzResearch.WordTrace]
  refine ⟨359746840642144083157031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3837299633516203553674997 359746840642144083157031)
  ·
    refine ⟨539620260963216124735547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 359746840642144083157031 539620260963216124735547)
    ·
      refine ⟨809430391444824187103321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 539620260963216124735547 809430391444824187103321)
      ·
        refine ⟨607072793583618140327491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 809430391444824187103321 607072793583618140327491)
        ·
          refine ⟨910609190375427210491237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 607072793583618140327491 910609190375427210491237)
          ·
            refine ⟨170739223195392601967107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 910609190375427210491237 170739223195392601967107)
            ·
              refine ⟨256108834793088902950661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170739223195392601967107 256108834793088902950661)
              ·
                refine ⟨48020406523704169303249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 256108834793088902950661 48020406523704169303249)
                ·
                  rfl

theorem cell19_157814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_157814 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_157814 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_157814 prefixEnd_157814 := by exact prefixLift 157814
  have htrace : WordTrace (prefixWord ++ tailWord_157814) baseStart_157814 baseEnd_157814 := by
    simpa [prefixWord, tailWord_157814, baseEnd_157814] using wordTrace_append hprefix tailTrace_157814
  have hstable : (prefixWord ++ tailWord_157814).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157814).length < 2 ^ (prefixWord ++ tailWord_157814).sum := by decide
  have hdescent : baseEnd_157814 < baseStart_157814 := by decide
  rcases family_descends (prefixWord ++ tailWord_157814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157856 : List Nat := [2, 1, 1, 4, 2, 3, 6]
def baseStart_157856 : Nat := 118140960795 + 157856 * 2 ^ 59
def prefixEnd_157856 : Nat := 4983230072969 + 3 ^ 40 * 157856 * 2
def baseEnd_157856 : Nat := 16011062162220172123267

theorem tailTrace_157856 : CollatzResearch.WordTrace tailWord_157856 prefixEnd_157856 16011062162220172123267 := by
  unfold tailWord_157856
  simp only [CollatzResearch.WordTrace]
  refine ⟨2878740658061073251770711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3838320877414764335694281 2878740658061073251770711)
  ·
    refine ⟨4318110987091609877656067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2878740658061073251770711 4318110987091609877656067)
    ·
      refine ⟨6477166480637414816484101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4318110987091609877656067 6477166480637414816484101)
      ·
        refine ⟨1214468715119515278090769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6477166480637414816484101 1214468715119515278090769)
        ·
          refine ⟨910851536339636458568077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1214468715119515278090769 910851536339636458568077)
          ·
            refine ⟨341569326127363671963029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 910851536339636458568077 341569326127363671963029)
            ·
              refine ⟨16011062162220172123267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 341569326127363671963029 16011062162220172123267)
              ·
                rfl

theorem cell19_157856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 6].length) (baseStart_157856 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_157856 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_157856 prefixEnd_157856 := by exact prefixLift 157856
  have htrace : WordTrace (prefixWord ++ tailWord_157856) baseStart_157856 baseEnd_157856 := by
    simpa [prefixWord, tailWord_157856, baseEnd_157856] using wordTrace_append hprefix tailTrace_157856
  have hstable : (prefixWord ++ tailWord_157856).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157856).length < 2 ^ (prefixWord ++ tailWord_157856).sum := by decide
  have hdescent : baseEnd_157856 < baseStart_157856 := by decide
  rcases family_descends (prefixWord ++ tailWord_157856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157892 : List Nat := [2, 3, 3, 1, 2, 2, 1, 5]
def baseStart_157892 : Nat := 118140960795 + 157892 * 2 ^ 59
def prefixEnd_157892 : Nat := 4983230072969 + 3 ^ 40 * 157892 * 2
def baseEnd_157892 : Nat := 48044140740623099569703

theorem tailTrace_157892 : CollatzResearch.WordTrace tailWord_157892 prefixEnd_157892 48044140740623099569703 := by
  unfold tailWord_157892
  simp only [CollatzResearch.WordTrace]
  refine ⟨2879397171995862325925965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3839196229327816434567953 2879397171995862325925965)
  ·
    refine ⟨1079773939498448372222237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2879397171995862325925965 1079773939498448372222237)
    ·
      refine ⟨404915227311918139583339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1079773939498448372222237 404915227311918139583339)
      ·
        refine ⟨607372840967877209375009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 404915227311918139583339 607372840967877209375009)
        ·
          refine ⟨455529630725907907031257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 607372840967877209375009 455529630725907907031257)
          ·
            refine ⟨341647223044430930273443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 455529630725907907031257 341647223044430930273443)
            ·
              refine ⟨512470834566646395410165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 341647223044430930273443 512470834566646395410165)
              ·
                refine ⟨48044140740623099569703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 512470834566646395410165 48044140740623099569703)
                ·
                  rfl

theorem cell19_157892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 5].length) (baseStart_157892 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_157892 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_157892 prefixEnd_157892 := by exact prefixLift 157892
  have htrace : WordTrace (prefixWord ++ tailWord_157892) baseStart_157892 baseEnd_157892 := by
    simpa [prefixWord, tailWord_157892, baseEnd_157892] using wordTrace_append hprefix tailTrace_157892
  have hstable : (prefixWord ++ tailWord_157892).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157892).length < 2 ^ (prefixWord ++ tailWord_157892).sum := by decide
  have hdescent : baseEnd_157892 < baseStart_157892 := by decide
  rcases family_descends (prefixWord ++ tailWord_157892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157909 : List Nat := [1, 3, 2, 4, 3, 1, 5]
def baseStart_157909 : Nat := 118140960795 + 157909 * 2 ^ 59
def prefixEnd_157909 : Nat := 4983230072969 + 3 ^ 40 * 157909 * 2
def baseEnd_157909 : Nat := 16016437860924032397293

theorem tailTrace_157909 : CollatzResearch.WordTrace tailWord_157909 prefixEnd_157909 16016437860924032397293 := by
  unfold tailWord_157909
  simp only [CollatzResearch.WordTrace]
  refine ⟨5759414384930136555220781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3839609589953424370147187 5759414384930136555220781)
  ·
    refine ⟨2159780394348801208207793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5759414384930136555220781 2159780394348801208207793)
    ·
      refine ⟨1619835295761600906155845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2159780394348801208207793 1619835295761600906155845)
      ·
        refine ⟨303719117955300169904221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1619835295761600906155845 303719117955300169904221)
        ·
          refine ⟨113894669233237563714083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 303719117955300169904221 113894669233237563714083)
          ·
            refine ⟨170842003849856345571125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113894669233237563714083 170842003849856345571125)
            ·
              refine ⟨16016437860924032397293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 170842003849856345571125 16016437860924032397293)
              ·
                rfl

theorem cell19_157909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 5].length) (baseStart_157909 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_157909 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_157909 prefixEnd_157909 := by exact prefixLift 157909
  have htrace : WordTrace (prefixWord ++ tailWord_157909) baseStart_157909 baseEnd_157909 := by
    simpa [prefixWord, tailWord_157909, baseEnd_157909] using wordTrace_append hprefix tailTrace_157909
  have hstable : (prefixWord ++ tailWord_157909).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157909).length < 2 ^ (prefixWord ++ tailWord_157909).sum := by decide
  have hdescent : baseEnd_157909 < baseStart_157909 := by decide
  rcases family_descends (prefixWord ++ tailWord_157909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157932 : List Nat := [2, 2, 1, 1, 2, 3, 4, 4]
def baseStart_157932 : Nat := 118140960795 + 157932 * 2 ^ 59
def prefixEnd_157932 : Nat := 4983230072969 + 3 ^ 40 * 157932 * 2
def baseEnd_157932 : Nat := 48056312133914858680705

theorem tailTrace_157932 : CollatzResearch.WordTrace tailWord_157932 prefixEnd_157932 48056312133914858680705 := by
  unfold tailWord_157932
  simp only [CollatzResearch.WordTrace]
  refine ⟨2880126631923405741654025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3840168842564540988872033 2880126631923405741654025)
  ·
    refine ⟨2160094973942554306240519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2880126631923405741654025 2160094973942554306240519)
    ·
      refine ⟨3240142460913831459360779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2160094973942554306240519 3240142460913831459360779)
      ·
        refine ⟨4860213691370747189041169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3240142460913831459360779 4860213691370747189041169)
        ·
          refine ⟨3645160268528060391780877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4860213691370747189041169 3645160268528060391780877)
          ·
            refine ⟨1366935100698022646917829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3645160268528060391780877 1366935100698022646917829)
            ·
              refine ⟨256300331380879246297093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1366935100698022646917829 256300331380879246297093)
              ·
                refine ⟨48056312133914858680705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 256300331380879246297093 48056312133914858680705)
                ·
                  rfl

theorem cell19_157932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 4].length) (baseStart_157932 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_157932 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_157932 prefixEnd_157932 := by exact prefixLift 157932
  have htrace : WordTrace (prefixWord ++ tailWord_157932) baseStart_157932 baseEnd_157932 := by
    simpa [prefixWord, tailWord_157932, baseEnd_157932] using wordTrace_append hprefix tailTrace_157932
  have hstable : (prefixWord ++ tailWord_157932).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157932).length < 2 ^ (prefixWord ++ tailWord_157932).sum := by decide
  have hdescent : baseEnd_157932 < baseStart_157932 := by decide
  rcases family_descends (prefixWord ++ tailWord_157932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157970 : List Nat := [3, 2, 4, 10]
def baseStart_157970 : Nat := 118140960795 + 157970 * 2 ^ 59
def prefixEnd_157970 : Nat := 4983230072969 + 3 ^ 40 * 157970 * 2
def baseEnd_157970 : Nat := 593430555031383084397

theorem tailTrace_157970 : CollatzResearch.WordTrace tailWord_157970 prefixEnd_157970 593430555031383084397 := by
  unfold tailWord_157970
  simp only [CollatzResearch.WordTrace]
  refine ⟨1440409809427285993297841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3841092825139429315460909 1440409809427285993297841)
  ·
    refine ⟨1080307357070464494973381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1440409809427285993297841 1080307357070464494973381)
    ·
      refine ⟨202557629450712092807509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1080307357070464494973381 202557629450712092807509)
      ·
        refine ⟨593430555031383084397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 202557629450712092807509 593430555031383084397)
        ·
          rfl

theorem cell19_157970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 10].length) (baseStart_157970 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_157970 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_157970 prefixEnd_157970 := by exact prefixLift 157970
  have htrace : WordTrace (prefixWord ++ tailWord_157970) baseStart_157970 baseEnd_157970 := by
    simpa [prefixWord, tailWord_157970, baseEnd_157970] using wordTrace_append hprefix tailTrace_157970
  have hstable : (prefixWord ++ tailWord_157970).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157970).length < 2 ^ (prefixWord ++ tailWord_157970).sum := by decide
  have hdescent : baseEnd_157970 < baseStart_157970 := by decide
  rcases family_descends (prefixWord ++ tailWord_157970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158004 : List Nat := [2, 5, 1, 1, 1, 3, 3, 3]
def baseStart_158004 : Nat := 118140960795 + 158004 * 2 ^ 59
def prefixEnd_158004 : Nat := 4983230072969 + 3 ^ 40 * 158004 * 2
def baseEnd_158004 : Nat := 48078220641840025080509

theorem tailTrace_158004 : CollatzResearch.WordTrace tailWord_158004 prefixEnd_158004 48078220641840025080509 := by
  unfold tailWord_158004
  simp only [CollatzResearch.WordTrace]
  refine ⟨2881439659792983889964533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3841919546390645186619377 2881439659792983889964533)
  ·
    refine ⟨270134968105592239684175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2881439659792983889964533 270134968105592239684175)
    ·
      refine ⟨405202452158388359526263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270134968105592239684175 405202452158388359526263)
      ·
        refine ⟨607803678237582539289395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405202452158388359526263 607803678237582539289395)
        ·
          refine ⟨911705517356373808934093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 607803678237582539289395 911705517356373808934093)
          ·
            refine ⟨341889569008640178350285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 911705517356373808934093 341889569008640178350285)
            ·
              refine ⟨128208588378240066881357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 341889569008640178350285 128208588378240066881357)
              ·
                refine ⟨48078220641840025080509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128208588378240066881357 48078220641840025080509)
                ·
                  rfl

theorem cell19_158004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 3].length) (baseStart_158004 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_158004 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_158004 prefixEnd_158004 := by exact prefixLift 158004
  have htrace : WordTrace (prefixWord ++ tailWord_158004) baseStart_158004 baseEnd_158004 := by
    simpa [prefixWord, tailWord_158004, baseEnd_158004] using wordTrace_append hprefix tailTrace_158004
  have hstable : (prefixWord ++ tailWord_158004).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158004).length < 2 ^ (prefixWord ++ tailWord_158004).sum := by decide
  have hdescent : baseEnd_158004 < baseStart_158004 := by decide
  rcases family_descends (prefixWord ++ tailWord_158004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158067 : List Nat := [1, 1, 1, 2, 2, 1, 2, 9]
def baseStart_158067 : Nat := 118140960795 + 158067 * 2 ^ 59
def prefixEnd_158067 : Nat := 4983230072969 + 3 ^ 40 * 158067 * 2
def baseEnd_158067 : Nat := 48097390586274545680337

theorem tailTrace_158067 : CollatzResearch.WordTrace tailWord_158067 prefixEnd_158067 48097390586274545680337 := by
  unfold tailWord_158067
  simp only [CollatzResearch.WordTrace]
  refine ⟨5765177118357729539472455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3843451412238486359648303 5765177118357729539472455)
  ·
    refine ⟨8647765677536594309208683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5765177118357729539472455 8647765677536594309208683)
    ·
      refine ⟨12971648516304891463813025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8647765677536594309208683 12971648516304891463813025)
      ·
        refine ⟨9728736387228668597859769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12971648516304891463813025 9728736387228668597859769)
        ·
          refine ⟨7296552290421501448394827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9728736387228668597859769 7296552290421501448394827)
          ·
            refine ⟨10944828435632252172592241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7296552290421501448394827 10944828435632252172592241)
            ·
              refine ⟨8208621326724189129444181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10944828435632252172592241 8208621326724189129444181)
              ·
                refine ⟨48097390586274545680337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8208621326724189129444181 48097390586274545680337)
                ·
                  rfl

theorem cell19_158067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 9].length) (baseStart_158067 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_158067 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_158067 prefixEnd_158067 := by exact prefixLift 158067
  have htrace : WordTrace (prefixWord ++ tailWord_158067) baseStart_158067 baseEnd_158067 := by
    simpa [prefixWord, tailWord_158067, baseEnd_158067] using wordTrace_append hprefix tailTrace_158067
  have hstable : (prefixWord ++ tailWord_158067).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158067).length < 2 ^ (prefixWord ++ tailWord_158067).sum := by decide
  have hdescent : baseEnd_158067 < baseStart_158067 := by decide
  rcases family_descends (prefixWord ++ tailWord_158067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158120 : List Nat := [2, 1, 6, 1, 1, 1, 2, 5]
def baseStart_158120 : Nat := 118140960795 + 158120 * 2 ^ 59
def prefixEnd_158120 : Nat := 4983230072969 + 3 ^ 40 * 158120 * 2
def baseEnd_158120 : Nat := 48113517682386126502415

theorem tailTrace_158120 : CollatzResearch.WordTrace tailWord_158120 prefixEnd_158120 48113517682386126502415 := by
  unfold tailWord_158120
  simp only [CollatzResearch.WordTrace]
  refine ⟨2883555093582859795575907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3844740124777146394101209 2883555093582859795575907)
  ·
    refine ⟨4325332640374289693363861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2883555093582859795575907 4325332640374289693363861)
    ·
      refine ⟨202749967517544829376431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4325332640374289693363861 202749967517544829376431)
      ·
        refine ⟨304124951276317244064647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202749967517544829376431 304124951276317244064647)
        ·
          refine ⟨456187426914475866096971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304124951276317244064647 456187426914475866096971)
          ·
            refine ⟨684281140371713799145457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 456187426914475866096971 684281140371713799145457)
            ·
              refine ⟨513210855278785349359093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 684281140371713799145457 513210855278785349359093)
              ·
                refine ⟨48113517682386126502415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 513210855278785349359093 48113517682386126502415)
                ·
                  rfl

theorem cell19_158120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 5].length) (baseStart_158120 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_158120 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_158120 prefixEnd_158120 := by exact prefixLift 158120
  have htrace : WordTrace (prefixWord ++ tailWord_158120) baseStart_158120 baseEnd_158120 := by
    simpa [prefixWord, tailWord_158120, baseEnd_158120] using wordTrace_append hprefix tailTrace_158120
  have hstable : (prefixWord ++ tailWord_158120).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158120).length < 2 ^ (prefixWord ++ tailWord_158120).sum := by decide
  have hdescent : baseEnd_158120 < baseStart_158120 := by decide
  rcases family_descends (prefixWord ++ tailWord_158120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158156 : List Nat := [2, 2, 1, 4, 4, 1, 1, 4]
def baseStart_158156 : Nat := 118140960795 + 158156 * 2 ^ 59
def prefixEnd_158156 : Nat := 4983230072969 + 3 ^ 40 * 158156 * 2
def baseEnd_158156 : Nat := 48124471936348709702317

theorem tailTrace_158156 : CollatzResearch.WordTrace tailWord_158156 prefixEnd_158156 48124471936348709702317 := by
  unfold tailWord_158156
  simp only [CollatzResearch.WordTrace]
  refine ⟨2884211607517648869731161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3845615476690198492974881 2884211607517648869731161)
  ·
    refine ⟨2163158705638236652298371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2884211607517648869731161 2163158705638236652298371)
    ·
      refine ⟨3244738058457354978447557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2163158705638236652298371 3244738058457354978447557)
      ·
        refine ⟨608388385960754058458917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3244738058457354978447557 608388385960754058458917)
        ·
          refine ⟨114072822367641385961047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 608388385960754058458917 114072822367641385961047)
          ·
            refine ⟨171109233551462078941571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114072822367641385961047 171109233551462078941571)
            ·
              refine ⟨256663850327193118412357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171109233551462078941571 256663850327193118412357)
              ·
                refine ⟨48124471936348709702317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 256663850327193118412357 48124471936348709702317)
                ·
                  rfl

theorem cell19_158156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 4].length) (baseStart_158156 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_158156 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_158156 prefixEnd_158156 := by exact prefixLift 158156
  have htrace : WordTrace (prefixWord ++ tailWord_158156) baseStart_158156 baseEnd_158156 := by
    simpa [prefixWord, tailWord_158156, baseEnd_158156] using wordTrace_append hprefix tailTrace_158156
  have hstable : (prefixWord ++ tailWord_158156).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158156).length < 2 ^ (prefixWord ++ tailWord_158156).sum := by decide
  have hdescent : baseEnd_158156 < baseStart_158156 := by decide
  rcases family_descends (prefixWord ++ tailWord_158156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158198 : List Nat := [5, 1, 1, 1, 2, 1, 8]
def baseStart_158198 : Nat := 118140960795 + 158198 * 2 ^ 59
def prefixEnd_158198 : Nat := 4983230072969 + 3 ^ 40 * 158198 * 2
def baseEnd_158198 : Nat := 16045750633101685589623

theorem tailTrace_158198 : CollatzResearch.WordTrace tailWord_158198 prefixEnd_158198 16045750633101685589623 := by
  unfold tailWord_158198
  simp only [CollatzResearch.WordTrace]
  refine ⟨360622192555196182030703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3846636720588759274994165 360622192555196182030703)
  ·
    refine ⟨540933288832794273046055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 360622192555196182030703 540933288832794273046055)
    ·
      refine ⟨811399933249191409569083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 540933288832794273046055 811399933249191409569083)
      ·
        refine ⟨1217099899873787114353625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 811399933249191409569083 1217099899873787114353625)
        ·
          refine ⟨912824924905340335765219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1217099899873787114353625 912824924905340335765219)
          ·
            refine ⟨1369237387358010503647829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 912824924905340335765219 1369237387358010503647829)
            ·
              refine ⟨16045750633101685589623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1369237387358010503647829 16045750633101685589623)
              ·
                rfl

theorem cell19_158198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 8].length) (baseStart_158198 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_158198 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_158198 prefixEnd_158198 := by exact prefixLift 158198
  have htrace : WordTrace (prefixWord ++ tailWord_158198) baseStart_158198 baseEnd_158198 := by
    simpa [prefixWord, tailWord_158198, baseEnd_158198] using wordTrace_append hprefix tailTrace_158198
  have hstable : (prefixWord ++ tailWord_158198).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158198).length < 2 ^ (prefixWord ++ tailWord_158198).sum := by decide
  have hdescent : baseEnd_158198 < baseStart_158198 := by decide
  rcases family_descends (prefixWord ++ tailWord_158198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158200 : List Nat := [2, 1, 2, 1, 1, 4, 8]
def baseStart_158200 : Nat := 118140960795 + 158200 * 2 ^ 59
def prefixEnd_158200 : Nat := 4983230072969 + 3 ^ 40 * 158200 * 2
def baseEnd_158200 : Nat := 16045953489656548241473

theorem tailTrace_158200 : CollatzResearch.WordTrace tailWord_158200 prefixEnd_158200 16045953489656548241473 := by
  unfold tailWord_158200
  simp only [CollatzResearch.WordTrace]
  refine ⟨2885014013437946627032027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3846685351250595502709369 2885014013437946627032027)
  ·
    refine ⟨4327521020156919940548041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2885014013437946627032027 4327521020156919940548041)
    ·
      refine ⟨3245640765117689955411031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4327521020156919940548041 3245640765117689955411031)
      ·
        refine ⟨4868461147676534933116547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3245640765117689955411031 4868461147676534933116547)
        ·
          refine ⟨7302691721514802399674821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4868461147676534933116547 7302691721514802399674821)
          ·
            refine ⟨1369254697784025449939029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7302691721514802399674821 1369254697784025449939029)
            ·
              refine ⟨16045953489656548241473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1369254697784025449939029 16045953489656548241473)
              ·
                rfl

theorem cell19_158200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 8].length) (baseStart_158200 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_158200 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_158200 prefixEnd_158200 := by exact prefixLift 158200
  have htrace : WordTrace (prefixWord ++ tailWord_158200) baseStart_158200 baseEnd_158200 := by
    simpa [prefixWord, tailWord_158200, baseEnd_158200] using wordTrace_append hprefix tailTrace_158200
  have hstable : (prefixWord ++ tailWord_158200).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158200).length < 2 ^ (prefixWord ++ tailWord_158200).sum := by decide
  have hdescent : baseEnd_158200 < baseStart_158200 := by decide
  rcases family_descends (prefixWord ++ tailWord_158200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158236 : List Nat := [2, 2, 3, 1, 2, 3, 1, 5]
def baseStart_158236 : Nat := 118140960795 + 158236 * 2 ^ 59
def prefixEnd_158236 : Nat := 4983230072969 + 3 ^ 40 * 158236 * 2
def baseEnd_158236 : Nat := 48148814722932227924321

theorem tailTrace_158236 : CollatzResearch.WordTrace tailWord_158236 prefixEnd_158236 48148814722932227924321 := by
  unfold tailWord_158236
  simp only [CollatzResearch.WordTrace]
  refine ⟨2885670527372735701187281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3847560703163647601583041 2885670527372735701187281)
  ·
    refine ⟨2164252895529551775890461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2885670527372735701187281 2164252895529551775890461)
    ·
      refine ⟨811594835823581915958923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2164252895529551775890461 811594835823581915958923)
      ·
        refine ⟨1217392253735372873938385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 811594835823581915958923 1217392253735372873938385)
        ·
          refine ⟨913044190301529655453789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1217392253735372873938385 913044190301529655453789)
          ·
            refine ⟨342391571363073620795171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 913044190301529655453789 342391571363073620795171)
            ·
              refine ⟨513587357044610431192757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342391571363073620795171 513587357044610431192757)
              ·
                refine ⟨48148814722932227924321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 513587357044610431192757 48148814722932227924321)
                ·
                  rfl

theorem cell19_158236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 5].length) (baseStart_158236 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_158236 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_158236 prefixEnd_158236 := by exact prefixLift 158236
  have htrace : WordTrace (prefixWord ++ tailWord_158236) baseStart_158236 baseEnd_158236 := by
    simpa [prefixWord, tailWord_158236, baseEnd_158236] using wordTrace_append hprefix tailTrace_158236
  have hstable : (prefixWord ++ tailWord_158236).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158236).length < 2 ^ (prefixWord ++ tailWord_158236).sum := by decide
  have hdescent : baseEnd_158236 < baseStart_158236 := by decide
  rcases family_descends (prefixWord ++ tailWord_158236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158257 : List Nat := [1, 2, 2, 3, 1, 1, 9]
def baseStart_158257 : Nat := 118140960795 + 158257 * 2 ^ 59
def prefixEnd_158257 : Nat := 4983230072969 + 3 ^ 40 * 158257 * 2
def baseEnd_158257 : Nat := 16051734901470133819199

theorem tailTrace_158257 : CollatzResearch.WordTrace tailWord_158257 prefixEnd_158257 16051734901470133819199 := by
  unfold tailWord_158257
  simp only [CollatzResearch.WordTrace]
  refine ⟨5772106987669391988889025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3848071325112927992592683 5772106987669391988889025)
  ·
    refine ⟨4329080240752043991666769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5772106987669391988889025 4329080240752043991666769)
    ·
      refine ⟨3246810180564032993750077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4329080240752043991666769 3246810180564032993750077)
      ·
        refine ⟨1217553817711512372656279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3246810180564032993750077 1217553817711512372656279)
        ·
          refine ⟨1826330726567268558984419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1217553817711512372656279 1826330726567268558984419)
          ·
            refine ⟨2739496089850902838476629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1826330726567268558984419 2739496089850902838476629)
            ·
              refine ⟨16051734901470133819199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2739496089850902838476629 16051734901470133819199)
              ·
                rfl

theorem cell19_158257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 9].length) (baseStart_158257 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_158257 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_158257 prefixEnd_158257 := by exact prefixLift 158257
  have htrace : WordTrace (prefixWord ++ tailWord_158257) baseStart_158257 baseEnd_158257 := by
    simpa [prefixWord, tailWord_158257, baseEnd_158257] using wordTrace_append hprefix tailTrace_158257
  have hstable : (prefixWord ++ tailWord_158257).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158257).length < 2 ^ (prefixWord ++ tailWord_158257).sum := by decide
  have hdescent : baseEnd_158257 < baseStart_158257 := by decide
  rcases family_descends (prefixWord ++ tailWord_158257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158270 : List Nat := [4, 2, 1, 4, 1, 1, 2, 4]
def baseStart_158270 : Nat := 118140960795 + 158270 * 2 ^ 59
def prefixEnd_158270 : Nat := 4983230072969 + 3 ^ 40 * 158270 * 2
def baseEnd_158270 : Nat := 48159160407230223168673

theorem tailTrace_158270 : CollatzResearch.WordTrace tailWord_158270 prefixEnd_158270 48159160407230223168673 := by
  unfold tailWord_158270
  simp only [CollatzResearch.WordTrace]
  refine ⟨721572642077786901139033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3848387424414863472741509 721572642077786901139033)
  ·
    refine ⟨541179481558340175854275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 721572642077786901139033 541179481558340175854275)
    ·
      refine ⟨811769222337510263781413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 541179481558340175854275 811769222337510263781413)
      ·
        refine ⟨152206729188283174459015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 811769222337510263781413 152206729188283174459015)
        ·
          refine ⟨228310093782424761688523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152206729188283174459015 228310093782424761688523)
          ·
            refine ⟨342465140673637142532785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228310093782424761688523 342465140673637142532785)
            ·
              refine ⟨256848855505227856899589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 342465140673637142532785 256848855505227856899589)
              ·
                refine ⟨48159160407230223168673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 256848855505227856899589 48159160407230223168673)
                ·
                  rfl

theorem cell19_158270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_158270 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_158270 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_158270 prefixEnd_158270 := by exact prefixLift 158270
  have htrace : WordTrace (prefixWord ++ tailWord_158270) baseStart_158270 baseEnd_158270 := by
    simpa [prefixWord, tailWord_158270, baseEnd_158270] using wordTrace_append hprefix tailTrace_158270
  have hstable : (prefixWord ++ tailWord_158270).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158270).length < 2 ^ (prefixWord ++ tailWord_158270).sum := by decide
  have hdescent : baseEnd_158270 < baseStart_158270 := by decide
  rcases family_descends (prefixWord ++ tailWord_158270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158295 : List Nat := [1, 1, 3, 2, 2, 2, 1, 7]
def baseStart_158295 : Nat := 118140960795 + 158295 * 2 ^ 59
def prefixEnd_158295 : Nat := 4983230072969 + 3 ^ 40 * 158295 * 2
def baseEnd_158295 : Nat := 48166767528037572613049

theorem tailTrace_158295 : CollatzResearch.WordTrace tailWord_158295 prefixEnd_158295 48166767528037572613049 := by
  unfold tailWord_158295
  simp only [CollatzResearch.WordTrace]
  refine ⟨5773492961531724478772339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3848995307687816319181559 5773492961531724478772339)
  ·
    refine ⟨8660239442297586718158509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5773492961531724478772339 8660239442297586718158509)
    ·
      refine ⟨3247589790861595019309441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8660239442297586718158509 3247589790861595019309441)
      ·
        refine ⟨2435692343146196264482081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3247589790861595019309441 2435692343146196264482081)
        ·
          refine ⟨1826769257359647198361561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2435692343146196264482081 1826769257359647198361561)
          ·
            refine ⟨1370076943019735398771171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1826769257359647198361561 1370076943019735398771171)
            ·
              refine ⟨2055115414529603098156757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1370076943019735398771171 2055115414529603098156757)
              ·
                refine ⟨48166767528037572613049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2055115414529603098156757 48166767528037572613049)
                ·
                  rfl

theorem cell19_158295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 7].length) (baseStart_158295 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_158295 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_158295 prefixEnd_158295 := by exact prefixLift 158295
  have htrace : WordTrace (prefixWord ++ tailWord_158295) baseStart_158295 baseEnd_158295 := by
    simpa [prefixWord, tailWord_158295, baseEnd_158295] using wordTrace_append hprefix tailTrace_158295
  have hstable : (prefixWord ++ tailWord_158295).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158295).length < 2 ^ (prefixWord ++ tailWord_158295).sum := by decide
  have hdescent : baseEnd_158295 < baseStart_158295 := by decide
  rcases family_descends (prefixWord ++ tailWord_158295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158312 : List Nat := [2, 1, 4, 3, 2, 7]
def baseStart_158312 : Nat := 118140960795 + 158312 * 2 ^ 59
def prefixEnd_158312 : Nat := 4983230072969 + 3 ^ 40 * 158312 * 2
def baseEnd_158312 : Nat := 5352437818909618915025

theorem tailTrace_158312 : CollatzResearch.WordTrace tailWord_158312 prefixEnd_158312 5352437818909618915025 := by
  unfold tailWord_158312
  simp only [CollatzResearch.WordTrace]
  refine ⟨2887056501235068191070595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3849408668313424254760793 2887056501235068191070595)
  ·
    refine ⟨4330584751852602286605893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2887056501235068191070595 4330584751852602286605893)
    ·
      refine ⟨811984640972362928738605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4330584751852602286605893 811984640972362928738605)
      ·
        refine ⟨304494240364636098276977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 811984640972362928738605 304494240364636098276977)
        ·
          refine ⟨228370680273477073707733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304494240364636098276977 228370680273477073707733)
          ·
            refine ⟨5352437818909618915025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 228370680273477073707733 5352437818909618915025)
            ·
              rfl

theorem cell19_158312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 7].length) (baseStart_158312 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_158312 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_158312 prefixEnd_158312 := by exact prefixLift 158312
  have htrace : WordTrace (prefixWord ++ tailWord_158312) baseStart_158312 baseEnd_158312 := by
    simpa [prefixWord, tailWord_158312, baseEnd_158312] using wordTrace_append hprefix tailTrace_158312
  have hstable : (prefixWord ++ tailWord_158312).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158312).length < 2 ^ (prefixWord ++ tailWord_158312).sum := by decide
  have hdescent : baseEnd_158312 < baseStart_158312 := by decide
  rcases family_descends (prefixWord ++ tailWord_158312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158369 : List Nat := [1, 2, 3, 3, 3, 1, 6]
def baseStart_158369 : Nat := 118140960795 + 158369 * 2 ^ 59
def prefixEnd_158369 : Nat := 4983230072969 + 3 ^ 40 * 158369 * 2
def baseEnd_158369 : Nat := 16063094868542442322801

theorem tailTrace_158369 : CollatzResearch.WordTrace tailWord_158369 prefixEnd_158369 16063094868542442322801 := by
  unfold tailWord_158369
  simp only [CollatzResearch.WordTrace]
  refine ⟨5776191963263635116966161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3850794642175756744644107 5776191963263635116966161)
  ·
    refine ⟨4332143972447726337724621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5776191963263635116966161 4332143972447726337724621)
    ·
      refine ⟨1624553989667897376646733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4332143972447726337724621 1624553989667897376646733)
      ·
        refine ⟨609207746125461516242525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1624553989667897376646733 609207746125461516242525)
        ·
          refine ⟨228452904797048068590947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 609207746125461516242525 228452904797048068590947)
          ·
            refine ⟨342679357195572102886421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228452904797048068590947 342679357195572102886421)
            ·
              refine ⟨16063094868542442322801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 342679357195572102886421 16063094868542442322801)
              ·
                rfl

theorem cell19_158369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 6].length) (baseStart_158369 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_158369 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_158369 prefixEnd_158369 := by exact prefixLift 158369
  have htrace : WordTrace (prefixWord ++ tailWord_158369) baseStart_158369 baseEnd_158369 := by
    simpa [prefixWord, tailWord_158369, baseEnd_158369] using wordTrace_append hprefix tailTrace_158369
  have hstable : (prefixWord ++ tailWord_158369).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158369).length < 2 ^ (prefixWord ++ tailWord_158369).sum := by decide
  have hdescent : baseEnd_158369 < baseStart_158369 := by decide
  rcases family_descends (prefixWord ++ tailWord_158369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158401 : List Nat := [1, 2, 6, 2, 1, 2, 2, 3]
def baseStart_158401 : Nat := 118140960795 + 158401 * 2 ^ 59
def prefixEnd_158401 : Nat := 4983230072969 + 3 ^ 40 * 158401 * 2
def baseEnd_158401 : Nat := 48199021720260734257205

theorem tailTrace_158401 : CollatzResearch.WordTrace tailWord_158401 prefixEnd_158401 48199021720260734257205 := by
  unfold tailWord_158401
  simp only [CollatzResearch.WordTrace]
  refine ⟨5777359099147704582131057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3851572732765136388087371 5777359099147704582131057)
  ·
    refine ⟨4333019324360778436598293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5777359099147704582131057 4333019324360778436598293)
    ·
      refine ⟨203110280829411489215545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4333019324360778436598293 203110280829411489215545)
      ·
        refine ⟨152332710622058616911659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203110280829411489215545 152332710622058616911659)
        ·
          refine ⟨228499065933087925367489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152332710622058616911659 228499065933087925367489)
          ·
            refine ⟨171374299449815944025617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228499065933087925367489 171374299449815944025617)
            ·
              refine ⟨128530724587361958019213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171374299449815944025617 128530724587361958019213)
              ·
                refine ⟨48199021720260734257205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128530724587361958019213 48199021720260734257205)
                ·
                  rfl

theorem cell19_158401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 3].length) (baseStart_158401 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_158401 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_158401 prefixEnd_158401 := by exact prefixLift 158401
  have htrace : WordTrace (prefixWord ++ tailWord_158401) baseStart_158401 baseEnd_158401 := by
    simpa [prefixWord, tailWord_158401, baseEnd_158401] using wordTrace_append hprefix tailTrace_158401
  have hstable : (prefixWord ++ tailWord_158401).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158401).length < 2 ^ (prefixWord ++ tailWord_158401).sum := by decide
  have hdescent : baseEnd_158401 < baseStart_158401 := by decide
  rcases family_descends (prefixWord ++ tailWord_158401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158445 : List Nat := [1, 5, 1, 2, 1, 1, 4, 4]
def baseStart_158445 : Nat := 118140960795 + 158445 * 2 ^ 59
def prefixEnd_158445 : Nat := 4983230072969 + 3 ^ 40 * 158445 * 2
def baseEnd_158445 : Nat := 48212410252881669279307

theorem tailTrace_158445 : CollatzResearch.WordTrace tailWord_158445 prefixEnd_158445 48212410252881669279307 := by
  unfold tailWord_158445
  simp only [CollatzResearch.WordTrace]
  refine ⟨5778963910988300096732789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3852642607325533397821859 5778963910988300096732789)
  ·
    refine ⟨541777866655153134068699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5778963910988300096732789 541777866655153134068699)
    ·
      refine ⟨812666799982729701103049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 541777866655153134068699 812666799982729701103049)
      ·
        refine ⟨609500099987047275827287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 812666799982729701103049 609500099987047275827287)
        ·
          refine ⟨914250149980570913740931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 609500099987047275827287 914250149980570913740931)
          ·
            refine ⟨1371375224970856370611397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 914250149980570913740931 1371375224970856370611397)
            ·
              refine ⟨257132854682035569489637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1371375224970856370611397 257132854682035569489637)
              ·
                refine ⟨48212410252881669279307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 257132854682035569489637 48212410252881669279307)
                ·
                  rfl

theorem cell19_158445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 4].length) (baseStart_158445 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_158445 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_158445 prefixEnd_158445 := by exact prefixLift 158445
  have htrace : WordTrace (prefixWord ++ tailWord_158445) baseStart_158445 baseEnd_158445 := by
    simpa [prefixWord, tailWord_158445, baseEnd_158445] using wordTrace_append hprefix tailTrace_158445
  have hstable : (prefixWord ++ tailWord_158445).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158445).length < 2 ^ (prefixWord ++ tailWord_158445).sum := by decide
  have hdescent : baseEnd_158445 < baseStart_158445 := by decide
  rcases family_descends (prefixWord ++ tailWord_158445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158447 : List Nat := [1, 1, 2, 1, 5, 2, 1, 6]
def baseStart_158447 : Nat := 118140960795 + 158447 * 2 ^ 59
def prefixEnd_158447 : Nat := 4983230072969 + 3 ^ 40 * 158447 * 2
def baseEnd_158447 : Nat := 48213018822546257234857

theorem tailTrace_158447 : CollatzResearch.WordTrace tailWord_158447 prefixEnd_158447 48213018822546257234857 := by
  unfold tailWord_158447
  simp only [CollatzResearch.WordTrace]
  refine ⟨5779036856981054438305595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3852691237987369625537063 5779036856981054438305595)
  ·
    refine ⟨8668555285471581657458393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5779036856981054438305595 8668555285471581657458393)
    ·
      refine ⟨6501416464103686243093795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8668555285471581657458393 6501416464103686243093795)
      ·
        refine ⟨9752124696155529364640693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6501416464103686243093795 9752124696155529364640693)
        ·
          refine ⟨914261690264580877935065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9752124696155529364640693 914261690264580877935065)
          ·
            refine ⟨685696267698435658451299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 914261690264580877935065 685696267698435658451299)
            ·
              refine ⟨1028544401547653487676949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 685696267698435658451299 1028544401547653487676949)
              ·
                refine ⟨48213018822546257234857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1028544401547653487676949 48213018822546257234857)
                ·
                  rfl

theorem cell19_158447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 6].length) (baseStart_158447 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_158447 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_158447 prefixEnd_158447 := by exact prefixLift 158447
  have htrace : WordTrace (prefixWord ++ tailWord_158447) baseStart_158447 baseEnd_158447 := by
    simpa [prefixWord, tailWord_158447, baseEnd_158447] using wordTrace_append hprefix tailTrace_158447
  have hstable : (prefixWord ++ tailWord_158447).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158447).length < 2 ^ (prefixWord ++ tailWord_158447).sum := by decide
  have hdescent : baseEnd_158447 < baseStart_158447 := by decide
  rcases family_descends (prefixWord ++ tailWord_158447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158500 : List Nat := [2, 3, 1, 3, 3, 2, 1, 4]
def baseStart_158500 : Nat := 118140960795 + 158500 * 2 ^ 59
def prefixEnd_158500 : Nat := 4983230072969 + 3 ^ 40 * 158500 * 2
def baseEnd_158500 : Nat := 48229145918657838056935

theorem tailTrace_158500 : CollatzResearch.WordTrace tailWord_158500 prefixEnd_158500 48229145918657838056935 := by
  unfold tailWord_158500
  simp only [CollatzResearch.WordTrace]
  refine ⟨2890484962894522244992477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3853979950526029659989969 2890484962894522244992477)
  ·
    refine ⟨1083931861085445841872179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2890484962894522244992477 1083931861085445841872179)
    ·
      refine ⟨1625897791628168762808269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1083931861085445841872179 1625897791628168762808269)
      ·
        refine ⟨609711671860563286053101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1625897791628168762808269 609711671860563286053101)
        ·
          refine ⟨228641876947711232269913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 609711671860563286053101 228641876947711232269913)
          ·
            refine ⟨171481407710783424202435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228641876947711232269913 171481407710783424202435)
            ·
              refine ⟨257222111566175136303653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171481407710783424202435 257222111566175136303653)
              ·
                refine ⟨48229145918657838056935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 257222111566175136303653 48229145918657838056935)
                ·
                  rfl

theorem cell19_158500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 4].length) (baseStart_158500 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_158500 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_158500 prefixEnd_158500 := by exact prefixLift 158500
  have htrace : WordTrace (prefixWord ++ tailWord_158500) baseStart_158500 baseEnd_158500 := by
    simpa [prefixWord, tailWord_158500, baseEnd_158500] using wordTrace_append hprefix tailTrace_158500
  have hstable : (prefixWord ++ tailWord_158500).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158500).length < 2 ^ (prefixWord ++ tailWord_158500).sum := by decide
  have hdescent : baseEnd_158500 < baseStart_158500 := by decide
  rcases family_descends (prefixWord ++ tailWord_158500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158574 : List Nat := [4, 1, 2, 3, 2, 2, 2, 3]
def baseStart_158574 : Nat := 118140960795 + 158574 * 2 ^ 59
def prefixEnd_158574 : Nat := 4983230072969 + 3 ^ 40 * 158574 * 2
def baseEnd_158574 : Nat := 48251662996247592412289

theorem tailTrace_158574 : CollatzResearch.WordTrace tailWord_158574 prefixEnd_158574 48251662996247592412289 := by
  unfold tailWord_158574
  simp only [CollatzResearch.WordTrace]
  refine ⟨722958615940119391022347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3855779285013970085452517 722958615940119391022347)
  ·
    refine ⟨1084437923910179086533521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 722958615940119391022347 1084437923910179086533521)
    ·
      refine ⟨813328442932634314900141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1084437923910179086533521 813328442932634314900141)
      ·
        refine ⟨304998166099737868087553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 813328442932634314900141 304998166099737868087553)
        ·
          refine ⟨228748624574803401065665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304998166099737868087553 228748624574803401065665)
          ·
            refine ⟨171561468431102550799249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228748624574803401065665 171561468431102550799249)
            ·
              refine ⟨128671101323326913099437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171561468431102550799249 128671101323326913099437)
              ·
                refine ⟨48251662996247592412289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128671101323326913099437 48251662996247592412289)
                ·
                  rfl

theorem cell19_158574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_158574 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_158574 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_158574 prefixEnd_158574 := by exact prefixLift 158574
  have htrace : WordTrace (prefixWord ++ tailWord_158574) baseStart_158574 baseEnd_158574 := by
    simpa [prefixWord, tailWord_158574, baseEnd_158574] using wordTrace_append hprefix tailTrace_158574
  have hstable : (prefixWord ++ tailWord_158574).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158574).length < 2 ^ (prefixWord ++ tailWord_158574).sum := by decide
  have hdescent : baseEnd_158574 < baseStart_158574 := by decide
  rcases family_descends (prefixWord ++ tailWord_158574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158578 : List Nat := [3, 2, 1, 2, 1, 1, 6, 3]
def baseStart_158578 : Nat := 118140960795 + 158578 * 2 ^ 59
def prefixEnd_158578 : Nat := 4983230072969 + 3 ^ 40 * 158578 * 2
def baseEnd_158578 : Nat := 48252880135576768323389

theorem tailTrace_158578 : CollatzResearch.WordTrace tailWord_158578 prefixEnd_158578 48252880135576768323389 := by
  unfold tailWord_158578
  simp only [CollatzResearch.WordTrace]
  refine ⟨1445953704876615952831097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3855876546337642540882925 1445953704876615952831097)
  ·
    refine ⟨1084465278657461964623323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1445953704876615952831097 1084465278657461964623323)
    ·
      refine ⟨1626697917986192946934985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1084465278657461964623323 1626697917986192946934985)
      ·
        refine ⟨1220023438489644710201239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1626697917986192946934985 1220023438489644710201239)
        ·
          refine ⟨1830035157734467065301859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1220023438489644710201239 1830035157734467065301859)
          ·
            refine ⟨2745052736601700597952789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1830035157734467065301859 2745052736601700597952789)
            ·
              refine ⟨128674347028204715529037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2745052736601700597952789 128674347028204715529037)
              ·
                refine ⟨48252880135576768323389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128674347028204715529037 48252880135576768323389)
                ·
                  rfl

theorem cell19_158578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 3].length) (baseStart_158578 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_158578 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_158578 prefixEnd_158578 := by exact prefixLift 158578
  have htrace : WordTrace (prefixWord ++ tailWord_158578) baseStart_158578 baseEnd_158578 := by
    simpa [prefixWord, tailWord_158578, baseEnd_158578] using wordTrace_append hprefix tailTrace_158578
  have hstable : (prefixWord ++ tailWord_158578).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158578).length < 2 ^ (prefixWord ++ tailWord_158578).sum := by decide
  have hdescent : baseEnd_158578 < baseStart_158578 := by decide
  rcases family_descends (prefixWord ++ tailWord_158578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158599 : List Nat := [1, 1, 4, 2, 3, 1, 7]
def baseStart_158599 : Nat := 118140960795 + 158599 * 2 ^ 59
def prefixEnd_158599 : Nat := 4983230072969 + 3 ^ 40 * 158599 * 2
def baseEnd_158599 : Nat := 16086423372351647285555

theorem tailTrace_158599 : CollatzResearch.WordTrace tailWord_158599 prefixEnd_158599 16086423372351647285555 := by
  unfold tailWord_158599
  simp only [CollatzResearch.WordTrace]
  refine ⟨5784580752430384397838851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3856387168286922931892567 5784580752430384397838851)
  ·
    refine ⟨8676871128645576596758277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5784580752430384397838851 8676871128645576596758277)
    ·
      refine ⟨1626913336621045611892177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8676871128645576596758277 1626913336621045611892177)
      ·
        refine ⟨1220185002465784208919133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1626913336621045611892177 1220185002465784208919133)
        ·
          refine ⟨457569375924669078344675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1220185002465784208919133 457569375924669078344675)
          ·
            refine ⟨686354063887003617517013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457569375924669078344675 686354063887003617517013)
            ·
              refine ⟨16086423372351647285555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 686354063887003617517013 16086423372351647285555)
              ·
                rfl

theorem cell19_158599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 7].length) (baseStart_158599 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_158599 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_158599 prefixEnd_158599 := by exact prefixLift 158599
  have htrace : WordTrace (prefixWord ++ tailWord_158599) baseStart_158599 baseEnd_158599 := by
    simpa [prefixWord, tailWord_158599, baseEnd_158599] using wordTrace_append hprefix tailTrace_158599
  have hstable : (prefixWord ++ tailWord_158599).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158599).length < 2 ^ (prefixWord ++ tailWord_158599).sum := by decide
  have hdescent : baseEnd_158599 < baseStart_158599 := by decide
  rcases family_descends (prefixWord ++ tailWord_158599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158709 : List Nat := [1, 3, 5, 2, 1, 1, 6]
def baseStart_158709 : Nat := 118140960795 + 158709 * 2 ^ 59
def prefixEnd_158709 : Nat := 4983230072969 + 3 ^ 40 * 158709 * 2
def baseEnd_158709 : Nat := 16097580482869093137307

theorem tailTrace_158709 : CollatzResearch.WordTrace tailWord_158709 prefixEnd_158709 16097580482869093137307 := by
  unfold tailWord_158709
  simp only [CollatzResearch.WordTrace]
  refine ⟨5788592782031873184343181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3859061854687915456228787 5788592782031873184343181)
  ·
    refine ⟨2170722293261952444128693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5788592782031873184343181 2170722293261952444128693)
    ·
      refine ⟨203505214993308041637065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2170722293261952444128693 203505214993308041637065)
      ·
        refine ⟨152628911244981031227799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203505214993308041637065 152628911244981031227799)
        ·
          refine ⟨228943366867471546841699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152628911244981031227799 228943366867471546841699)
          ·
            refine ⟨343415050301207320262549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228943366867471546841699 343415050301207320262549)
            ·
              refine ⟨16097580482869093137307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 343415050301207320262549 16097580482869093137307)
              ·
                rfl

theorem cell19_158709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 6].length) (baseStart_158709 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_158709 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_158709 prefixEnd_158709 := by exact prefixLift 158709
  have htrace : WordTrace (prefixWord ++ tailWord_158709) baseStart_158709 baseEnd_158709 := by
    simpa [prefixWord, tailWord_158709, baseEnd_158709] using wordTrace_append hprefix tailTrace_158709
  have hstable : (prefixWord ++ tailWord_158709).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158709).length < 2 ^ (prefixWord ++ tailWord_158709).sum := by decide
  have hdescent : baseEnd_158709 < baseStart_158709 := by decide
  rcases family_descends (prefixWord ++ tailWord_158709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158749 : List Nat := [1, 4, 2, 2, 3, 1, 1, 5]
def baseStart_158749 : Nat := 118140960795 + 158749 * 2 ^ 59
def prefixEnd_158749 : Nat := 4983230072969 + 3 ^ 40 * 158749 * 2
def baseEnd_158749 : Nat := 48304912841899038522923

theorem tailTrace_158749 : CollatzResearch.WordTrace tailWord_158749 prefixEnd_158749 48304912841899038522923 := by
  unfold tailWord_158749
  simp only [CollatzResearch.WordTrace]
  refine ⟨5790051701886960015799301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3860034467924640010532867 5790051701886960015799301)
  ·
    refine ⟨1085634694103805002962369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5790051701886960015799301 1085634694103805002962369)
    ·
      refine ⟨814226020577853752221777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1085634694103805002962369 814226020577853752221777)
      ·
        refine ⟨610669515433390314166333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 814226020577853752221777 610669515433390314166333)
        ·
          refine ⟨229001068287521367812375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 610669515433390314166333 229001068287521367812375)
          ·
            refine ⟨343501602431282051718563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229001068287521367812375 343501602431282051718563)
            ·
              refine ⟨515252403646923077577845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343501602431282051718563 515252403646923077577845)
              ·
                refine ⟨48304912841899038522923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 515252403646923077577845 48304912841899038522923)
                ·
                  rfl

theorem cell19_158749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 5].length) (baseStart_158749 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_158749 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_158749 prefixEnd_158749 := by exact prefixLift 158749
  have htrace : WordTrace (prefixWord ++ tailWord_158749) baseStart_158749 baseEnd_158749 := by
    simpa [prefixWord, tailWord_158749, baseEnd_158749] using wordTrace_append hprefix tailTrace_158749
  have hstable : (prefixWord ++ tailWord_158749).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158749).length < 2 ^ (prefixWord ++ tailWord_158749).sum := by decide
  have hdescent : baseEnd_158749 < baseStart_158749 := by decide
  rcases family_descends (prefixWord ++ tailWord_158749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158751 : List Nat := [1, 1, 2, 4, 1, 4, 1, 5]
def baseStart_158751 : Nat := 118140960795 + 158751 * 2 ^ 59
def prefixEnd_158751 : Nat := 4983230072969 + 3 ^ 40 * 158751 * 2
def baseEnd_158751 : Nat := 48305521411563626478473

theorem tailTrace_158751 : CollatzResearch.WordTrace tailWord_158751 prefixEnd_158751 48305521411563626478473 := by
  unfold tailWord_158751
  simp only [CollatzResearch.WordTrace]
  refine ⟨5790124647879714357372107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3860083098586476238248071 5790124647879714357372107)
  ·
    refine ⟨8685186971819571536058161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5790124647879714357372107 8685186971819571536058161)
    ·
      refine ⟨6513890228864678652043621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8685186971819571536058161 6513890228864678652043621)
      ·
        refine ⟨1221354417912127247258179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6513890228864678652043621 1221354417912127247258179)
        ·
          refine ⟨1832031626868190870887269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1221354417912127247258179 1832031626868190870887269)
          ·
            refine ⟨343505930037785788291363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1832031626868190870887269 343505930037785788291363)
            ·
              refine ⟨515258895056678682437045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343505930037785788291363 515258895056678682437045)
              ·
                refine ⟨48305521411563626478473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 515258895056678682437045 48305521411563626478473)
                ·
                  rfl

theorem cell19_158751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 5].length) (baseStart_158751 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_158751 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_158751 prefixEnd_158751 := by exact prefixLift 158751
  have htrace : WordTrace (prefixWord ++ tailWord_158751) baseStart_158751 baseEnd_158751 := by
    simpa [prefixWord, tailWord_158751, baseEnd_158751] using wordTrace_append hprefix tailTrace_158751
  have hstable : (prefixWord ++ tailWord_158751).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158751).length < 2 ^ (prefixWord ++ tailWord_158751).sum := by decide
  have hdescent : baseEnd_158751 < baseStart_158751 := by decide
  rcases family_descends (prefixWord ++ tailWord_158751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158867 : List Nat := [1, 1, 1, 2, 1, 2, 4, 7]
def baseStart_158867 : Nat := 118140960795 + 158867 * 2 ^ 59
def prefixEnd_158867 : Nat := 4983230072969 + 3 ^ 40 * 158867 * 2
def baseEnd_158867 : Nat := 48340818452109727900379

theorem tailTrace_158867 : CollatzResearch.WordTrace tailWord_158867 prefixEnd_158867 48340818452109727900379 := by
  unfold tailWord_158867
  simp only [CollatzResearch.WordTrace]
  refine ⟨5794355515459466168594855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3862903676972977445729903 5794355515459466168594855)
  ·
    refine ⟨8691533273189199252892283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5794355515459466168594855 8691533273189199252892283)
    ·
      refine ⟨13037299909783798879338425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8691533273189199252892283 13037299909783798879338425)
      ·
        refine ⟨9777974932337849159503819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13037299909783798879338425 9777974932337849159503819)
        ·
          refine ⟨14666962398506773739255729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9777974932337849159503819 14666962398506773739255729)
          ·
            refine ⟨11000221798880080304441797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14666962398506773739255729 11000221798880080304441797)
            ·
              refine ⟨2062541587290015057082837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11000221798880080304441797 2062541587290015057082837)
              ·
                refine ⟨48340818452109727900379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2062541587290015057082837 48340818452109727900379)
                ·
                  rfl

theorem cell19_158867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 7].length) (baseStart_158867 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_158867 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_158867 prefixEnd_158867 := by exact prefixLift 158867
  have htrace : WordTrace (prefixWord ++ tailWord_158867) baseStart_158867 baseEnd_158867 := by
    simpa [prefixWord, tailWord_158867, baseEnd_158867] using wordTrace_append hprefix tailTrace_158867
  have hstable : (prefixWord ++ tailWord_158867).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158867).length < 2 ^ (prefixWord ++ tailWord_158867).sum := by decide
  have hdescent : baseEnd_158867 < baseStart_158867 := by decide
  rcases family_descends (prefixWord ++ tailWord_158867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158882 : List Nat := [3, 3, 1, 3, 2, 1, 6]
def baseStart_158882 : Nat := 118140960795 + 158882 * 2 ^ 59
def prefixEnd_158882 : Nat := 4983230072969 + 3 ^ 40 * 158882 * 2
def baseEnd_158882 : Nat := 16115127574864712522335

theorem tailTrace_158882 : CollatzResearch.WordTrace tailWord_158882 prefixEnd_158882 16115127574864712522335 := by
  unfold tailWord_158882
  simp only [CollatzResearch.WordTrace]
  refine ⟨1448725652601280932597725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3863268406936749153593933 1448725652601280932597725)
  ·
    refine ⟨543272119725480349724147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1448725652601280932597725 543272119725480349724147)
    ·
      refine ⟨814908179588220524586221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 543272119725480349724147 814908179588220524586221)
      ·
        refine ⟨305590567345582696719833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 814908179588220524586221 305590567345582696719833)
        ·
          refine ⟨229192925509187022539875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305590567345582696719833 229192925509187022539875)
          ·
            refine ⟨343789388263780533809813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229192925509187022539875 343789388263780533809813)
            ·
              refine ⟨16115127574864712522335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 343789388263780533809813 16115127574864712522335)
              ·
                rfl

theorem cell19_158882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 6].length) (baseStart_158882 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_158882 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_158882 prefixEnd_158882 := by exact prefixLift 158882
  have htrace : WordTrace (prefixWord ++ tailWord_158882) baseStart_158882 baseEnd_158882 := by
    simpa [prefixWord, tailWord_158882, baseEnd_158882] using wordTrace_append hprefix tailTrace_158882
  have hstable : (prefixWord ++ tailWord_158882).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158882).length < 2 ^ (prefixWord ++ tailWord_158882).sum := by decide
  have hdescent : baseEnd_158882 < baseStart_158882 := by decide
  rcases family_descends (prefixWord ++ tailWord_158882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158884 : List Nat := [2, 3, 1, 2, 3, 2, 6]
def baseStart_158884 : Nat := 118140960795 + 158884 * 2 ^ 59
def prefixEnd_158884 : Nat := 4983230072969 + 3 ^ 40 * 158884 * 2
def baseEnd_158884 : Nat := 16115330431419575174185

theorem tailTrace_158884 : CollatzResearch.WordTrace tailWord_158884 prefixEnd_158884 16115330431419575174185 := by
  unfold tailWord_158884
  simp only [CollatzResearch.WordTrace]
  refine ⟨2897487778198939035981853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3863317037598585381309137 2897487778198939035981853)
  ·
    refine ⟨1086557916824602138493195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2897487778198939035981853 1086557916824602138493195)
    ·
      refine ⟨1629836875236903207739793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1086557916824602138493195 1629836875236903207739793)
      ·
        refine ⟨1222377656427677405804845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1629836875236903207739793 1222377656427677405804845)
        ·
          refine ⟨458391621160379027176817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1222377656427677405804845 458391621160379027176817)
          ·
            refine ⟨343793715870284270382613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 458391621160379027176817 343793715870284270382613)
            ·
              refine ⟨16115330431419575174185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 343793715870284270382613 16115330431419575174185)
              ·
                rfl

theorem cell19_158884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 6].length) (baseStart_158884 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_158884 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_158884 prefixEnd_158884 := by exact prefixLift 158884
  have htrace : WordTrace (prefixWord ++ tailWord_158884) baseStart_158884 baseEnd_158884 := by
    simpa [prefixWord, tailWord_158884, baseEnd_158884] using wordTrace_append hprefix tailTrace_158884
  have hstable : (prefixWord ++ tailWord_158884).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158884).length < 2 ^ (prefixWord ++ tailWord_158884).sum := by decide
  have hdescent : baseEnd_158884 < baseStart_158884 := by decide
  rcases family_descends (prefixWord ++ tailWord_158884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158914 : List Nat := [3, 5, 1, 1, 2, 2, 2, 3]
def baseStart_158914 : Nat := 118140960795 + 158914 * 2 ^ 59
def prefixEnd_158914 : Nat := 4983230072969 + 3 ^ 40 * 158914 * 2
def baseEnd_158914 : Nat := 48355119839227544855807

theorem tailTrace_158914 : CollatzResearch.WordTrace tailWord_158914 prefixEnd_158914 48355119839227544855807 := by
  unfold tailWord_158914
  simp only [CollatzResearch.WordTrace]
  refine ⟨1449017436572298298888949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3864046497526128797037197 1449017436572298298888949)
  ·
    refine ⟨135845384678652965520839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1449017436572298298888949 135845384678652965520839)
    ·
      refine ⟨203768077017979448281259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135845384678652965520839 203768077017979448281259)
      ·
        refine ⟨305652115526969172421889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203768077017979448281259 305652115526969172421889)
        ·
          refine ⟨229239086645226879316417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305652115526969172421889 229239086645226879316417)
          ·
            refine ⟨171929314983920159487313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 229239086645226879316417 171929314983920159487313)
            ·
              refine ⟨128946986237940119615485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171929314983920159487313 128946986237940119615485)
              ·
                refine ⟨48355119839227544855807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128946986237940119615485 48355119839227544855807)
                ·
                  rfl

theorem cell19_158914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 3].length) (baseStart_158914 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_158914 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_158914 prefixEnd_158914 := by exact prefixLift 158914
  have htrace : WordTrace (prefixWord ++ tailWord_158914) baseStart_158914 baseEnd_158914 := by
    simpa [prefixWord, tailWord_158914, baseEnd_158914] using wordTrace_append hprefix tailTrace_158914
  have hstable : (prefixWord ++ tailWord_158914).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158914).length < 2 ^ (prefixWord ++ tailWord_158914).sum := by decide
  have hdescent : baseEnd_158914 < baseStart_158914 := by decide
  rcases family_descends (prefixWord ++ tailWord_158914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158916 : List Nat := [2, 3, 3, 1, 4, 1, 2, 3]
def baseStart_158916 : Nat := 118140960795 + 158916 * 2 ^ 59
def prefixEnd_158916 : Nat := 4983230072969 + 3 ^ 40 * 158916 * 2
def baseEnd_158916 : Nat := 48355728408892132811357

theorem tailTrace_158916 : CollatzResearch.WordTrace tailWord_158916 prefixEnd_158916 48355728408892132811357 := by
  unfold tailWord_158916
  simp only [CollatzResearch.WordTrace]
  refine ⟨2898071346140973768564301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3864095128187965024752401 2898071346140973768564301)
  ·
    refine ⟨1086776754802865163211613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2898071346140973768564301 1086776754802865163211613)
    ·
      refine ⟨407541283051074436204355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1086776754802865163211613 407541283051074436204355)
      ·
        refine ⟨611311924576611654306533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 407541283051074436204355 611311924576611654306533)
        ·
          refine ⟨114620985858114685182475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 611311924576611654306533 114620985858114685182475)
          ·
            refine ⟨171931478787172027773713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114620985858114685182475 171931478787172027773713)
            ·
              refine ⟨128948609090379020830285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171931478787172027773713 128948609090379020830285)
              ·
                refine ⟨48355728408892132811357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128948609090379020830285 48355728408892132811357)
                ·
                  rfl

theorem cell19_158916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 3].length) (baseStart_158916 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_158916 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_158916 prefixEnd_158916 := by exact prefixLift 158916
  have htrace : WordTrace (prefixWord ++ tailWord_158916) baseStart_158916 baseEnd_158916 := by
    simpa [prefixWord, tailWord_158916, baseEnd_158916] using wordTrace_append hprefix tailTrace_158916
  have hstable : (prefixWord ++ tailWord_158916).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158916).length < 2 ^ (prefixWord ++ tailWord_158916).sum := by decide
  have hdescent : baseEnd_158916 < baseStart_158916 := by decide
  rcases family_descends (prefixWord ++ tailWord_158916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158922 : List Nat := [3, 1, 2, 1, 3, 3, 1, 5]
def baseStart_158922 : Nat := 118140960795 + 158922 * 2 ^ 59
def prefixEnd_158922 : Nat := 4983230072969 + 3 ^ 40 * 158922 * 2
def baseEnd_158922 : Nat := 48357554117885896678007

theorem tailTrace_158922 : CollatzResearch.WordTrace tailWord_158922 prefixEnd_158922 48357554117885896678007 := by
  unfold tailWord_158922
  simp only [CollatzResearch.WordTrace]
  refine ⟨1449090382565052640461755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3864241020173473707898013 1449090382565052640461755)
  ·
    refine ⟨2173635573847578960692633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1449090382565052640461755 2173635573847578960692633)
    ·
      refine ⟨1630226680385684220519475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2173635573847578960692633 1630226680385684220519475)
      ·
        refine ⟨2445340020578526330779213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1630226680385684220519475 2445340020578526330779213)
        ·
          refine ⟨917002507716947374042205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2445340020578526330779213 917002507716947374042205)
          ·
            refine ⟨343875940393855265265827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 917002507716947374042205 343875940393855265265827)
            ·
              refine ⟨515813910590782897898741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343875940393855265265827 515813910590782897898741)
              ·
                refine ⟨48357554117885896678007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 515813910590782897898741 48357554117885896678007)
                ·
                  rfl

theorem cell19_158922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_158922 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_158922 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_158922 prefixEnd_158922 := by exact prefixLift 158922
  have htrace : WordTrace (prefixWord ++ tailWord_158922) baseStart_158922 baseEnd_158922 := by
    simpa [prefixWord, tailWord_158922, baseEnd_158922] using wordTrace_append hprefix tailTrace_158922
  have hstable : (prefixWord ++ tailWord_158922).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158922).length < 2 ^ (prefixWord ++ tailWord_158922).sum := by decide
  have hdescent : baseEnd_158922 < baseStart_158922 := by decide
  rcases family_descends (prefixWord ++ tailWord_158922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158943 : List Nat := [1, 1, 2, 3, 2, 1, 9]
def baseStart_158943 : Nat := 118140960795 + 158943 * 2 ^ 59
def prefixEnd_158943 : Nat := 4983230072969 + 3 ^ 40 * 158943 * 2
def baseEnd_158943 : Nat := 16121314699788023403761

theorem tailTrace_158943 : CollatzResearch.WordTrace tailWord_158943 prefixEnd_158943 16121314699788023403761 := by
  unfold tailWord_158943
  simp only [CollatzResearch.WordTrace]
  refine ⟨5797127463184131148361483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3864751642122754098907655 5797127463184131148361483)
  ·
    refine ⟨8695691194776196722542225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5797127463184131148361483 8695691194776196722542225)
    ·
      refine ⟨6521768396082147541906669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8695691194776196722542225 6521768396082147541906669)
      ·
        refine ⟨2445663148530805328215001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6521768396082147541906669 2445663148530805328215001)
        ·
          refine ⟨1834247361398103996161251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2445663148530805328215001 1834247361398103996161251)
          ·
            refine ⟨2751371042097155994241877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1834247361398103996161251 2751371042097155994241877)
            ·
              refine ⟨16121314699788023403761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2751371042097155994241877 16121314699788023403761)
              ·
                rfl

theorem cell19_158943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 9].length) (baseStart_158943 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_158943 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_158943 prefixEnd_158943 := by exact prefixLift 158943
  have htrace : WordTrace (prefixWord ++ tailWord_158943) baseStart_158943 baseEnd_158943 := by
    simpa [prefixWord, tailWord_158943, baseEnd_158943] using wordTrace_append hprefix tailTrace_158943
  have hstable : (prefixWord ++ tailWord_158943).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158943).length < 2 ^ (prefixWord ++ tailWord_158943).sum := by decide
  have hdescent : baseEnd_158943 < baseStart_158943 := by decide
  rcases family_descends (prefixWord ++ tailWord_158943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158981 : List Nat := [1, 3, 1, 1, 2, 1, 3, 7]
def baseStart_158981 : Nat := 118140960795 + 158981 * 2 ^ 59
def prefixEnd_158981 : Nat := 4983230072969 + 3 ^ 40 * 158981 * 2
def baseEnd_158981 : Nat := 48375506922991241366735

theorem tailTrace_158981 : CollatzResearch.WordTrace tailWord_158981 prefixEnd_158981 48375506922991241366735 := by
  unfold tailWord_158981
  simp only [CollatzResearch.WordTrace]
  refine ⟨5798513437046463638244797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3865675624697642425496531 5798513437046463638244797)
  ·
    refine ⟨2174442538892423864341799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5798513437046463638244797 2174442538892423864341799)
    ·
      refine ⟨3261663808338635796512699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2174442538892423864341799 3261663808338635796512699)
      ·
        refine ⟨4892495712507953694769049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3261663808338635796512699 4892495712507953694769049)
        ·
          refine ⟨3669371784380965271076787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4892495712507953694769049 3669371784380965271076787)
          ·
            refine ⟨5504057676571447906615181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3669371784380965271076787 5504057676571447906615181)
            ·
              refine ⟨2064021628714292964980693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5504057676571447906615181 2064021628714292964980693)
              ·
                refine ⟨48375506922991241366735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2064021628714292964980693 48375506922991241366735)
                ·
                  rfl

theorem cell19_158981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 7].length) (baseStart_158981 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_158981 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_158981 prefixEnd_158981 := by exact prefixLift 158981
  have htrace : WordTrace (prefixWord ++ tailWord_158981) baseStart_158981 baseEnd_158981 := by
    simpa [prefixWord, tailWord_158981, baseEnd_158981] using wordTrace_append hprefix tailTrace_158981
  have hstable : (prefixWord ++ tailWord_158981).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158981).length < 2 ^ (prefixWord ++ tailWord_158981).sum := by decide
  have hdescent : baseEnd_158981 < baseStart_158981 := by decide
  rcases family_descends (prefixWord ++ tailWord_158981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158994 : List Nat := [3, 2, 4, 2, 2, 6]
def baseStart_158994 : Nat := 118140960795 + 158994 * 2 ^ 59
def prefixEnd_158994 : Nat := 4983230072969 + 3 ^ 40 * 158994 * 2
def baseEnd_158994 : Nat := 5375495847312340341979

theorem tailTrace_158994 : CollatzResearch.WordTrace tailWord_158994 prefixEnd_158994 5375495847312340341979 := by
  unfold tailWord_158994
  simp only [CollatzResearch.WordTrace]
  refine ⟨1449746896499841714617009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3865991723999577905645357 1449746896499841714617009)
  ·
    refine ⟨1087310172374881285962757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1449746896499841714617009 1087310172374881285962757)
    ·
      refine ⟨203870657320290241118017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1087310172374881285962757 203870657320290241118017)
      ·
        refine ⟨152902992990217680838513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203870657320290241118017 152902992990217680838513)
        ·
          refine ⟨114677244742663260628885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152902992990217680838513 114677244742663260628885)
          ·
            refine ⟨5375495847312340341979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 114677244742663260628885 5375495847312340341979)
            ·
              rfl

theorem cell19_158994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 6].length) (baseStart_158994 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_158994 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_158994 prefixEnd_158994 := by exact prefixLift 158994
  have htrace : WordTrace (prefixWord ++ tailWord_158994) baseStart_158994 baseEnd_158994 := by
    simpa [prefixWord, tailWord_158994, baseEnd_158994] using wordTrace_append hprefix tailTrace_158994
  have hstable : (prefixWord ++ tailWord_158994).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158994).length < 2 ^ (prefixWord ++ tailWord_158994).sum := by decide
  have hdescent : baseEnd_158994 < baseStart_158994 := by decide
  rcases family_descends (prefixWord ++ tailWord_158994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159000 : List Nat := [2, 1, 2, 3, 1, 10]
def baseStart_159000 : Nat := 118140960795 + 159000 * 2 ^ 59
def prefixEnd_159000 : Nat := 4983230072969 + 3 ^ 40 * 159000 * 2
def baseEnd_159000 : Nat := 5375698703867202993829

theorem tailTrace_159000 : CollatzResearch.WordTrace tailWord_159000 prefixEnd_159000 5375698703867202993829 := by
  unfold tailWord_159000
  simp only [CollatzResearch.WordTrace]
  refine ⟨2899603211988814941593227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3866137615985086588790969 2899603211988814941593227)
  ·
    refine ⟨4349404817983222412389841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2899603211988814941593227 4349404817983222412389841)
    ·
      refine ⟨3262053613487416809292381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4349404817983222412389841 3262053613487416809292381)
      ·
        refine ⟨1223270105057781303484643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3262053613487416809292381 1223270105057781303484643)
        ·
          refine ⟨1834905157586671955226965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1223270105057781303484643 1834905157586671955226965)
          ·
            refine ⟨5375698703867202993829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1834905157586671955226965 5375698703867202993829)
            ·
              rfl

theorem cell19_159000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 10].length) (baseStart_159000 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_159000 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_159000 prefixEnd_159000 := by exact prefixLift 159000
  have htrace : WordTrace (prefixWord ++ tailWord_159000) baseStart_159000 baseEnd_159000 := by
    simpa [prefixWord, tailWord_159000, baseEnd_159000] using wordTrace_append hprefix tailTrace_159000
  have hstable : (prefixWord ++ tailWord_159000).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159000).length < 2 ^ (prefixWord ++ tailWord_159000).sum := by decide
  have hdescent : baseEnd_159000 < baseStart_159000 := by decide
  rcases family_descends (prefixWord ++ tailWord_159000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159030 : List Nat := [5, 1, 2, 3, 1, 1, 3, 3]
def baseStart_159030 : Nat := 118140960795 + 159030 * 2 ^ 59
def prefixEnd_159030 : Nat := 4983230072969 + 3 ^ 40 * 159030 * 2
def baseEnd_159030 : Nat := 48390416879773646277713

theorem tailTrace_159030 : CollatzResearch.WordTrace tailWord_159030 prefixEnd_159030 48390416879773646277713 := by
  unfold tailWord_159030
  simp only [CollatzResearch.WordTrace]
  refine ⟨362518788366809062923659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3866867075912630004519029 362518788366809062923659)
  ·
    refine ⟨543778182550213594385489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 362518788366809062923659 543778182550213594385489)
    ·
      refine ⟨407833636912660195789117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 543778182550213594385489 407833636912660195789117)
      ·
        refine ⟨152937613842247573420919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 407833636912660195789117 152937613842247573420919)
        ·
          refine ⟨229406420763371360131379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152937613842247573420919 229406420763371360131379)
          ·
            refine ⟨344109631145057040197069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229406420763371360131379 344109631145057040197069)
            ·
              refine ⟨129041111679396390073901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 344109631145057040197069 129041111679396390073901)
              ·
                refine ⟨48390416879773646277713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129041111679396390073901 48390416879773646277713)
                ·
                  rfl

theorem cell19_159030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_159030 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_159030 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_159030 prefixEnd_159030 := by exact prefixLift 159030
  have htrace : WordTrace (prefixWord ++ tailWord_159030) baseStart_159030 baseEnd_159030 := by
    simpa [prefixWord, tailWord_159030, baseEnd_159030] using wordTrace_append hprefix tailTrace_159030
  have hstable : (prefixWord ++ tailWord_159030).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159030).length < 2 ^ (prefixWord ++ tailWord_159030).sum := by decide
  have hdescent : baseEnd_159030 < baseStart_159030 := by decide
  rcases family_descends (prefixWord ++ tailWord_159030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159057 : List Nat := [1, 2, 2, 1, 4, 1, 8]
def baseStart_159057 : Nat := 118140960795 + 159057 * 2 ^ 59
def prefixEnd_159057 : Nat := 4983230072969 + 3 ^ 40 * 159057 * 2
def baseEnd_159057 : Nat := 16132877523415194559213

theorem tailTrace_159057 : CollatzResearch.WordTrace tailWord_159057 prefixEnd_159057 16132877523415194559213 := by
  unfold tailWord_159057
  simp only [CollatzResearch.WordTrace]
  refine ⟨5801285384771128618011425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3867523589847419078674283 5801285384771128618011425)
  ·
    refine ⟨4350964038578346463508569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5801285384771128618011425 4350964038578346463508569)
    ·
      refine ⟨3263223028933759847631427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4350964038578346463508569 3263223028933759847631427)
      ·
        refine ⟨4894834543400639771447141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3263223028933759847631427 4894834543400639771447141)
        ·
          refine ⟨917781476887619957146339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4894834543400639771447141 917781476887619957146339)
          ·
            refine ⟨1376672215331429935719509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 917781476887619957146339 1376672215331429935719509)
            ·
              refine ⟨16132877523415194559213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1376672215331429935719509 16132877523415194559213)
              ·
                rfl

theorem cell19_159057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 8].length) (baseStart_159057 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_159057 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_159057 prefixEnd_159057 := by exact prefixLift 159057
  have htrace : WordTrace (prefixWord ++ tailWord_159057) baseStart_159057 baseEnd_159057 := by
    simpa [prefixWord, tailWord_159057, baseEnd_159057] using wordTrace_append hprefix tailTrace_159057
  have hstable : (prefixWord ++ tailWord_159057).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159057).length < 2 ^ (prefixWord ++ tailWord_159057).sum := by decide
  have hdescent : baseEnd_159057 < baseStart_159057 := by decide
  rcases family_descends (prefixWord ++ tailWord_159057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159074 : List Nat := [3, 3, 2, 1, 1, 1, 2, 6]
def baseStart_159074 : Nat := 118140960795 + 159074 * 2 ^ 59
def prefixEnd_159074 : Nat := 4983230072969 + 3 ^ 40 * 159074 * 2
def baseEnd_159074 : Nat := 48403805412394581299815

theorem tailTrace_159074 : CollatzResearch.WordTrace tailWord_159074 prefixEnd_159074 48403805412394581299815 := by
  unfold tailWord_159074
  simp only [CollatzResearch.WordTrace]
  refine ⟨1450476356427385130345069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3867936950473027014253517 1450476356427385130345069)
  ·
    refine ⟨543928633660269423879401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1450476356427385130345069 543928633660269423879401)
    ·
      refine ⟨407946475245202067909551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 543928633660269423879401 407946475245202067909551)
      ·
        refine ⟨611919712867803101864327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 407946475245202067909551 611919712867803101864327)
        ·
          refine ⟨917879569301704652796491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 611919712867803101864327 917879569301704652796491)
          ·
            refine ⟨1376819353952556979194737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 917879569301704652796491 1376819353952556979194737)
            ·
              refine ⟨1032614515464417734396053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1376819353952556979194737 1032614515464417734396053)
              ·
                refine ⟨48403805412394581299815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1032614515464417734396053 48403805412394581299815)
                ·
                  rfl

theorem cell19_159074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_159074 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_159074 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_159074 prefixEnd_159074 := by exact prefixLift 159074
  have htrace : WordTrace (prefixWord ++ tailWord_159074) baseStart_159074 baseEnd_159074 := by
    simpa [prefixWord, tailWord_159074, baseEnd_159074] using wordTrace_append hprefix tailTrace_159074
  have hstable : (prefixWord ++ tailWord_159074).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159074).length < 2 ^ (prefixWord ++ tailWord_159074).sum := by decide
  have hdescent : baseEnd_159074 < baseStart_159074 := by decide
  rcases family_descends (prefixWord ++ tailWord_159074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159095 : List Nat := [1, 1, 3, 1, 1, 2, 5, 5]
def baseStart_159095 : Nat := 118140960795 + 159095 * 2 ^ 59
def prefixEnd_159095 : Nat := 4983230072969 + 3 ^ 40 * 159095 * 2
def baseEnd_159095 : Nat := 48410195393872754833091

theorem tailTrace_159095 : CollatzResearch.WordTrace tailWord_159095 prefixEnd_159095 48410195393872754833091 := by
  unfold tailWord_159095
  simp only [CollatzResearch.WordTrace]
  refine ⟨5802671358633461107894739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3868447572422307405263159 5802671358633461107894739)
  ·
    refine ⟨8704007037950191661842109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5802671358633461107894739 8704007037950191661842109)
    ·
      refine ⟨3264002639231321873190791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8704007037950191661842109 3264002639231321873190791)
      ·
        refine ⟨4896003958846982809786187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3264002639231321873190791 4896003958846982809786187)
        ·
          refine ⟨7344005938270474214679281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4896003958846982809786187 7344005938270474214679281)
          ·
            refine ⟨5508004453702855661009461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7344005938270474214679281 5508004453702855661009461)
            ·
              refine ⟨516375417534642718219637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5508004453702855661009461 516375417534642718219637)
              ·
                refine ⟨48410195393872754833091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 516375417534642718219637 48410195393872754833091)
                ·
                  rfl

theorem cell19_159095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 5].length) (baseStart_159095 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_159095 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_159095 prefixEnd_159095 := by exact prefixLift 159095
  have htrace : WordTrace (prefixWord ++ tailWord_159095) baseStart_159095 baseEnd_159095 := by
    simpa [prefixWord, tailWord_159095, baseEnd_159095] using wordTrace_append hprefix tailTrace_159095
  have hstable : (prefixWord ++ tailWord_159095).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159095).length < 2 ^ (prefixWord ++ tailWord_159095).sum := by decide
  have hdescent : baseEnd_159095 < baseStart_159095 := by decide
  rcases family_descends (prefixWord ++ tailWord_159095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159112 : List Nat := [2, 1, 3, 3, 1, 4, 5]
def baseStart_159112 : Nat := 118140960795 + 159112 * 2 ^ 59
def prefixEnd_159112 : Nat := 4983230072969 + 3 ^ 40 * 159112 * 2
def baseEnd_159112 : Nat := 16138456078673917485089

theorem tailTrace_159112 : CollatzResearch.WordTrace tailWord_159112 prefixEnd_159112 16138456078673917485089 := by
  unfold tailWord_159112
  simp only [CollatzResearch.WordTrace]
  refine ⟨2901645699785936505631795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3868860933047915340842393 2901645699785936505631795)
  ·
    refine ⟨4352468549678904758447693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2901645699785936505631795 4352468549678904758447693)
    ·
      refine ⟨1632175706129589284417885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4352468549678904758447693 1632175706129589284417885)
      ·
        refine ⟨612065889798595981656707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1632175706129589284417885 612065889798595981656707)
        ·
          refine ⟨918098834697893972485061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 612065889798595981656707 918098834697893972485061)
          ·
            refine ⟨172143531505855119840949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 918098834697893972485061 172143531505855119840949)
            ·
              refine ⟨16138456078673917485089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 172143531505855119840949 16138456078673917485089)
              ·
                rfl

theorem cell19_159112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 5].length) (baseStart_159112 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_159112 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_159112 prefixEnd_159112 := by exact prefixLift 159112
  have htrace : WordTrace (prefixWord ++ tailWord_159112) baseStart_159112 baseEnd_159112 := by
    simpa [prefixWord, tailWord_159112, baseEnd_159112] using wordTrace_append hprefix tailTrace_159112
  have hstable : (prefixWord ++ tailWord_159112).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159112).length < 2 ^ (prefixWord ++ tailWord_159112).sum := by decide
  have hdescent : baseEnd_159112 < baseStart_159112 := by decide
  rcases family_descends (prefixWord ++ tailWord_159112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159169 : List Nat := [1, 2, 7, 9]
def baseStart_159169 : Nat := 118140960795 + 159169 * 2 ^ 59
def prefixEnd_159169 : Nat := 4983230072969 + 3 ^ 40 * 159169 * 2
def baseEnd_159169 : Nat := 597934721869907520845

theorem tailTrace_159169 : CollatzResearch.WordTrace tailWord_159169 prefixEnd_159169 597934721869907520845 := by
  unfold tailWord_159169
  simp only [CollatzResearch.WordTrace]
  refine ⟨5805370360365371746088561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3870246906910247830725707 5805370360365371746088561)
  ·
    refine ⟨4354027770274028809566421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5805370360365371746088561 4354027770274028809566421)
    ·
      refine ⟨102047525865797550224213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 4354027770274028809566421 102047525865797550224213)
      ·
        refine ⟨597934721869907520845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 9 102047525865797550224213 597934721869907520845)
        ·
          rfl

theorem cell19_159169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 9].length) (baseStart_159169 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_159169 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_159169 prefixEnd_159169 := by exact prefixLift 159169
  have htrace : WordTrace (prefixWord ++ tailWord_159169) baseStart_159169 baseEnd_159169 := by
    simpa [prefixWord, tailWord_159169, baseEnd_159169] using wordTrace_append hprefix tailTrace_159169
  have hstable : (prefixWord ++ tailWord_159169).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159169).length < 2 ^ (prefixWord ++ tailWord_159169).sum := by decide
  have hdescent : baseEnd_159169 < baseStart_159169 := by decide
  rcases family_descends (prefixWord ++ tailWord_159169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159205 : List Nat := [1, 3, 1, 5, 1, 2, 3, 3]
def baseStart_159205 : Nat := 118140960795 + 159205 * 2 ^ 59
def prefixEnd_159205 : Nat := 4983230072969 + 3 ^ 40 * 159205 * 2
def baseEnd_159205 : Nat := 48443666725425092388347

theorem tailTrace_159205 : CollatzResearch.WordTrace tailWord_159205 prefixEnd_159205 48443666725425092388347 := by
  unfold tailWord_159205
  simp only [CollatzResearch.WordTrace]
  refine ⟨5806683388234949894399069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3871122258823299929599379 5806683388234949894399069)
  ·
    refine ⟨2177506270588106210399651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5806683388234949894399069 2177506270588106210399651)
    ·
      refine ⟨3266259405882159315599477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2177506270588106210399651 3266259405882159315599477)
      ·
        refine ⟨306211819301452435837451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3266259405882159315599477 306211819301452435837451)
        ·
          refine ⟨459317728952178653756177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306211819301452435837451 459317728952178653756177)
          ·
            refine ⟨344488296714133990317133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 459317728952178653756177 344488296714133990317133)
            ·
              refine ⟨129183111267800246368925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 344488296714133990317133 129183111267800246368925)
              ·
                refine ⟨48443666725425092388347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129183111267800246368925 48443666725425092388347)
                ·
                  rfl

theorem cell19_159205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 3].length) (baseStart_159205 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_159205 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_159205 prefixEnd_159205 := by exact prefixLift 159205
  have htrace : WordTrace (prefixWord ++ tailWord_159205) baseStart_159205 baseEnd_159205 := by
    simpa [prefixWord, tailWord_159205, baseEnd_159205] using wordTrace_append hprefix tailTrace_159205
  have hstable : (prefixWord ++ tailWord_159205).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159205).length < 2 ^ (prefixWord ++ tailWord_159205).sum := by decide
  have hdescent : baseEnd_159205 < baseStart_159205 := by decide
  rcases family_descends (prefixWord ++ tailWord_159205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159264 : List Nat := [2, 1, 1, 6, 1, 2, 1, 5]
def baseStart_159264 : Nat := 118140960795 + 159264 * 2 ^ 59
def prefixEnd_159264 : Nat := 4983230072969 + 3 ^ 40 * 159264 * 2
def baseEnd_159264 : Nat := 48461619530530437077075

theorem tailTrace_159264 : CollatzResearch.WordTrace tailWord_159264 prefixEnd_159264 48461619530530437077075 := by
  unfold tailWord_159264
  simp only [CollatzResearch.WordTrace]
  refine ⟨2904417647510601485398423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3872556863347468647197897 2904417647510601485398423)
  ·
    refine ⟨4356626471265902228097635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2904417647510601485398423 4356626471265902228097635)
    ·
      refine ⟨6534939706898853342146453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4356626471265902228097635 6534939706898853342146453)
      ·
        refine ⟨306325298760883750413115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6534939706898853342146453 306325298760883750413115)
        ·
          refine ⟨459487948141325625619673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306325298760883750413115 459487948141325625619673)
          ·
            refine ⟨344615961105994219214755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 459487948141325625619673 344615961105994219214755)
            ·
              refine ⟨516923941658991328822133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 344615961105994219214755 516923941658991328822133)
              ·
                refine ⟨48461619530530437077075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 516923941658991328822133 48461619530530437077075)
                ·
                  rfl

theorem cell19_159264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 5].length) (baseStart_159264 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_159264 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_159264 prefixEnd_159264 := by exact prefixLift 159264
  have htrace : WordTrace (prefixWord ++ tailWord_159264) baseStart_159264 baseEnd_159264 := by
    simpa [prefixWord, tailWord_159264, baseEnd_159264] using wordTrace_append hprefix tailTrace_159264
  have hstable : (prefixWord ++ tailWord_159264).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159264).length < 2 ^ (prefixWord ++ tailWord_159264).sum := by decide
  have hdescent : baseEnd_159264 < baseStart_159264 := by decide
  rcases family_descends (prefixWord ++ tailWord_159264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159285 : List Nat := [1, 3, 3, 1, 1, 3, 7]
def baseStart_159285 : Nat := 118140960795 + 159285 * 2 ^ 59
def prefixEnd_159285 : Nat := 4983230072969 + 3 ^ 40 * 159285 * 2
def baseEnd_159285 : Nat := 16156003170669536870117

theorem tailTrace_159285 : CollatzResearch.WordTrace tailWord_159285 prefixEnd_159285 16156003170669536870117 := by
  unfold tailWord_159285
  simp only [CollatzResearch.WordTrace]
  refine ⟨5809601227945123557311309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3873067485296749038207539 5809601227945123557311309)
  ·
    refine ⟨2178600460479421333991741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5809601227945123557311309 2178600460479421333991741)
    ·
      refine ⟨816975172679783000246903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2178600460479421333991741 816975172679783000246903)
      ·
        refine ⟨1225462759019674500370355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 816975172679783000246903 1225462759019674500370355)
        ·
          refine ⟨1838194138529511750555533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1225462759019674500370355 1838194138529511750555533)
          ·
            refine ⟨689322801948566906458325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1838194138529511750555533 689322801948566906458325)
            ·
              refine ⟨16156003170669536870117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 689322801948566906458325 16156003170669536870117)
              ·
                rfl

theorem cell19_159285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 7].length) (baseStart_159285 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_159285 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_159285 prefixEnd_159285 := by exact prefixLift 159285
  have htrace : WordTrace (prefixWord ++ tailWord_159285) baseStart_159285 baseEnd_159285 := by
    simpa [prefixWord, tailWord_159285, baseEnd_159285] using wordTrace_append hprefix tailTrace_159285
  have hstable : (prefixWord ++ tailWord_159285).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159285).length < 2 ^ (prefixWord ++ tailWord_159285).sum := by decide
  have hdescent : baseEnd_159285 < baseStart_159285 := by decide
  rcases family_descends (prefixWord ++ tailWord_159285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159342 : List Nat := [4, 1, 2, 2, 10]
def baseStart_159342 : Nat := 118140960795 + 159342 * 2 ^ 59
def prefixEnd_159342 : Nat := 4983230072969 + 3 ^ 40 * 159342 * 2
def baseEnd_159342 : Nat := 1795753842498124716427

theorem tailTrace_159342 : CollatzResearch.WordTrace tailWord_159342 prefixEnd_159342 1795753842498124716427 := by
  unfold tailWord_159342
  simp only [CollatzResearch.WordTrace]
  refine ⟨726460023592327786517035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3874453459159081528090853 726460023592327786517035)
  ·
    refine ⟨1089690035388491679775553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 726460023592327786517035 1089690035388491679775553)
    ·
      refine ⟨817267526541368759831665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1089690035388491679775553 817267526541368759831665)
      ·
        refine ⟨612950644906026569873749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 817267526541368759831665 612950644906026569873749)
        ·
          refine ⟨1795753842498124716427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 612950644906026569873749 1795753842498124716427)
          ·
            rfl

theorem cell19_159342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 10].length) (baseStart_159342 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_159342 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_159342 prefixEnd_159342 := by exact prefixLift 159342
  have htrace : WordTrace (prefixWord ++ tailWord_159342) baseStart_159342 baseEnd_159342 := by
    simpa [prefixWord, tailWord_159342, baseEnd_159342] using wordTrace_append hprefix tailTrace_159342
  have hstable : (prefixWord ++ tailWord_159342).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159342).length < 2 ^ (prefixWord ++ tailWord_159342).sum := by decide
  have hdescent : baseEnd_159342 < baseStart_159342 := by decide
  rcases family_descends (prefixWord ++ tailWord_159342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159452 : List Nat := [2, 2, 5, 1, 2, 2, 5]
def baseStart_159452 : Nat := 118140960795 + 159452 * 2 ^ 59
def prefixEnd_159452 : Nat := 4983230072969 + 3 ^ 40 * 159452 * 2
def baseEnd_159452 : Nat := 16172941693000568299595

theorem tailTrace_159452 : CollatzResearch.WordTrace tailWord_159452 prefixEnd_159452 16172941693000568299595 := by
  unfold tailWord_159452
  simp only [CollatzResearch.WordTrace]
  refine ⟨2907846109170055539320305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3877128145560074052427073 2907846109170055539320305)
  ·
    refine ⟨2180884581877541654490229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2907846109170055539320305 2180884581877541654490229)
    ·
      refine ⟨204457929551019530108459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2180884581877541654490229 204457929551019530108459)
      ·
        refine ⟨306686894326529295162689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204457929551019530108459 306686894326529295162689)
        ·
          refine ⟨230015170744896971372017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 306686894326529295162689 230015170744896971372017)
          ·
            refine ⟨172511378058672728529013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230015170744896971372017 172511378058672728529013)
            ·
              refine ⟨16172941693000568299595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 172511378058672728529013 16172941693000568299595)
              ·
                rfl

theorem cell19_159452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 5].length) (baseStart_159452 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_159452 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_159452 prefixEnd_159452 := by exact prefixLift 159452
  have htrace : WordTrace (prefixWord ++ tailWord_159452) baseStart_159452 baseEnd_159452 := by
    simpa [prefixWord, tailWord_159452, baseEnd_159452] using wordTrace_append hprefix tailTrace_159452
  have hstable : (prefixWord ++ tailWord_159452).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159452).length < 2 ^ (prefixWord ++ tailWord_159452).sum := by decide
  have hdescent : baseEnd_159452 < baseStart_159452 := by decide
  rcases family_descends (prefixWord ++ tailWord_159452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159532 : List Nat := [2, 2, 1, 1, 1, 5, 3, 4]
def baseStart_159532 : Nat := 118140960795 + 159532 * 2 ^ 59
def prefixEnd_159532 : Nat := 4983230072969 + 3 ^ 40 * 159532 * 2
def baseEnd_159532 : Nat := 48543167865585223120789

theorem tailTrace_159532 : CollatzResearch.WordTrace tailWord_159532 prefixEnd_159532 48543167865585223120789 := by
  unfold tailWord_159532
  simp only [CollatzResearch.WordTrace]
  refine ⟨2909305029025142370776425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3879073372033523161035233 2909305029025142370776425)
  ·
    refine ⟨2181978771768856778082319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2909305029025142370776425 2181978771768856778082319)
    ·
      refine ⟨3272968157653285167123479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2181978771768856778082319 3272968157653285167123479)
      ·
        refine ⟨4909452236479927750685219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3272968157653285167123479 4909452236479927750685219)
        ·
          refine ⟨7364178354719891626027829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4909452236479927750685219 7364178354719891626027829)
          ·
            refine ⟨690391720754989839940109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7364178354719891626027829 690391720754989839940109)
            ·
              refine ⟨258896895283121189977541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 690391720754989839940109 258896895283121189977541)
              ·
                refine ⟨48543167865585223120789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 258896895283121189977541 48543167865585223120789)
                ·
                  rfl

theorem cell19_159532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 4].length) (baseStart_159532 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_159532 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_159532 prefixEnd_159532 := by exact prefixLift 159532
  have htrace : WordTrace (prefixWord ++ tailWord_159532) baseStart_159532 baseEnd_159532 := by
    simpa [prefixWord, tailWord_159532, baseEnd_159532] using wordTrace_append hprefix tailTrace_159532
  have hstable : (prefixWord ++ tailWord_159532).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159532).length < 2 ^ (prefixWord ++ tailWord_159532).sum := by decide
  have hdescent : baseEnd_159532 < baseStart_159532 := by decide
  rcases family_descends (prefixWord ++ tailWord_159532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159570 : List Nat := [3, 2, 2, 1, 1, 4, 6]
def baseStart_159570 : Nat := 118140960795 + 159570 * 2 ^ 59
def prefixEnd_159570 : Nat := 4983230072969 + 3 ^ 40 * 159570 * 2
def baseEnd_159570 : Nat := 16184910229737464758747

theorem tailTrace_159570 : CollatzResearch.WordTrace tailWord_159570 prefixEnd_159570 16184910229737464758747 := by
  unfold tailWord_159570
  simp only [CollatzResearch.WordTrace]
  refine ⟨1454999007978154307859041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3879997354608411487624109 1454999007978154307859041)
  ·
    refine ⟨1091249255983615730894281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1454999007978154307859041 1091249255983615730894281)
    ·
      refine ⟨818436941987711798170711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1091249255983615730894281 818436941987711798170711)
      ·
        refine ⟨1227655412981567697256067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 818436941987711798170711 1227655412981567697256067)
        ·
          refine ⟨1841483119472351545884101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1227655412981567697256067 1841483119472351545884101)
          ·
            refine ⟨345278084901065914853269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1841483119472351545884101 345278084901065914853269)
            ·
              refine ⟨16184910229737464758747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 345278084901065914853269 16184910229737464758747)
              ·
                rfl

theorem cell19_159570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 6].length) (baseStart_159570 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_159570 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_159570 prefixEnd_159570 := by exact prefixLift 159570
  have htrace : WordTrace (prefixWord ++ tailWord_159570) baseStart_159570 baseEnd_159570 := by
    simpa [prefixWord, tailWord_159570, baseEnd_159570] using wordTrace_append hprefix tailTrace_159570
  have hstable : (prefixWord ++ tailWord_159570).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159570).length < 2 ^ (prefixWord ++ tailWord_159570).sum := by decide
  have hdescent : baseEnd_159570 < baseStart_159570 := by decide
  rcases family_descends (prefixWord ++ tailWord_159570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159644 : List Nat := [2, 2, 3, 3, 1, 2, 2, 4]
def baseStart_159644 : Nat := 118140960795 + 159644 * 2 ^ 59
def prefixEnd_159644 : Nat := 4983230072969 + 3 ^ 40 * 159644 * 2
def baseEnd_159644 : Nat := 48577247766802148631595

theorem tailTrace_159644 : CollatzResearch.WordTrace tailWord_159644 prefixEnd_159644 48577247766802148631595 := by
  unfold tailWord_159644
  simp only [CollatzResearch.WordTrace]
  refine ⟨2911347516822263934814993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3881796689096351913086657 2911347516822263934814993)
  ·
    refine ⟨2183510637616697951111245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2911347516822263934814993 2183510637616697951111245)
    ·
      refine ⟨818816489106261731666717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2183510637616697951111245 818816489106261731666717)
      ·
        refine ⟨307056183414848149375019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 818816489106261731666717 307056183414848149375019)
        ·
          refine ⟨460584275122272224062529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307056183414848149375019 460584275122272224062529)
          ·
            refine ⟨345438206341704168046897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 460584275122272224062529 345438206341704168046897)
            ·
              refine ⟨259078654756278126035173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 345438206341704168046897 259078654756278126035173)
              ·
                refine ⟨48577247766802148631595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 259078654756278126035173 48577247766802148631595)
                ·
                  rfl

theorem cell19_159644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 4].length) (baseStart_159644 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_159644 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_159644 prefixEnd_159644 := by exact prefixLift 159644
  have htrace : WordTrace (prefixWord ++ tailWord_159644) baseStart_159644 baseEnd_159644 := by
    simpa [prefixWord, tailWord_159644, baseEnd_159644] using wordTrace_append hprefix tailTrace_159644
  have hstable : (prefixWord ++ tailWord_159644).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159644).length < 2 ^ (prefixWord ++ tailWord_159644).sum := by decide
  have hdescent : baseEnd_159644 < baseStart_159644 := by decide
  rcases family_descends (prefixWord ++ tailWord_159644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159665 : List Nat := [1, 2, 2, 4, 2, 1, 2, 5]
def baseStart_159665 : Nat := 118140960795 + 159665 * 2 ^ 59
def prefixEnd_159665 : Nat := 4983230072969 + 3 ^ 40 * 159665 * 2
def baseEnd_159665 : Nat := 48583637748280322164871

theorem tailTrace_159665 : CollatzResearch.WordTrace tailWord_159665 prefixEnd_159665 48583637748280322164871 := by
  unfold tailWord_159665
  simp only [CollatzResearch.WordTrace]
  refine ⟨5823460966568448456144449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3882307311045632304096299 5823460966568448456144449)
  ·
    refine ⟨4367595724926336342108337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5823460966568448456144449 4367595724926336342108337)
    ·
      refine ⟨3275696793694752256581253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4367595724926336342108337 3275696793694752256581253)
      ·
        refine ⟨614193148817766048108985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3275696793694752256581253 614193148817766048108985)
        ·
          refine ⟨460644861613324536081739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 614193148817766048108985 460644861613324536081739)
          ·
            refine ⟨690967292419986804122609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 460644861613324536081739 690967292419986804122609)
            ·
              refine ⟨518225469314990103091957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 690967292419986804122609 518225469314990103091957)
              ·
                refine ⟨48583637748280322164871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 518225469314990103091957 48583637748280322164871)
                ·
                  rfl

theorem cell19_159665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 5].length) (baseStart_159665 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_159665 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_159665 prefixEnd_159665 := by exact prefixLift 159665
  have htrace : WordTrace (prefixWord ++ tailWord_159665) baseStart_159665 baseEnd_159665 := by
    simpa [prefixWord, tailWord_159665, baseEnd_159665] using wordTrace_append hprefix tailTrace_159665
  have hstable : (prefixWord ++ tailWord_159665).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159665).length < 2 ^ (prefixWord ++ tailWord_159665).sum := by decide
  have hdescent : baseEnd_159665 < baseStart_159665 := by decide
  rcases family_descends (prefixWord ++ tailWord_159665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159667 : List Nat := [1, 1, 1, 2, 3, 1, 3, 7]
def baseStart_159667 : Nat := 118140960795 + 159667 * 2 ^ 59
def prefixEnd_159667 : Nat := 4983230072969 + 3 ^ 40 * 159667 * 2
def baseEnd_159667 : Nat := 48584246317944910120421

theorem tailTrace_159667 : CollatzResearch.WordTrace tailWord_159667 prefixEnd_159667 48584246317944910120421 := by
  unfold tailWord_159667
  simp only [CollatzResearch.WordTrace]
  refine ⟨5823533912561202797717255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3882355941707468531811503 5823533912561202797717255)
  ·
    refine ⟨8735300868841804196575883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5823533912561202797717255 8735300868841804196575883)
    ·
      refine ⟨13102951303262706294863825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8735300868841804196575883 13102951303262706294863825)
      ·
        refine ⟨9827213477447029721147869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13102951303262706294863825 9827213477447029721147869)
        ·
          refine ⟨3685205054042636145430451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9827213477447029721147869 3685205054042636145430451)
          ·
            refine ⟨5527807581063954218145677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3685205054042636145430451 5527807581063954218145677)
            ·
              refine ⟨2072927842898982831804629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5527807581063954218145677 2072927842898982831804629)
              ·
                refine ⟨48584246317944910120421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2072927842898982831804629 48584246317944910120421)
                ·
                  rfl

theorem cell19_159667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 7].length) (baseStart_159667 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_159667 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_159667 prefixEnd_159667 := by exact prefixLift 159667
  have htrace : WordTrace (prefixWord ++ tailWord_159667) baseStart_159667 baseEnd_159667 := by
    simpa [prefixWord, tailWord_159667, baseEnd_159667] using wordTrace_append hprefix tailTrace_159667
  have hstable : (prefixWord ++ tailWord_159667).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159667).length < 2 ^ (prefixWord ++ tailWord_159667).sum := by decide
  have hdescent : baseEnd_159667 < baseStart_159667 := by decide
  rcases family_descends (prefixWord ++ tailWord_159667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159701 : List Nat := [1, 3, 2, 3, 2, 3, 1, 4]
def baseStart_159701 : Nat := 118140960795 + 159701 * 2 ^ 59
def prefixEnd_159701 : Nat := 4983230072969 + 3 ^ 40 * 159701 * 2
def baseEnd_159701 : Nat := 48594592002242905364773

theorem tailTrace_159701 : CollatzResearch.WordTrace tailWord_159701 prefixEnd_159701 48594592002242905364773 := by
  unfold tailWord_159701
  simp only [CollatzResearch.WordTrace]
  refine ⟨5824773994438026604454957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3883182662958684402969971 5824773994438026604454957)
  ·
    refine ⟨2184290247914259976670609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5824773994438026604454957 2184290247914259976670609)
    ·
      refine ⟨1638217685935694982502957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2184290247914259976670609 1638217685935694982502957)
      ·
        refine ⟨614331632225885618438609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1638217685935694982502957 614331632225885618438609)
        ·
          refine ⟨460748724169414213828957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 614331632225885618438609 460748724169414213828957)
          ·
            refine ⟨172780771563530330185859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 460748724169414213828957 172780771563530330185859)
            ·
              refine ⟨259171157345295495278789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172780771563530330185859 259171157345295495278789)
              ·
                refine ⟨48594592002242905364773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 259171157345295495278789 48594592002242905364773)
                ·
                  rfl

theorem cell19_159701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 4].length) (baseStart_159701 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_159701 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_159701 prefixEnd_159701 := by exact prefixLift 159701
  have htrace : WordTrace (prefixWord ++ tailWord_159701) baseStart_159701 baseEnd_159701 := by
    simpa [prefixWord, tailWord_159701, baseEnd_159701] using wordTrace_append hprefix tailTrace_159701
  have hstable : (prefixWord ++ tailWord_159701).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159701).length < 2 ^ (prefixWord ++ tailWord_159701).sum := by decide
  have hdescent : baseEnd_159701 < baseStart_159701 := by decide
  rcases family_descends (prefixWord ++ tailWord_159701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159724 : List Nat := [2, 2, 1, 1, 2, 1, 1, 9]
def baseStart_159724 : Nat := 118140960795 + 159724 * 2 ^ 59
def prefixEnd_159724 : Nat := 4983230072969 + 3 ^ 40 * 159724 * 2
def baseEnd_159724 : Nat := 48601590553385666853599

theorem tailTrace_159724 : CollatzResearch.WordTrace tailWord_159724 prefixEnd_159724 48601590553385666853599 := by
  unfold tailWord_159724
  simp only [CollatzResearch.WordTrace]
  refine ⟨2912806436677350766271113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3883741915569801021694817 2912806436677350766271113)
  ·
    refine ⟨2184604827508013074703335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2912806436677350766271113 2184604827508013074703335)
    ·
      refine ⟨3276907241262019612055003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2184604827508013074703335 3276907241262019612055003)
      ·
        refine ⟨4915360861893029418082505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3276907241262019612055003 4915360861893029418082505)
        ·
          refine ⟨3686520646419772063561879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4915360861893029418082505 3686520646419772063561879)
          ·
            refine ⟨5529780969629658095342819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3686520646419772063561879 5529780969629658095342819)
            ·
              refine ⟨8294671454444487143014229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5529780969629658095342819 8294671454444487143014229)
              ·
                refine ⟨48601590553385666853599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8294671454444487143014229 48601590553385666853599)
                ·
                  rfl

theorem cell19_159724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_159724 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_159724 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_159724 prefixEnd_159724 := by exact prefixLift 159724
  have htrace : WordTrace (prefixWord ++ tailWord_159724) baseStart_159724 baseEnd_159724 := by
    simpa [prefixWord, tailWord_159724, baseEnd_159724] using wordTrace_append hprefix tailTrace_159724
  have hstable : (prefixWord ++ tailWord_159724).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159724).length < 2 ^ (prefixWord ++ tailWord_159724).sum := by decide
  have hdescent : baseEnd_159724 < baseStart_159724 := by decide
  rcases family_descends (prefixWord ++ tailWord_159724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159836 : List Nat := [2, 2, 4, 1, 1, 2, 2, 5]
def baseStart_159836 : Nat := 118140960795 + 159836 * 2 ^ 59
def prefixEnd_159836 : Nat := 4983230072969 + 3 ^ 40 * 159836 * 2
def baseEnd_159836 : Nat := 48635670454602592364405

theorem tailTrace_159836 : CollatzResearch.WordTrace tailWord_159836 prefixEnd_159836 48635670454602592364405 := by
  unfold tailWord_159836
  simp only [CollatzResearch.WordTrace]
  refine ⟨2914848924474472330309681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3886465232632629773746241 2914848924474472330309681)
  ·
    refine ⟨2186136693355854247732261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2914848924474472330309681 2186136693355854247732261)
    ·
      refine ⟨409900630004222671449799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2186136693355854247732261 409900630004222671449799)
      ·
        refine ⟨614850945006334007174699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409900630004222671449799 614850945006334007174699)
        ·
          refine ⟨922276417509501010762049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 614850945006334007174699 922276417509501010762049)
          ·
            refine ⟨691707313132125758071537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 922276417509501010762049 691707313132125758071537)
            ·
              refine ⟨518780484849094318553653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 691707313132125758071537 518780484849094318553653)
              ·
                refine ⟨48635670454602592364405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 518780484849094318553653 48635670454602592364405)
                ·
                  rfl

theorem cell19_159836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 5].length) (baseStart_159836 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_159836 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_159836 prefixEnd_159836 := by exact prefixLift 159836
  have htrace : WordTrace (prefixWord ++ tailWord_159836) baseStart_159836 baseEnd_159836 := by
    simpa [prefixWord, tailWord_159836, baseEnd_159836] using wordTrace_append hprefix tailTrace_159836
  have hstable : (prefixWord ++ tailWord_159836).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159836).length < 2 ^ (prefixWord ++ tailWord_159836).sum := by decide
  have hdescent : baseEnd_159836 < baseStart_159836 := by decide
  rcases family_descends (prefixWord ++ tailWord_159836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159893 : List Nat := [1, 3, 2, 1, 1, 1, 7, 3]
def baseStart_159893 : Nat := 118140960795 + 159893 * 2 ^ 59
def prefixEnd_159893 : Nat := 4983230072969 + 3 ^ 40 * 159893 * 2
def baseEnd_159893 : Nat := 48653014690043349097583

theorem tailTrace_159893 : CollatzResearch.WordTrace tailWord_159893 prefixEnd_159893 48653014690043349097583 := by
  unfold tailWord_159893
  simp only [CollatzResearch.WordTrace]
  refine ⟨5831776809742443395444333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3887851206494962263629555 5831776809742443395444333)
  ·
    refine ⟨2186916303653416273291625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5831776809742443395444333 2186916303653416273291625)
    ·
      refine ⟨1640187227740062204968719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2186916303653416273291625 1640187227740062204968719)
      ·
        refine ⟨2460280841610093307453079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1640187227740062204968719 2460280841610093307453079)
        ·
          refine ⟨3690421262415139961179619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2460280841610093307453079 3690421262415139961179619)
          ·
            refine ⟨5535631893622709941769429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3690421262415139961179619 5535631893622709941769429)
            ·
              refine ⟨129741372506782264260221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 5535631893622709941769429 129741372506782264260221)
              ·
                refine ⟨48653014690043349097583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129741372506782264260221 48653014690043349097583)
                ·
                  rfl

theorem cell19_159893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 3].length) (baseStart_159893 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_159893 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_159893 prefixEnd_159893 := by exact prefixLift 159893
  have htrace : WordTrace (prefixWord ++ tailWord_159893) baseStart_159893 baseEnd_159893 := by
    simpa [prefixWord, tailWord_159893, baseEnd_159893] using wordTrace_append hprefix tailTrace_159893
  have hstable : (prefixWord ++ tailWord_159893).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159893).length < 2 ^ (prefixWord ++ tailWord_159893).sum := by decide
  have hdescent : baseEnd_159893 < baseStart_159893 := by decide
  rcases family_descends (prefixWord ++ tailWord_159893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159933 : List Nat := [1, 4, 1, 2, 1, 1, 1, 8]
def baseStart_159933 : Nat := 118140960795 + 159933 * 2 ^ 59
def prefixEnd_159933 : Nat := 4983230072969 + 3 ^ 40 * 159933 * 2
def baseEnd_159933 : Nat := 48665186083335108208585

theorem tailTrace_159933 : CollatzResearch.WordTrace tailWord_159933 prefixEnd_159933 48665186083335108208585 := by
  unfold tailWord_159933
  simp only [CollatzResearch.WordTrace]
  refine ⟨5833235729597530226900453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3888823819731686817933635 5833235729597530226900453)
  ·
    refine ⟨1093731699299536917543835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5833235729597530226900453 1093731699299536917543835)
    ·
      refine ⟨1640597548949305376315753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1093731699299536917543835 1640597548949305376315753)
      ·
        refine ⟨1230448161711979032236815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1640597548949305376315753 1230448161711979032236815)
        ·
          refine ⟨1845672242567968548355223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1230448161711979032236815 1845672242567968548355223)
          ·
            refine ⟨2768508363851952822532835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1845672242567968548355223 2768508363851952822532835)
            ·
              refine ⟨4152762545777929233799253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2768508363851952822532835 4152762545777929233799253)
              ·
                refine ⟨48665186083335108208585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4152762545777929233799253 48665186083335108208585)
                ·
                  rfl

theorem cell19_159933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 8].length) (baseStart_159933 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_159933 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_159933 prefixEnd_159933 := by exact prefixLift 159933
  have htrace : WordTrace (prefixWord ++ tailWord_159933) baseStart_159933 baseEnd_159933 := by
    simpa [prefixWord, tailWord_159933, baseEnd_159933] using wordTrace_append hprefix tailTrace_159933
  have hstable : (prefixWord ++ tailWord_159933).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159933).length < 2 ^ (prefixWord ++ tailWord_159933).sum := by decide
  have hdescent : baseEnd_159933 < baseStart_159933 := by decide
  rcases family_descends (prefixWord ++ tailWord_159933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159948 : List Nat := [2, 2, 1, 6, 1, 1, 1, 5]
def baseStart_159948 : Nat := 118140960795 + 159948 * 2 ^ 59
def prefixEnd_159948 : Nat := 4983230072969 + 3 ^ 40 * 159948 * 2
def baseEnd_159948 : Nat := 48669750355819517875211

theorem tailTrace_159948 : CollatzResearch.WordTrace tailWord_159948 prefixEnd_159948 48669750355819517875211 := by
  unfold tailWord_159948
  simp only [CollatzResearch.WordTrace]
  refine ⟨2916891412271593894348249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3889188549695458525797665 2916891412271593894348249)
  ·
    refine ⟨2187668559203695420761187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2916891412271593894348249 2187668559203695420761187)
    ·
      refine ⟨3281502838805543131141781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2187668559203695420761187 3281502838805543131141781)
      ·
        refine ⟨153820445569009834272271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3281502838805543131141781 153820445569009834272271)
        ·
          refine ⟨230730668353514751408407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153820445569009834272271 230730668353514751408407)
          ·
            refine ⟨346096002530272127112611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230730668353514751408407 346096002530272127112611)
            ·
              refine ⟨519144003795408190668917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346096002530272127112611 519144003795408190668917)
              ·
                refine ⟨48669750355819517875211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 519144003795408190668917 48669750355819517875211)
                ·
                  rfl

theorem cell19_159948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 5].length) (baseStart_159948 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_159948 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_159948 prefixEnd_159948 := by exact prefixLift 159948
  have htrace : WordTrace (prefixWord ++ tailWord_159948) baseStart_159948 baseEnd_159948 := by
    simpa [prefixWord, tailWord_159948, baseEnd_159948] using wordTrace_append hprefix tailTrace_159948
  have hstable : (prefixWord ++ tailWord_159948).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159948).length < 2 ^ (prefixWord ++ tailWord_159948).sum := by decide
  have hdescent : baseEnd_159948 < baseStart_159948 := by decide
  rcases family_descends (prefixWord ++ tailWord_159948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159950 : List Nat := [4, 1, 1, 1, 4, 2, 1, 5]
def baseStart_159950 : Nat := 118140960795 + 159950 * 2 ^ 59
def prefixEnd_159950 : Nat := 4983230072969 + 3 ^ 40 * 159950 * 2
def baseEnd_159950 : Nat := 48670358925484105830761

theorem tailTrace_159950 : CollatzResearch.WordTrace tailWord_159950 prefixEnd_159950 48670358925484105830761 := by
  unfold tailWord_159950
  simp only [CollatzResearch.WordTrace]
  refine ⟨729231971316992766283663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3889237180357294753512869 729231971316992766283663)
  ·
    refine ⟨1093847956975489149425495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 729231971316992766283663 1093847956975489149425495)
    ·
      refine ⟨1640771935463233724138243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1093847956975489149425495 1640771935463233724138243)
      ·
        refine ⟨2461157903194850586207365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1640771935463233724138243 2461157903194850586207365)
        ·
          refine ⟨461467106849034484913881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2461157903194850586207365 461467106849034484913881)
          ·
            refine ⟨346100330136775863685411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 461467106849034484913881 346100330136775863685411)
            ·
              refine ⟨519150495205163795528117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346100330136775863685411 519150495205163795528117)
              ·
                refine ⟨48670358925484105830761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 519150495205163795528117 48670358925484105830761)
                ·
                  rfl

theorem cell19_159950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_159950 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_159950 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_159950 prefixEnd_159950 := by exact prefixLift 159950
  have htrace : WordTrace (prefixWord ++ tailWord_159950) baseStart_159950 baseEnd_159950 := by
    simpa [prefixWord, tailWord_159950, baseEnd_159950] using wordTrace_append hprefix tailTrace_159950
  have hstable : (prefixWord ++ tailWord_159950).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159950).length < 2 ^ (prefixWord ++ tailWord_159950).sum := by decide
  have hdescent : baseEnd_159950 < baseStart_159950 := by decide
  rcases family_descends (prefixWord ++ tailWord_159950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160009 : List Nat := [1, 2, 1, 1, 3, 4, 2, 5]
def baseStart_160009 : Nat := 118140960795 + 160009 * 2 ^ 59
def prefixEnd_160009 : Nat := 4983230072969 + 3 ^ 40 * 160009 * 2
def baseEnd_160009 : Nat := 48688311730589450519489

theorem tailTrace_160009 : CollatzResearch.WordTrace tailWord_160009 prefixEnd_160009 48688311730589450519489 := by
  unfold tailWord_160009
  simp only [CollatzResearch.WordTrace]
  refine ⟨5836007677322195206667081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3890671784881463471111387 5836007677322195206667081)
  ·
    refine ⟨4377005757991646405000311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5836007677322195206667081 4377005757991646405000311)
    ·
      refine ⟨6565508636987469607500467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4377005757991646405000311 6565508636987469607500467)
      ·
        refine ⟨9848262955481204411250701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6565508636987469607500467 9848262955481204411250701)
        ·
          refine ⟨3693098608305451654219013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9848262955481204411250701 3693098608305451654219013)
          ·
            refine ⟨692455989057272185166065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3693098608305451654219013 692455989057272185166065)
            ·
              refine ⟨519341991792954138874549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 692455989057272185166065 519341991792954138874549)
              ·
                refine ⟨48688311730589450519489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 519341991792954138874549 48688311730589450519489)
                ·
                  rfl

theorem cell19_160009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 5].length) (baseStart_160009 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_160009 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_160009 prefixEnd_160009 := by exact prefixLift 160009
  have htrace : WordTrace (prefixWord ++ tailWord_160009) baseStart_160009 baseEnd_160009 := by
    simpa [prefixWord, tailWord_160009, baseEnd_160009] using wordTrace_append hprefix tailTrace_160009
  have hstable : (prefixWord ++ tailWord_160009).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160009).length < 2 ^ (prefixWord ++ tailWord_160009).sum := by decide
  have hdescent : baseEnd_160009 < baseStart_160009 := by decide
  rcases family_descends (prefixWord ++ tailWord_160009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160026 : List Nat := [3, 1, 1, 3, 5, 6]
def baseStart_160026 : Nat := 118140960795 + 160026 * 2 ^ 59
def prefixEnd_160026 : Nat := 4983230072969 + 3 ^ 40 * 160026 * 2
def baseEnd_160026 : Nat := 5410387174748716460185

theorem tailTrace_160026 : CollatzResearch.WordTrace tailWord_160026 prefixEnd_160026 5410387174748716460185 := by
  unfold tailWord_160026
  simp only [CollatzResearch.WordTrace]
  refine ⟨1459156929565151777508983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3891085145507071406690621 1459156929565151777508983)
  ·
    refine ⟨2188735394347727666263475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1459156929565151777508983 2188735394347727666263475)
    ·
      refine ⟨3283103091521591499395213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2188735394347727666263475 3283103091521591499395213)
      ·
        refine ⟨1231163659320596812273205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3283103091521591499395213 1231163659320596812273205)
        ·
          refine ⟨115421593061305951150613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1231163659320596812273205 115421593061305951150613)
          ·
            refine ⟨5410387174748716460185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 115421593061305951150613 5410387174748716460185)
            ·
              rfl

theorem cell19_160026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 6].length) (baseStart_160026 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_160026 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_160026 prefixEnd_160026 := by exact prefixLift 160026
  have htrace : WordTrace (prefixWord ++ tailWord_160026) baseStart_160026 baseEnd_160026 := by
    simpa [prefixWord, tailWord_160026, baseEnd_160026] using wordTrace_append hprefix tailTrace_160026
  have hstable : (prefixWord ++ tailWord_160026).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160026).length < 2 ^ (prefixWord ++ tailWord_160026).sum := by decide
  have hdescent : baseEnd_160026 < baseStart_160026 := by decide
  rcases family_descends (prefixWord ++ tailWord_160026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160039 : List Nat := [1, 1, 8, 1, 1, 2, 1, 4]
def baseStart_160039 : Nat := 118140960795 + 160039 * 2 ^ 59
def prefixEnd_160039 : Nat := 4983230072969 + 3 ^ 40 * 160039 * 2
def baseEnd_160039 : Nat := 48697440275558269852741

theorem tailTrace_160039 : CollatzResearch.WordTrace tailWord_160039 prefixEnd_160039 48697440275558269852741 := by
  unfold tailWord_160039
  simp only [CollatzResearch.WordTrace]
  refine ⟨5837101867213510330259171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3891401244809006886839447 5837101867213510330259171)
  ·
    refine ⟨8755652800820265495388757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5837101867213510330259171 8755652800820265495388757)
    ·
      refine ⟨102605306259612486274087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 8755652800820265495388757 102605306259612486274087)
      ·
        refine ⟨153907959389418729411131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102605306259612486274087 153907959389418729411131)
        ·
          refine ⟨230861939084128094116697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153907959389418729411131 230861939084128094116697)
          ·
            refine ⟨173146454313096070587523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230861939084128094116697 173146454313096070587523)
            ·
              refine ⟨259719681469644105881285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173146454313096070587523 259719681469644105881285)
              ·
                refine ⟨48697440275558269852741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 259719681469644105881285 48697440275558269852741)
                ·
                  rfl

theorem cell19_160039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 4].length) (baseStart_160039 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_160039 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_160039 prefixEnd_160039 := by exact prefixLift 160039
  have htrace : WordTrace (prefixWord ++ tailWord_160039) baseStart_160039 baseEnd_160039 := by
    simpa [prefixWord, tailWord_160039, baseEnd_160039] using wordTrace_append hprefix tailTrace_160039
  have hstable : (prefixWord ++ tailWord_160039).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160039).length < 2 ^ (prefixWord ++ tailWord_160039).sum := by decide
  have hdescent : baseEnd_160039 < baseStart_160039 := by decide
  rcases family_descends (prefixWord ++ tailWord_160039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160047 : List Nat := [1, 1, 2, 1, 2, 1, 7, 4]
def baseStart_160047 : Nat := 118140960795 + 160047 * 2 ^ 59
def prefixEnd_160047 : Nat := 4983230072969 + 3 ^ 40 * 160047 * 2
def baseEnd_160047 : Nat := 48699874554216621674941

theorem tailTrace_160047 : CollatzResearch.WordTrace tailWord_160047 prefixEnd_160047 48699874554216621674941 := by
  unfold tailWord_160047
  simp only [CollatzResearch.WordTrace]
  refine ⟨5837393651184527696550395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3891595767456351797700263 5837393651184527696550395)
  ·
    refine ⟨8756090476776791544825593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5837393651184527696550395 8756090476776791544825593)
    ·
      refine ⟨6567067857582593658619195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8756090476776791544825593 6567067857582593658619195)
      ·
        refine ⟨9850601786373890487928793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6567067857582593658619195 9850601786373890487928793)
        ·
          refine ⟨7387951339780417865946595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9850601786373890487928793 7387951339780417865946595)
          ·
            refine ⟨11081927009670626798919893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7387951339780417865946595 11081927009670626798919893)
            ·
              refine ⟨259732664289155315599685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 11081927009670626798919893 259732664289155315599685)
              ·
                refine ⟨48699874554216621674941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 259732664289155315599685 48699874554216621674941)
                ·
                  rfl

theorem cell19_160047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 4].length) (baseStart_160047 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_160047 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_160047 prefixEnd_160047 := by exact prefixLift 160047
  have htrace : WordTrace (prefixWord ++ tailWord_160047) baseStart_160047 baseEnd_160047 := by
    simpa [prefixWord, tailWord_160047, baseEnd_160047] using wordTrace_append hprefix tailTrace_160047
  have hstable : (prefixWord ++ tailWord_160047).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160047).length < 2 ^ (prefixWord ++ tailWord_160047).sum := by decide
  have hdescent : baseEnd_160047 < baseStart_160047 := by decide
  rcases family_descends (prefixWord ++ tailWord_160047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160062 : List Nat := [4, 2, 1, 2, 1, 3, 3, 3]
def baseStart_160062 : Nat := 118140960795 + 160062 * 2 ^ 59
def prefixEnd_160062 : Nat := 4983230072969 + 3 ^ 40 * 160062 * 2
def baseEnd_160062 : Nat := 48704438826701031341567

theorem tailTrace_160062 : CollatzResearch.WordTrace tailWord_160062 prefixEnd_160062 48704438826701031341567 := by
  unfold tailWord_160062
  simp only [CollatzResearch.WordTrace]
  refine ⟨729742593266273157293305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3891960497420123505564293 729742593266273157293305)
  ·
    refine ⟨547306944949704867969979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 729742593266273157293305 547306944949704867969979)
    ·
      refine ⟨820960417424557301954969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 547306944949704867969979 820960417424557301954969)
      ·
        refine ⟨615720313068417976466227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 820960417424557301954969 615720313068417976466227)
        ·
          refine ⟨923580469602626964699341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 615720313068417976466227 923580469602626964699341)
          ·
            refine ⟨346342676100985111762253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 923580469602626964699341 346342676100985111762253)
            ·
              refine ⟨129878503537869416910845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 346342676100985111762253 129878503537869416910845)
              ·
                refine ⟨48704438826701031341567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129878503537869416910845 48704438826701031341567)
                ·
                  rfl

theorem cell19_160062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_160062 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_160062 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_160062 prefixEnd_160062 := by exact prefixLift 160062
  have htrace : WordTrace (prefixWord ++ tailWord_160062) baseStart_160062 baseEnd_160062 := by
    simpa [prefixWord, tailWord_160062, baseEnd_160062] using wordTrace_append hprefix tailTrace_160062
  have hstable : (prefixWord ++ tailWord_160062).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160062).length < 2 ^ (prefixWord ++ tailWord_160062).sum := by decide
  have hdescent : baseEnd_160062 < baseStart_160062 := by decide
  rcases family_descends (prefixWord ++ tailWord_160062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160123 : List Nat := [1, 1, 1, 1, 1, 8, 1, 5]
def baseStart_160123 : Nat := 118140960795 + 160123 * 2 ^ 59
def prefixEnd_160123 : Nat := 4983230072969 + 3 ^ 40 * 160123 * 2
def baseEnd_160123 : Nat := 48723000201470963985845

theorem tailTrace_160123 : CollatzResearch.WordTrace tailWord_160123 prefixEnd_160123 48723000201470963985845 := by
  unfold tailWord_160123
  simp only [CollatzResearch.WordTrace]
  refine ⟨5840165598909192676317023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3893443732606128450878015 5840165598909192676317023)
  ·
    refine ⟨8760248398363789014475535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5840165598909192676317023 8760248398363789014475535)
    ·
      refine ⟨13140372597545683521713303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8760248398363789014475535 13140372597545683521713303)
      ·
        refine ⟨19710558896318525282569955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13140372597545683521713303 19710558896318525282569955)
        ·
          refine ⟨29565838344477787923854933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19710558896318525282569955 29565838344477787923854933)
          ·
            refine ⟨346474668099349077232675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 29565838344477787923854933 346474668099349077232675)
            ·
              refine ⟨519712002149023615849013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346474668099349077232675 519712002149023615849013)
              ·
                refine ⟨48723000201470963985845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 519712002149023615849013 48723000201470963985845)
                ·
                  rfl

theorem cell19_160123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 5].length) (baseStart_160123 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_160123 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_160123 prefixEnd_160123 := by exact prefixLift 160123
  have htrace : WordTrace (prefixWord ++ tailWord_160123) baseStart_160123 baseEnd_160123 := by
    simpa [prefixWord, tailWord_160123, baseEnd_160123] using wordTrace_append hprefix tailTrace_160123
  have hstable : (prefixWord ++ tailWord_160123).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160123).length < 2 ^ (prefixWord ++ tailWord_160123).sum := by decide
  have hdescent : baseEnd_160123 < baseStart_160123 := by decide
  rcases family_descends (prefixWord ++ tailWord_160123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160138 : List Nat := [3, 1, 2, 5, 1, 2, 5]
def baseStart_160138 : Nat := 118140960795 + 160138 * 2 ^ 59
def prefixEnd_160138 : Nat := 4983230072969 + 3 ^ 40 * 160138 * 2
def baseEnd_160138 : Nat := 16242521491318457884157

theorem tailTrace_160138 : CollatzResearch.WordTrace tailWord_160138 prefixEnd_160138 16242521491318457884157 := by
  unfold tailWord_160138
  simp only [CollatzResearch.WordTrace]
  refine ⟨1460178173463712559528267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3893808462569900158742045 1460178173463712559528267)
  ·
    refine ⟨2190267260195568839292401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1460178173463712559528267 2190267260195568839292401)
    ·
      refine ⟨1642700445146676629469301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2190267260195568839292401 1642700445146676629469301)
      ·
        refine ⟨154003166732500934012747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1642700445146676629469301 154003166732500934012747)
        ·
          refine ⟨231004750098751401019121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154003166732500934012747 231004750098751401019121)
          ·
            refine ⟨173253562574063550764341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231004750098751401019121 173253562574063550764341)
            ·
              refine ⟨16242521491318457884157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 173253562574063550764341 16242521491318457884157)
              ·
                rfl

theorem cell19_160138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 5].length) (baseStart_160138 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_160138 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_160138 prefixEnd_160138 := by exact prefixLift 160138
  have htrace : WordTrace (prefixWord ++ tailWord_160138) baseStart_160138 baseEnd_160138 := by
    simpa [prefixWord, tailWord_160138, baseEnd_160138] using wordTrace_append hprefix tailTrace_160138
  have hstable : (prefixWord ++ tailWord_160138).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160138).length < 2 ^ (prefixWord ++ tailWord_160138).sum := by decide
  have hdescent : baseEnd_160138 < baseStart_160138 := by decide
  rcases family_descends (prefixWord ++ tailWord_160138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160193 : List Nat := [1, 2, 7, 1, 2, 6]
def baseStart_160193 : Nat := 118140960795 + 160193 * 2 ^ 59
def prefixEnd_160193 : Nat := 4983230072969 + 3 ^ 40 * 160193 * 2
def baseEnd_160193 : Nat := 5416033348859060270011

theorem tailTrace_160193 : CollatzResearch.WordTrace tailWord_160193 prefixEnd_160193 5416033348859060270011 := by
  unfold tailWord_160193
  simp only [CollatzResearch.WordTrace]
  refine ⟨5842718708655594631365233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3895145805770396420910155 5842718708655594631365233)
  ·
    refine ⟨4382039031491695973523925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5842718708655594631365233 4382039031491695973523925)
    ·
      refine ⟨102704039800586624379467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 4382039031491695973523925 102704039800586624379467)
      ·
        refine ⟨154056059700879936569201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102704039800586624379467 154056059700879936569201)
        ·
          refine ⟨115542044775659952426901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154056059700879936569201 115542044775659952426901)
          ·
            refine ⟨5416033348859060270011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 115542044775659952426901 5416033348859060270011)
            ·
              rfl

theorem cell19_160193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 6].length) (baseStart_160193 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_160193 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_160193 prefixEnd_160193 := by exact prefixLift 160193
  have htrace : WordTrace (prefixWord ++ tailWord_160193) baseStart_160193 baseEnd_160193 := by
    simpa [prefixWord, tailWord_160193, baseEnd_160193] using wordTrace_append hprefix tailTrace_160193
  have hstable : (prefixWord ++ tailWord_160193).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160193).length < 2 ^ (prefixWord ++ tailWord_160193).sum := by decide
  have hdescent : baseEnd_160193 < baseStart_160193 := by decide
  rcases family_descends (prefixWord ++ tailWord_160193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160288 : List Nat := [2, 1, 1, 6, 3, 1, 2, 3]
def baseStart_160288 : Nat := 118140960795 + 160288 * 2 ^ 59
def prefixEnd_160288 : Nat := 4983230072969 + 3 ^ 40 * 160288 * 2
def baseEnd_160288 : Nat := 48773207198799470318729

theorem tailTrace_160288 : CollatzResearch.WordTrace tailWord_160288 prefixEnd_160288 48773207198799470318729 := by
  unfold tailWord_160288
  simp only [CollatzResearch.WordTrace]
  refine ⟨2923091821655712928036759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3897455762207617237382345 2923091821655712928036759)
  ·
    refine ⟨4384637732483569392055139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2923091821655712928036759 4384637732483569392055139)
    ·
      refine ⟨6576956598725354088082709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4384637732483569392055139 6576956598725354088082709)
      ·
        refine ⟨308294840565250972878877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6576956598725354088082709 308294840565250972878877)
        ·
          refine ⟨115610565211969114829579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 308294840565250972878877 115610565211969114829579)
          ·
            refine ⟨173415847817953672244369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115610565211969114829579 173415847817953672244369)
            ·
              refine ⟨130061885863465254183277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173415847817953672244369 130061885863465254183277)
              ·
                refine ⟨48773207198799470318729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130061885863465254183277 48773207198799470318729)
                ·
                  rfl

theorem cell19_160288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 3].length) (baseStart_160288 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_160288 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_160288 prefixEnd_160288 := by exact prefixLift 160288
  have htrace : WordTrace (prefixWord ++ tailWord_160288) baseStart_160288 baseEnd_160288 := by
    simpa [prefixWord, tailWord_160288, baseEnd_160288] using wordTrace_append hprefix tailTrace_160288
  have hstable : (prefixWord ++ tailWord_160288).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160288).length < 2 ^ (prefixWord ++ tailWord_160288).sum := by decide
  have hdescent : baseEnd_160288 < baseStart_160288 := by decide
  rcases family_descends (prefixWord ++ tailWord_160288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160332 : List Nat := [2, 2, 1, 3, 1, 2, 4, 4]
def baseStart_160332 : Nat := 118140960795 + 160332 * 2 ^ 59
def prefixEnd_160332 : Nat := 4983230072969 + 3 ^ 40 * 160332 * 2
def baseEnd_160332 : Nat := 48786595731420405340831

theorem tailTrace_160332 : CollatzResearch.WordTrace tailWord_160332 prefixEnd_160332 48786595731420405340831 := by
  unfold tailWord_160332
  simp only [CollatzResearch.WordTrace]
  refine ⟨2923894227576010685337625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3898525636768014247116833 2923894227576010685337625)
  ·
    refine ⟨2192920670682008014003219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2923894227576010685337625 2192920670682008014003219)
    ·
      refine ⟨3289381006023012021004829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2192920670682008014003219 3289381006023012021004829)
      ·
        refine ⟨1233517877258629507876811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3289381006023012021004829 1233517877258629507876811)
        ·
          refine ⟨1850276815887944261815217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1233517877258629507876811 1850276815887944261815217)
          ·
            refine ⟨1387707611915958196361413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1850276815887944261815217 1387707611915958196361413)
            ·
              refine ⟨260195177234242161817765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1387707611915958196361413 260195177234242161817765)
              ·
                refine ⟨48786595731420405340831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 260195177234242161817765 48786595731420405340831)
                ·
                  rfl

theorem cell19_160332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 4].length) (baseStart_160332 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_160332 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_160332 prefixEnd_160332 := by exact prefixLift 160332
  have htrace : WordTrace (prefixWord ++ tailWord_160332) baseStart_160332 baseEnd_160332 := by
    simpa [prefixWord, tailWord_160332, baseEnd_160332] using wordTrace_append hprefix tailTrace_160332
  have hstable : (prefixWord ++ tailWord_160332).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160332).length < 2 ^ (prefixWord ++ tailWord_160332).sum := by decide
  have hdescent : baseEnd_160332 < baseStart_160332 := by decide
  rcases family_descends (prefixWord ++ tailWord_160332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160370 : List Nat := [3, 2, 1, 2, 4, 7]
def baseStart_160370 : Nat := 118140960795 + 160370 * 2 ^ 59
def prefixEnd_160370 : Nat := 4983230072969 + 3 ^ 40 * 160370 * 2
def baseEnd_160370 : Nat := 5422017617227508499587

theorem tailTrace_160370 : CollatzResearch.WordTrace tailWord_160370 prefixEnd_160370 5422017617227508499587 := by
  unfold tailWord_160370
  simp only [CollatzResearch.WordTrace]
  refine ⟨1462293607253588465139641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3899449619342902573705709 1462293607253588465139641)
  ·
    refine ⟨1096720205440191348854731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1462293607253588465139641 1096720205440191348854731)
    ·
      refine ⟨1645080308160287023282097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1096720205440191348854731 1645080308160287023282097)
      ·
        refine ⟨1233810231120215267461573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1645080308160287023282097 1233810231120215267461573)
        ·
          refine ⟨231339418335040362649045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1233810231120215267461573 231339418335040362649045)
          ·
            refine ⟨5422017617227508499587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 231339418335040362649045 5422017617227508499587)
            ·
              rfl

theorem cell19_160370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 7].length) (baseStart_160370 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_160370 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_160370 prefixEnd_160370 := by exact prefixLift 160370
  have htrace : WordTrace (prefixWord ++ tailWord_160370) baseStart_160370 baseEnd_160370 := by
    simpa [prefixWord, tailWord_160370, baseEnd_160370] using wordTrace_append hprefix tailTrace_160370
  have hstable : (prefixWord ++ tailWord_160370).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160370).length < 2 ^ (prefixWord ++ tailWord_160370).sum := by decide
  have hdescent : baseEnd_160370 < baseStart_160370 := by decide
  rcases family_descends (prefixWord ++ tailWord_160370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160389 : List Nat := [1, 3, 1, 1, 4, 2, 3, 4]
def baseStart_160389 : Nat := 118140960795 + 160389 * 2 ^ 59
def prefixEnd_160389 : Nat := 4983230072969 + 3 ^ 40 * 160389 * 2
def baseEnd_160389 : Nat := 48803939966861162074009

theorem tailTrace_160389 : CollatzResearch.WordTrace tailWord_160389 prefixEnd_160389 48803939966861162074009 := by
  unfold tailWord_160389
  simp only [CollatzResearch.WordTrace]
  refine ⟨5849867415945520105500221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3899911610630346737000147 5849867415945520105500221)
  ·
    refine ⟨2193700280979570039562583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5849867415945520105500221 2193700280979570039562583)
    ·
      refine ⟨3290550421469355059343875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2193700280979570039562583 3290550421469355059343875)
      ·
        refine ⟨4935825632204032589015813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3290550421469355059343875 4935825632204032589015813)
        ·
          refine ⟨925467306038256110440465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4935825632204032589015813 925467306038256110440465)
          ·
            refine ⟨694100479528692082830349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 925467306038256110440465 694100479528692082830349)
            ·
              refine ⟨260287679823259531061381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 694100479528692082830349 260287679823259531061381)
              ·
                refine ⟨48803939966861162074009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 260287679823259531061381 48803939966861162074009)
                ·
                  rfl

theorem cell19_160389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 4].length) (baseStart_160389 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_160389 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_160389 prefixEnd_160389 := by exact prefixLift 160389
  have htrace : WordTrace (prefixWord ++ tailWord_160389) baseStart_160389 baseEnd_160389 := by
    simpa [prefixWord, tailWord_160389, baseEnd_160389] using wordTrace_append hprefix tailTrace_160389
  have hstable : (prefixWord ++ tailWord_160389).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160389).length < 2 ^ (prefixWord ++ tailWord_160389).sum := by decide
  have hdescent : baseEnd_160389 < baseStart_160389 := by decide
  rcases family_descends (prefixWord ++ tailWord_160389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160404 : List Nat := [2, 4, 2, 2, 1, 2, 3, 3]
def baseStart_160404 : Nat := 118140960795 + 160404 * 2 ^ 59
def prefixEnd_160404 : Nat := 4983230072969 + 3 ^ 40 * 160404 * 2
def baseEnd_160404 : Nat := 48808504239345571740635

theorem tailTrace_160404 : CollatzResearch.WordTrace tailWord_160404 prefixEnd_160404 48808504239345571740635 := by
  unfold tailWord_160404
  simp only [CollatzResearch.WordTrace]
  refine ⟨2925207255445588833648133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3900276340594118444864177 2925207255445588833648133)
  ·
    refine ⟨548476360396047906309025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2925207255445588833648133 548476360396047906309025)
    ·
      refine ⟨411357270297035929731769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 548476360396047906309025 411357270297035929731769)
      ·
        refine ⟨308517952722776947298827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 411357270297035929731769 308517952722776947298827)
        ·
          refine ⟨462776929084165420948241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308517952722776947298827 462776929084165420948241)
          ·
            refine ⟨347082696813124065711181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 462776929084165420948241 347082696813124065711181)
            ·
              refine ⟨130156011304921524641693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 347082696813124065711181 130156011304921524641693)
              ·
                refine ⟨48808504239345571740635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130156011304921524641693 48808504239345571740635)
                ·
                  rfl

theorem cell19_160404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 3].length) (baseStart_160404 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_160404 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_160404 prefixEnd_160404 := by exact prefixLift 160404
  have htrace : WordTrace (prefixWord ++ tailWord_160404) baseStart_160404 baseEnd_160404 := by
    simpa [prefixWord, tailWord_160404, baseEnd_160404] using wordTrace_append hprefix tailTrace_160404
  have hstable : (prefixWord ++ tailWord_160404).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160404).length < 2 ^ (prefixWord ++ tailWord_160404).sum := by decide
  have hdescent : baseEnd_160404 < baseStart_160404 := by decide
  rcases family_descends (prefixWord ++ tailWord_160404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160446 : List Nat := [4, 2, 1, 1, 2, 1, 2, 6]
def baseStart_160446 : Nat := 118140960795 + 160446 * 2 ^ 59
def prefixEnd_160446 : Nat := 4983230072969 + 3 ^ 40 * 160446 * 2
def baseEnd_160446 : Nat := 48821284202301918807187

theorem tailTrace_160446 : CollatzResearch.WordTrace tailWord_160446 prefixEnd_160446 48821284202301918807187 := by
  unfold tailWord_160446
  simp only [CollatzResearch.WordTrace]
  refine ⟨731493297092377355040649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3901297584492679226883461 731493297092377355040649)
  ·
    refine ⟨548619972819283016280487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 731493297092377355040649 548619972819283016280487)
    ·
      refine ⟨822929959228924524420731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 548619972819283016280487 822929959228924524420731)
      ·
        refine ⟨1234394938843386786631097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 822929959228924524420731 1234394938843386786631097)
        ·
          refine ⟨925796204132540089973323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1234394938843386786631097 925796204132540089973323)
          ·
            refine ⟨1388694306198810134959985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 925796204132540089973323 1388694306198810134959985)
            ·
              refine ⟨1041520729649107601219989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1388694306198810134959985 1041520729649107601219989)
              ·
                refine ⟨48821284202301918807187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1041520729649107601219989 48821284202301918807187)
                ·
                  rfl

theorem cell19_160446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_160446 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_160446 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_160446 prefixEnd_160446 := by exact prefixLift 160446
  have htrace : WordTrace (prefixWord ++ tailWord_160446) baseStart_160446 baseEnd_160446 := by
    simpa [prefixWord, tailWord_160446, baseEnd_160446] using wordTrace_append hprefix tailTrace_160446
  have hstable : (prefixWord ++ tailWord_160446).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160446).length < 2 ^ (prefixWord ++ tailWord_160446).sum := by decide
  have hdescent : baseEnd_160446 < baseStart_160446 := by decide
  rcases family_descends (prefixWord ++ tailWord_160446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160461 : List Nat := [1, 6, 2, 1, 2, 1, 1, 5]
def baseStart_160461 : Nat := 118140960795 + 160461 * 2 ^ 59
def prefixEnd_160461 : Nat := 4983230072969 + 3 ^ 40 * 160461 * 2
def baseEnd_160461 : Nat := 48825848474786328473813

theorem tailTrace_160461 : CollatzResearch.WordTrace tailWord_160461 prefixEnd_160461 48825848474786328473813 := by
  unfold tailWord_160461
  simp only [CollatzResearch.WordTrace]
  refine ⟨5852493471684676402121237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3901662314456450934747491 5852493471684676402121237)
  ·
    refine ⟨274335631485219206349433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5852493471684676402121237 274335631485219206349433)
    ·
      refine ⟨205751723613914404762075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274335631485219206349433 205751723613914404762075)
      ·
        refine ⟨308627585420871607143113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205751723613914404762075 308627585420871607143113)
        ·
          refine ⟨231470689065653705357335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308627585420871607143113 231470689065653705357335)
          ·
            refine ⟨347206033598480558036003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231470689065653705357335 347206033598480558036003)
            ·
              refine ⟨520809050397720837054005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 347206033598480558036003 520809050397720837054005)
              ·
                refine ⟨48825848474786328473813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 520809050397720837054005 48825848474786328473813)
                ·
                  rfl

theorem cell19_160461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 5].length) (baseStart_160461 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_160461 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_160461 prefixEnd_160461 := by exact prefixLift 160461
  have htrace : WordTrace (prefixWord ++ tailWord_160461) baseStart_160461 baseEnd_160461 := by
    simpa [prefixWord, tailWord_160461, baseEnd_160461] using wordTrace_append hprefix tailTrace_160461
  have hstable : (prefixWord ++ tailWord_160461).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160461).length < 2 ^ (prefixWord ++ tailWord_160461).sum := by decide
  have hdescent : baseEnd_160461 < baseStart_160461 := by decide
  rcases family_descends (prefixWord ++ tailWord_160461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160484 : List Nat := [2, 3, 1, 1, 1, 6, 5]
def baseStart_160484 : Nat := 118140960795 + 160484 * 2 ^ 59
def prefixEnd_160484 : Nat := 4983230072969 + 3 ^ 40 * 160484 * 2
def baseEnd_160484 : Nat := 16277615675309696654213

theorem tailTrace_160484 : CollatzResearch.WordTrace tailWord_160484 prefixEnd_160484 16277615675309696654213 := by
  unfold tailWord_160484
  simp only [CollatzResearch.WordTrace]
  refine ⟨2926666175300675665104253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3902221567067567553472337 2926666175300675665104253)
  ·
    refine ⟨1097499815737753374414095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2926666175300675665104253 1097499815737753374414095)
    ·
      refine ⟨1646249723606630061621143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1097499815737753374414095 1646249723606630061621143)
      ·
        refine ⟨2469374585409945092431715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1646249723606630061621143 2469374585409945092431715)
        ·
          refine ⟨3704061878114917638647573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2469374585409945092431715 3704061878114917638647573)
          ·
            refine ⟨173627900536636764311605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3704061878114917638647573 173627900536636764311605)
            ·
              refine ⟨16277615675309696654213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 173627900536636764311605 16277615675309696654213)
              ·
                rfl

theorem cell19_160484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 5].length) (baseStart_160484 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_160484 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_160484 prefixEnd_160484 := by exact prefixLift 160484
  have htrace : WordTrace (prefixWord ++ tailWord_160484) baseStart_160484 baseEnd_160484 := by
    simpa [prefixWord, tailWord_160484, baseEnd_160484] using wordTrace_append hprefix tailTrace_160484
  have hstable : (prefixWord ++ tailWord_160484).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160484).length < 2 ^ (prefixWord ++ tailWord_160484).sum := by decide
  have hdescent : baseEnd_160484 < baseStart_160484 := by decide
  rcases family_descends (prefixWord ++ tailWord_160484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160541 : List Nat := [1, 4, 2, 4, 8]
def baseStart_160541 : Nat := 118140960795 + 160541 * 2 ^ 59
def prefixEnd_160541 : Nat := 4983230072969 + 3 ^ 40 * 160541 * 2
def baseEnd_160541 : Nat := 1809266343013698025771

theorem tailTrace_160541 : CollatzResearch.WordTrace tailWord_160541 prefixEnd_160541 1809266343013698025771 := by
  unfold tailWord_160541
  simp only [CollatzResearch.WordTrace]
  refine ⟨5855411311394850065033477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3903607540929900043355651 5855411311394850065033477)
  ·
    refine ⟨1097889620886534387193777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5855411311394850065033477 1097889620886534387193777)
    ·
      refine ⟨823417215664900790395333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1097889620886534387193777 823417215664900790395333)
      ·
        refine ⟨154390727937168898199125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 823417215664900790395333 154390727937168898199125)
        ·
          refine ⟨1809266343013698025771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 154390727937168898199125 1809266343013698025771)
          ·
            rfl

theorem cell19_160541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 8].length) (baseStart_160541 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_160541 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_160541 prefixEnd_160541 := by exact prefixLift 160541
  have htrace : WordTrace (prefixWord ++ tailWord_160541) baseStart_160541 baseEnd_160541 := by
    simpa [prefixWord, tailWord_160541, baseEnd_160541] using wordTrace_append hprefix tailTrace_160541
  have hstable : (prefixWord ++ tailWord_160541).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160541).length < 2 ^ (prefixWord ++ tailWord_160541).sum := by decide
  have hdescent : baseEnd_160541 < baseStart_160541 := by decide
  rcases family_descends (prefixWord ++ tailWord_160541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160543 : List Nat := [1, 1, 2, 4, 2, 9]
def baseStart_160543 : Nat := 118140960795 + 160543 * 2 ^ 59
def prefixEnd_160543 : Nat := 4983230072969 + 3 ^ 40 * 160543 * 2
def baseEnd_160543 : Nat := 5427866647892714961263

theorem tailTrace_160543 : CollatzResearch.WordTrace tailWord_160543 prefixEnd_160543 5427866647892714961263 := by
  unfold tailWord_160543
  simp only [CollatzResearch.WordTrace]
  refine ⟨5855484257387604406606283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3903656171591736271070855 5855484257387604406606283)
  ·
    refine ⟨8783226386081406609909425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5855484257387604406606283 8783226386081406609909425)
    ·
      refine ⟨6587419789561054957432069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8783226386081406609909425 6587419789561054957432069)
      ·
        refine ⟨1235141210542697804518513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6587419789561054957432069 1235141210542697804518513)
        ·
          refine ⟨926355907907023353388885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1235141210542697804518513 926355907907023353388885)
          ·
            refine ⟨5427866647892714961263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 926355907907023353388885 5427866647892714961263)
            ·
              rfl

theorem cell19_160543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 9].length) (baseStart_160543 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_160543 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_160543 prefixEnd_160543 := by exact prefixLift 160543
  have htrace : WordTrace (prefixWord ++ tailWord_160543) baseStart_160543 baseEnd_160543 := by
    simpa [prefixWord, tailWord_160543, baseEnd_160543] using wordTrace_append hprefix tailTrace_160543
  have hstable : (prefixWord ++ tailWord_160543).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160543).length < 2 ^ (prefixWord ++ tailWord_160543).sum := by decide
  have hdescent : baseEnd_160543 < baseStart_160543 := by decide
  rcases family_descends (prefixWord ++ tailWord_160543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160554 : List Nat := [3, 1, 4, 3, 2, 1, 1, 4]
def baseStart_160554 : Nat := 118140960795 + 160554 * 2 ^ 59
def prefixEnd_160554 : Nat := 4983230072969 + 3 ^ 40 * 160554 * 2
def baseEnd_160554 : Nat := 48854146964189668406893

theorem tailTrace_160554 : CollatzResearch.WordTrace tailWord_160554 prefixEnd_160554 48854146964189668406893 := by
  unfold tailWord_160554
  simp only [CollatzResearch.WordTrace]
  refine ⟨1463971365086938321314179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3903923640231835523504477 1463971365086938321314179)
  ·
    refine ⟨2195957047630407481971269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1463971365086938321314179 2195957047630407481971269)
    ·
      refine ⟨411741946430701402869613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2195957047630407481971269 411741946430701402869613)
      ·
        refine ⟨154403229911513026076105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 411741946430701402869613 154403229911513026076105)
        ·
          refine ⟨115802422433634769557079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154403229911513026076105 115802422433634769557079)
          ·
            refine ⟨173703633650452154335619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115802422433634769557079 173703633650452154335619)
            ·
              refine ⟨260555450475678231503429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173703633650452154335619 260555450475678231503429)
              ·
                refine ⟨48854146964189668406893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 260555450475678231503429 48854146964189668406893)
                ·
                  rfl

theorem cell19_160554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 4].length) (baseStart_160554 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_160554 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_160554 prefixEnd_160554 := by exact prefixLift 160554
  have htrace : WordTrace (prefixWord ++ tailWord_160554) baseStart_160554 baseEnd_160554 := by
    simpa [prefixWord, tailWord_160554, baseEnd_160554] using wordTrace_append hprefix tailTrace_160554
  have hstable : (prefixWord ++ tailWord_160554).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160554).length < 2 ^ (prefixWord ++ tailWord_160554).sum := by decide
  have hdescent : baseEnd_160554 < baseStart_160554 := by decide
  rcases family_descends (prefixWord ++ tailWord_160554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160558 : List Nat := [4, 1, 3, 2, 1, 1, 3, 4]
def baseStart_160558 : Nat := 118140960795 + 160558 * 2 ^ 59
def prefixEnd_160558 : Nat := 4983230072969 + 3 ^ 40 * 160558 * 2
def baseEnd_160558 : Nat := 48855364103518844317993

theorem tailTrace_160558 : CollatzResearch.WordTrace tailWord_160558 prefixEnd_160558 48855364103518844317993 := by
  unfold tailWord_160558
  simp only [CollatzResearch.WordTrace]
  refine ⟨732003919041657746050291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3904020901555507978934885 732003919041657746050291)
  ·
    refine ⟨1098005878562486619075437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 732003919041657746050291 1098005878562486619075437)
    ·
      refine ⟨411752204460932482153289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1098005878562486619075437 411752204460932482153289)
      ·
        refine ⟨308814153345699361614967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 411752204460932482153289 308814153345699361614967)
        ·
          refine ⟨463221230018549042422451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308814153345699361614967 463221230018549042422451)
          ·
            refine ⟨694831845027823563633677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 463221230018549042422451 694831845027823563633677)
            ·
              refine ⟨260561941885433836362629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 694831845027823563633677 260561941885433836362629)
              ·
                refine ⟨48855364103518844317993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 260561941885433836362629 48855364103518844317993)
                ·
                  rfl

theorem cell19_160558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_160558 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_160558 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_160558 prefixEnd_160558 := by exact prefixLift 160558
  have htrace : WordTrace (prefixWord ++ tailWord_160558) baseStart_160558 baseEnd_160558 := by
    simpa [prefixWord, tailWord_160558, baseEnd_160558] using wordTrace_append hprefix tailTrace_160558
  have hstable : (prefixWord ++ tailWord_160558).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160558).length < 2 ^ (prefixWord ++ tailWord_160558).sum := by decide
  have hdescent : baseEnd_160558 < baseStart_160558 := by decide
  rcases family_descends (prefixWord ++ tailWord_160558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160579 : List Nat := [1, 1, 1, 3, 1, 4, 5, 3]
def baseStart_160579 : Nat := 118140960795 + 160579 * 2 ^ 59
def prefixEnd_160579 : Nat := 4983230072969 + 3 ^ 40 * 160579 * 2
def baseEnd_160579 : Nat := 48861754084997017851269

theorem tailTrace_160579 : CollatzResearch.WordTrace tailWord_160579 prefixEnd_160579 48861754084997017851269 := by
  unfold tailWord_160579
  simp only [CollatzResearch.WordTrace]
  refine ⟨5856797285257182554916791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3904531523504788369944527 5856797285257182554916791)
  ·
    refine ⟨8785195927885773832375187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5856797285257182554916791 8785195927885773832375187)
    ·
      refine ⟨13177793891828660748562781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8785195927885773832375187 13177793891828660748562781)
      ·
        refine ⟨4941672709435747780711043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13177793891828660748562781 4941672709435747780711043)
        ·
          refine ⟨7412509064153621671066565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4941672709435747780711043 7412509064153621671066565)
          ·
            refine ⟨1389845449528804063324981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7412509064153621671066565 1389845449528804063324981)
            ·
              refine ⟨130298010893325380936717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1389845449528804063324981 130298010893325380936717)
              ·
                refine ⟨48861754084997017851269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130298010893325380936717 48861754084997017851269)
                ·
                  rfl

theorem cell19_160579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 3].length) (baseStart_160579 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_160579 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_160579 prefixEnd_160579 := by exact prefixLift 160579
  have htrace : WordTrace (prefixWord ++ tailWord_160579) baseStart_160579 baseEnd_160579 := by
    simpa [prefixWord, tailWord_160579, baseEnd_160579] using wordTrace_append hprefix tailTrace_160579
  have hstable : (prefixWord ++ tailWord_160579).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160579).length < 2 ^ (prefixWord ++ tailWord_160579).sum := by decide
  have hdescent : baseEnd_160579 < baseStart_160579 := by decide
  rcases family_descends (prefixWord ++ tailWord_160579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160674 : List Nat := [3, 3, 1, 2, 2, 1, 1, 6]
def baseStart_160674 : Nat := 118140960795 + 160674 * 2 ^ 59
def prefixEnd_160674 : Nat := 4983230072969 + 3 ^ 40 * 160674 * 2
def baseEnd_160674 : Nat := 48890661144064945739899

theorem tailTrace_160674 : CollatzResearch.WordTrace tailWord_160674 prefixEnd_160674 48890661144064945739899 := by
  unfold tailWord_160674
  simp only [CollatzResearch.WordTrace]
  refine ⟨1465065554978253444906269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3906841479942009186416717 1465065554978253444906269)
  ·
    refine ⟨549399583116845041839851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1465065554978253444906269 549399583116845041839851)
    ·
      refine ⟨824099374675267562759777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 549399583116845041839851 824099374675267562759777)
      ·
        refine ⟨618074531006450672069833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 824099374675267562759777 618074531006450672069833)
        ·
          refine ⟨463555898254838004052375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 618074531006450672069833 463555898254838004052375)
          ·
            refine ⟨695333847382257006078563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 463555898254838004052375 695333847382257006078563)
            ·
              refine ⟨1043000771073385509117845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 695333847382257006078563 1043000771073385509117845)
              ·
                refine ⟨48890661144064945739899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1043000771073385509117845 48890661144064945739899)
                ·
                  rfl

theorem cell19_160674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_160674 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_160674 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_160674 prefixEnd_160674 := by exact prefixLift 160674
  have htrace : WordTrace (prefixWord ++ tailWord_160674) baseStart_160674 baseEnd_160674 := by
    simpa [prefixWord, tailWord_160674, baseEnd_160674] using wordTrace_append hprefix tailTrace_160674
  have hstable : (prefixWord ++ tailWord_160674).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160674).length < 2 ^ (prefixWord ++ tailWord_160674).sum := by decide
  have hdescent : baseEnd_160674 < baseStart_160674 := by decide
  rcases family_descends (prefixWord ++ tailWord_160674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160695 : List Nat := [1, 1, 3, 1, 3, 1, 4, 5]
def baseStart_160695 : Nat := 118140960795 + 160695 * 2 ^ 59
def prefixEnd_160695 : Nat := 4983230072969 + 3 ^ 40 * 160695 * 2
def baseEnd_160695 : Nat := 48897051125543119273175

theorem tailTrace_160695 : CollatzResearch.WordTrace tailWord_160695 prefixEnd_160695 48897051125543119273175 := by
  unfold tailWord_160695
  simp only [CollatzResearch.WordTrace]
  refine ⟨5861028152836934366139539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3907352101891289577426359 5861028152836934366139539)
  ·
    refine ⟨8791542229255401549209309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5861028152836934366139539 8791542229255401549209309)
    ·
      refine ⟨3296828335970775580953491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8791542229255401549209309 3296828335970775580953491)
      ·
        refine ⟨4945242503956163371430237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3296828335970775580953491 4945242503956163371430237)
        ·
          refine ⟨1854465938983561264286339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4945242503956163371430237 1854465938983561264286339)
          ·
            refine ⟨2781698908475341896429509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1854465938983561264286339 2781698908475341896429509)
            ·
              refine ⟨521568545339126605580533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2781698908475341896429509 521568545339126605580533)
              ·
                refine ⟨48897051125543119273175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 521568545339126605580533 48897051125543119273175)
                ·
                  rfl

theorem cell19_160695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 5].length) (baseStart_160695 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_160695 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_160695 prefixEnd_160695 := by exact prefixLift 160695
  have htrace : WordTrace (prefixWord ++ tailWord_160695) baseStart_160695 baseEnd_160695 := by
    simpa [prefixWord, tailWord_160695, baseEnd_160695] using wordTrace_append hprefix tailTrace_160695
  have hstable : (prefixWord ++ tailWord_160695).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160695).length < 2 ^ (prefixWord ++ tailWord_160695).sum := by decide
  have hdescent : baseEnd_160695 < baseStart_160695 := by decide
  rcases family_descends (prefixWord ++ tailWord_160695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160712 : List Nat := [2, 1, 3, 1, 6, 6]
def baseStart_160712 : Nat := 118140960795 + 160712 * 2 ^ 59
def prefixEnd_160712 : Nat := 4983230072969 + 3 ^ 40 * 160712 * 2
def baseEnd_160712 : Nat := 5433580440854679655039

theorem tailTrace_160712 : CollatzResearch.WordTrace tailWord_160712 prefixEnd_160712 5433580440854679655039 := by
  unfold tailWord_160712
  simp only [CollatzResearch.WordTrace]
  refine ⟨2930824096887673134754195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3907765462516897513005593 2930824096887673134754195)
  ·
    refine ⟨4396236145331509702131293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2930824096887673134754195 4396236145331509702131293)
    ·
      refine ⟨1648588554499316138299235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4396236145331509702131293 1648588554499316138299235)
      ·
        refine ⟨2472882831748974207448853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1648588554499316138299235 2472882831748974207448853)
        ·
          refine ⟨115916382738233165974165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2472882831748974207448853 115916382738233165974165)
          ·
            refine ⟨5433580440854679655039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 115916382738233165974165 5433580440854679655039)
            ·
              rfl

theorem cell19_160712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 6].length) (baseStart_160712 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_160712 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_160712 prefixEnd_160712 := by exact prefixLift 160712
  have htrace : WordTrace (prefixWord ++ tailWord_160712) baseStart_160712 baseEnd_160712 := by
    simpa [prefixWord, tailWord_160712, baseEnd_160712] using wordTrace_append hprefix tailTrace_160712
  have hstable : (prefixWord ++ tailWord_160712).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160712).length < 2 ^ (prefixWord ++ tailWord_160712).sum := by decide
  have hdescent : baseEnd_160712 < baseStart_160712 := by decide
  rcases family_descends (prefixWord ++ tailWord_160712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160828 : List Nat := [2, 2, 2, 2, 2, 2, 7]
def baseStart_160828 : Nat := 118140960795 + 160828 * 2 ^ 59
def prefixEnd_160828 : Nat := 4983230072969 + 3 ^ 40 * 160828 * 2
def baseEnd_160828 : Nat := 16312507002746072772419

theorem tailTrace_160828 : CollatzResearch.WordTrace tailWord_160828 prefixEnd_160828 16312507002746072772419 := by
  unfold tailWord_160828
  simp only [CollatzResearch.WordTrace]
  refine ⟨2932939530677549040365569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3910586040903398720487425 2932939530677549040365569)
  ·
    refine ⟨2199704648008161780274177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2932939530677549040365569 2199704648008161780274177)
    ·
      refine ⟨1649778486006121335205633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2199704648008161780274177 1649778486006121335205633)
      ·
        refine ⟨1237333864504591001404225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1649778486006121335205633 1237333864504591001404225)
        ·
          refine ⟨928000398378443251053169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1237333864504591001404225 928000398378443251053169)
          ·
            refine ⟨696000298783832438289877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 928000398378443251053169 696000298783832438289877)
            ·
              refine ⟨16312507002746072772419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 696000298783832438289877 16312507002746072772419)
              ·
                rfl

theorem cell19_160828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 7].length) (baseStart_160828 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_160828 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_160828 prefixEnd_160828 := by exact prefixLift 160828
  have htrace : WordTrace (prefixWord ++ tailWord_160828) baseStart_160828 baseEnd_160828 := by
    simpa [prefixWord, tailWord_160828, baseEnd_160828] using wordTrace_append hprefix tailTrace_160828
  have hstable : (prefixWord ++ tailWord_160828).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160828).length < 2 ^ (prefixWord ++ tailWord_160828).sum := by decide
  have hdescent : baseEnd_160828 < baseStart_160828 := by decide
  rcases family_descends (prefixWord ++ tailWord_160828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160845 : List Nat := [1, 6, 1, 1, 1, 2, 1, 6]
def baseStart_160845 : Nat := 118140960795 + 160845 * 2 ^ 59
def prefixEnd_160845 : Nat := 4983230072969 + 3 ^ 40 * 160845 * 2
def baseEnd_160845 : Nat := 48942693850387215939433

theorem tailTrace_160845 : CollatzResearch.WordTrace tailWord_160845 prefixEnd_160845 48942693850387215939433 := by
  unfold tailWord_160845
  simp only [CollatzResearch.WordTrace]
  refine ⟨5866499102293509984099989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3910999401529006656066659 5866499102293509984099989)
  ·
    refine ⟨274992145420008280504687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5866499102293509984099989 274992145420008280504687)
    ·
      refine ⟨412488218130012420757031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274992145420008280504687 412488218130012420757031)
      ·
        refine ⟨618732327195018631135547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412488218130012420757031 618732327195018631135547)
        ·
          refine ⟨928098490792527946703321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 618732327195018631135547 928098490792527946703321)
          ·
            refine ⟨696073868094395960027491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 928098490792527946703321 696073868094395960027491)
            ·
              refine ⟨1044110802141593940041237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 696073868094395960027491 1044110802141593940041237)
              ·
                refine ⟨48942693850387215939433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1044110802141593940041237 48942693850387215939433)
                ·
                  rfl

theorem cell19_160845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 6].length) (baseStart_160845 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_160845 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_160845 prefixEnd_160845 := by exact prefixLift 160845
  have htrace : WordTrace (prefixWord ++ tailWord_160845) baseStart_160845 baseEnd_160845 := by
    simpa [prefixWord, tailWord_160845, baseEnd_160845] using wordTrace_append hprefix tailTrace_160845
  have hstable : (prefixWord ++ tailWord_160845).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160845).length < 2 ^ (prefixWord ++ tailWord_160845).sum := by decide
  have hdescent : baseEnd_160845 < baseStart_160845 := by decide
  rcases family_descends (prefixWord ++ tailWord_160845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160894 : List Nat := [4, 2, 4, 1, 2, 1, 1, 4]
def baseStart_160894 : Nat := 118140960795 + 160894 * 2 ^ 59
def prefixEnd_160894 : Nat := 4983230072969 + 3 ^ 40 * 160894 * 2
def baseEnd_160894 : Nat := 48957603807169620850411

theorem tailTrace_160894 : CollatzResearch.WordTrace tailWord_160894 prefixEnd_160894 48957603807169620850411 := by
  unfold tailWord_160894
  simp only [CollatzResearch.WordTrace]
  refine ⟨733535784889498919079217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3912190852743994235089157 733535784889498919079217)
  ·
    refine ⟨550151838667124189309413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 733535784889498919079217 550151838667124189309413)
    ·
      refine ⟨103153469750085785495515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 550151838667124189309413 103153469750085785495515)
      ·
        refine ⟨154730204625128678243273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103153469750085785495515 154730204625128678243273)
        ·
          refine ⟨116047653468846508682455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154730204625128678243273 116047653468846508682455)
          ·
            refine ⟨174071480203269763023683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116047653468846508682455 174071480203269763023683)
            ·
              refine ⟨261107220304904644535525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174071480203269763023683 261107220304904644535525)
              ·
                refine ⟨48957603807169620850411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 261107220304904644535525 48957603807169620850411)
                ·
                  rfl

theorem cell19_160894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_160894 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_160894 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_160894 prefixEnd_160894 := by exact prefixLift 160894
  have htrace : WordTrace (prefixWord ++ tailWord_160894) baseStart_160894 baseEnd_160894 := by
    simpa [prefixWord, tailWord_160894, baseEnd_160894] using wordTrace_append hprefix tailTrace_160894
  have hstable : (prefixWord ++ tailWord_160894).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160894).length < 2 ^ (prefixWord ++ tailWord_160894).sum := by decide
  have hdescent : baseEnd_160894 < baseStart_160894 := by decide
  rcases family_descends (prefixWord ++ tailWord_160894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160974 : List Nat := [4, 1, 1, 1, 6, 1, 2, 3]
def baseStart_160974 : Nat := 118140960795 + 160974 * 2 ^ 59
def prefixEnd_160974 : Nat := 4983230072969 + 3 ^ 40 * 160974 * 2
def baseEnd_160974 : Nat := 48981946593753139072415

theorem tailTrace_160974 : CollatzResearch.WordTrace tailWord_160974 prefixEnd_160974 48981946593753139072415 := by
  unfold tailWord_160974
  simp only [CollatzResearch.WordTrace]
  refine ⟨733900514853270626943247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3914136079217443343697317 733900514853270626943247)
  ·
    refine ⟨1100850772279905940414871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 733900514853270626943247 1100850772279905940414871)
    ·
      refine ⟨1651276158419858910622307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1100850772279905940414871 1651276158419858910622307)
      ·
        refine ⟨2476914237629788365933461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1651276158419858910622307 2476914237629788365933461)
        ·
          refine ⟨116105354888896329653131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2476914237629788365933461 116105354888896329653131)
          ·
            refine ⟨174158032333344494479697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116105354888896329653131 174158032333344494479697)
            ·
              refine ⟨130618524250008370859773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174158032333344494479697 130618524250008370859773)
              ·
                refine ⟨48981946593753139072415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130618524250008370859773 48981946593753139072415)
                ·
                  rfl

theorem cell19_160974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_160974 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_160974 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_160974 prefixEnd_160974 := by exact prefixLift 160974
  have htrace : WordTrace (prefixWord ++ tailWord_160974) baseStart_160974 baseEnd_160974 := by
    simpa [prefixWord, tailWord_160974, baseEnd_160974] using wordTrace_append hprefix tailTrace_160974
  have hstable : (prefixWord ++ tailWord_160974).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160974).length < 2 ^ (prefixWord ++ tailWord_160974).sum := by decide
  have hdescent : baseEnd_160974 < baseStart_160974 := by decide
  rcases family_descends (prefixWord ++ tailWord_160974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160997 : List Nat := [1, 3, 1, 4, 3, 2, 5]
def baseStart_160997 : Nat := 118140960795 + 160997 * 2 ^ 59
def prefixEnd_160997 : Nat := 4983230072969 + 3 ^ 40 * 160997 * 2
def baseEnd_160997 : Nat := 16329648381631966853747

theorem tailTrace_160997 : CollatzResearch.WordTrace tailWord_160997 prefixEnd_160997 16329648381631966853747 := by
  unfold tailWord_160997
  simp only [CollatzResearch.WordTrace]
  refine ⟨5872042997742839943633245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3914695331828559962422163 5872042997742839943633245)
  ·
    refine ⟨2202016124153564978862467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5872042997742839943633245 2202016124153564978862467)
    ·
      refine ⟨3303024186230347468293701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2202016124153564978862467 3303024186230347468293701)
      ·
        refine ⟨619317034918190150305069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3303024186230347468293701 619317034918190150305069)
        ·
          refine ⟨232243888094321306364401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 619317034918190150305069 232243888094321306364401)
          ·
            refine ⟨174182916070740979773301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232243888094321306364401 174182916070740979773301)
            ·
              refine ⟨16329648381631966853747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 174182916070740979773301 16329648381631966853747)
              ·
                rfl

theorem cell19_160997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 5].length) (baseStart_160997 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_160997 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_160997 prefixEnd_160997 := by exact prefixLift 160997
  have htrace : WordTrace (prefixWord ++ tailWord_160997) baseStart_160997 baseEnd_160997 := by
    simpa [prefixWord, tailWord_160997, baseEnd_160997] using wordTrace_append hprefix tailTrace_160997
  have hstable : (prefixWord ++ tailWord_160997).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160997).length < 2 ^ (prefixWord ++ tailWord_160997).sum := by decide
  have hdescent : baseEnd_160997 < baseStart_160997 := by decide
  rcases family_descends (prefixWord ++ tailWord_160997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161018 : List Nat := [3, 1, 1, 1, 1, 4, 4, 4]
def baseStart_161018 : Nat := 118140960795 + 161018 * 2 ^ 59
def prefixEnd_161018 : Nat := 4983230072969 + 3 ^ 40 * 161018 * 2
def baseEnd_161018 : Nat := 48995335126374074094517

theorem tailTrace_161018 : CollatzResearch.WordTrace tailWord_161018 prefixEnd_161018 48995335126374074094517 := by
  unfold tailWord_161018
  simp only [CollatzResearch.WordTrace]
  refine ⟨1468202232666690132536927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3915205953777840353431805 1468202232666690132536927)
  ·
    refine ⟨2202303349000035198805391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1468202232666690132536927 2202303349000035198805391)
    ·
      refine ⟨3303455023500052798208087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2202303349000035198805391 3303455023500052798208087)
      ·
        refine ⟨4955182535250079197312131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3303455023500052798208087 4955182535250079197312131)
        ·
          refine ⟨7432773802875118795968197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4955182535250079197312131 7432773802875118795968197)
          ·
            refine ⟨1393645088039084774244037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7432773802875118795968197 1393645088039084774244037)
            ·
              refine ⟨261308454007328395170757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1393645088039084774244037 261308454007328395170757)
              ·
                refine ⟨48995335126374074094517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 261308454007328395170757 48995335126374074094517)
                ·
                  rfl

theorem cell19_161018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_161018 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_161018 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_161018 prefixEnd_161018 := by exact prefixLift 161018
  have htrace : WordTrace (prefixWord ++ tailWord_161018) baseStart_161018 baseEnd_161018 := by
    simpa [prefixWord, tailWord_161018, baseEnd_161018] using wordTrace_append hprefix tailTrace_161018
  have hstable : (prefixWord ++ tailWord_161018).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161018).length < 2 ^ (prefixWord ++ tailWord_161018).sum := by decide
  have hdescent : baseEnd_161018 < baseStart_161018 := by decide
  rcases family_descends (prefixWord ++ tailWord_161018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161054 : List Nat := [4, 3, 2, 1, 9]
def baseStart_161054 : Nat := 118140960795 + 161054 * 2 ^ 59
def prefixEnd_161054 : Nat := 4983230072969 + 3 ^ 40 * 161054 * 2
def baseEnd_161054 : Nat := 1815047754827283603497

theorem tailTrace_161054 : CollatzResearch.WordTrace tailWord_161054 prefixEnd_161054 1815047754827283603497 := by
  unfold tailWord_161054
  simp only [CollatzResearch.WordTrace]
  refine ⟨734265244817042334807277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3916081305690892452305477 734265244817042334807277)
  ·
    refine ⟨275349466806390875552729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 734265244817042334807277 275349466806390875552729)
    ·
      refine ⟨206512100104793156664547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275349466806390875552729 206512100104793156664547)
      ·
        refine ⟨309768150157189734996821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206512100104793156664547 309768150157189734996821)
        ·
          refine ⟨1815047754827283603497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 309768150157189734996821 1815047754827283603497)
          ·
            rfl

theorem cell19_161054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 9].length) (baseStart_161054 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_161054 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_161054 prefixEnd_161054 := by exact prefixLift 161054
  have htrace : WordTrace (prefixWord ++ tailWord_161054) baseStart_161054 baseEnd_161054 := by
    simpa [prefixWord, tailWord_161054, baseEnd_161054] using wordTrace_append hprefix tailTrace_161054
  have hstable : (prefixWord ++ tailWord_161054).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161054).length < 2 ^ (prefixWord ++ tailWord_161054).sum := by decide
  have hdescent : baseEnd_161054 < baseStart_161054 := by decide
  rcases family_descends (prefixWord ++ tailWord_161054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
