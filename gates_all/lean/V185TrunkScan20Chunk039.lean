import V185TrunkScan20Chunk038

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_237365 : List Nat := [1, 3, 3, 1, 5, 1, 1, 5]
def baseStart_237365 : Nat := 118140960795 + 237365 * 2 ^ 59
def prefixEnd_237365 : Nat := 4983230072969 + 3 ^ 40 * 237365 * 2
def baseEnd_237365 : Nat := 36113284608761197643225

theorem tailTrace_237365 : CollatzResearch.WordTrace tailWord_237365 prefixEnd_237365 36113284608761197643225 := by
  unfold tailWord_237365
  simp only [CollatzResearch.WordTrace]
  refine ⟨8657412785074618559657549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5771608523383079039771699 8657412785074618559657549)
  ·
    refine ⟨3246529794402981959871581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8657412785074618559657549 3246529794402981959871581)
    ·
      refine ⟨1217448672901118234951843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3246529794402981959871581 1217448672901118234951843)
      ·
        refine ⟨1826173009351677352427765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1217448672901118234951843 1826173009351677352427765)
        ·
          refine ⟨171203719626719751790103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1826173009351677352427765 171203719626719751790103)
          ·
            refine ⟨256805579440079627685155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171203719626719751790103 256805579440079627685155)
            ·
              refine ⟨385208369160119441527733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256805579440079627685155 385208369160119441527733)
              ·
                refine ⟨36113284608761197643225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 385208369160119441527733 36113284608761197643225)
                ·
                  rfl

theorem cell20_237365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 5].length) (baseStart_237365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237365 prefixEnd_237365 := by exact prefixLift 237365
  have htrace : WordTrace (prefixWord ++ tailWord_237365) baseStart_237365 baseEnd_237365 := by
    simpa [prefixWord, tailWord_237365, baseEnd_237365] using wordTrace_append hprefix tailTrace_237365
  have hstable : (prefixWord ++ tailWord_237365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237365).length < 2 ^ (prefixWord ++ tailWord_237365).sum := by decide
  have hdescent : baseEnd_237365 < baseStart_237365 := by decide
  rcases family_descends (prefixWord ++ tailWord_237365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237382 : List Nat := [6, 1, 1, 2, 1, 2, 3, 4]
def baseStart_237382 : Nat := 118140960795 + 237382 * 2 ^ 59
def prefixEnd_237382 : Nat := 4983230072969 + 3 ^ 40 * 237382 * 2
def baseEnd_237382 : Nat := 36115871029835696454313

theorem tailTrace_237382 : CollatzResearch.WordTrace tailWord_237382 prefixEnd_237382 36115871029835696454313 := by
  unfold tailWord_237382
  simp only [CollatzResearch.WordTrace]
  refine ⟨270563525812907201969575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5772021884008686975350933 270563525812907201969575)
  ·
    refine ⟨405845288719360802954363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270563525812907201969575 405845288719360802954363)
    ·
      refine ⟨608767933079041204431545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405845288719360802954363 608767933079041204431545)
      ·
        refine ⟨456575949809280903323659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 608767933079041204431545 456575949809280903323659)
        ·
          refine ⟨684863924713921354985489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456575949809280903323659 684863924713921354985489)
          ·
            refine ⟨513647943535441016239117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 684863924713921354985489 513647943535441016239117)
            ·
              refine ⟨192617978825790381089669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 513647943535441016239117 192617978825790381089669)
              ·
                refine ⟨36115871029835696454313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 192617978825790381089669 36115871029835696454313)
                ·
                  rfl

theorem cell20_237382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_237382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237382 prefixEnd_237382 := by exact prefixLift 237382
  have htrace : WordTrace (prefixWord ++ tailWord_237382) baseStart_237382 baseEnd_237382 := by
    simpa [prefixWord, tailWord_237382, baseEnd_237382] using wordTrace_append hprefix tailTrace_237382
  have hstable : (prefixWord ++ tailWord_237382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237382).length < 2 ^ (prefixWord ++ tailWord_237382).sum := by decide
  have hdescent : baseEnd_237382 < baseStart_237382 := by decide
  rcases family_descends (prefixWord ++ tailWord_237382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237383 : List Nat := [1, 1, 4, 1, 2, 1, 3, 1, 6]
def baseStart_237383 : Nat := 118140960795 + 237383 * 2 ^ 59
def prefixEnd_237383 : Nat := 4983230072969 + 3 ^ 40 * 237383 * 2
def baseEnd_237383 : Nat := 108348069516755530329601

theorem tailTrace_237383 : CollatzResearch.WordTrace tailWord_237383 prefixEnd_237383 108348069516755530329601 := by
  unfold tailWord_237383
  simp only [CollatzResearch.WordTrace]
  refine ⟨8658069299009407633812803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5772046199339605089208535 8658069299009407633812803)
  ·
    refine ⟨12987103948514111450719205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8658069299009407633812803 12987103948514111450719205)
    ·
      refine ⟨2435081990346395897009851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12987103948514111450719205 2435081990346395897009851)
      ·
        refine ⟨3652622985519593845514777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2435081990346395897009851 3652622985519593845514777)
        ·
          refine ⟨2739467239139695384136083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3652622985519593845514777 2739467239139695384136083)
          ·
            refine ⟨4109200858709543076204125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2739467239139695384136083 4109200858709543076204125)
            ·
              refine ⟨1540950322016078653576547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4109200858709543076204125 1540950322016078653576547)
              ·
                refine ⟨2311425483024117980364821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1540950322016078653576547 2311425483024117980364821)
                ·
                  refine ⟨108348069516755530329601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2311425483024117980364821 108348069516755530329601)
                  ·
                    rfl

theorem cell20_237383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 6].length) (baseStart_237383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237383 prefixEnd_237383 := by exact prefixLift 237383
  have htrace : WordTrace (prefixWord ++ tailWord_237383) baseStart_237383 baseEnd_237383 := by
    simpa [prefixWord, tailWord_237383, baseEnd_237383] using wordTrace_append hprefix tailTrace_237383
  have hstable : (prefixWord ++ tailWord_237383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237383).length < 2 ^ (prefixWord ++ tailWord_237383).sum := by decide
  have hdescent : baseEnd_237383 < baseStart_237383 := by decide
  rcases family_descends (prefixWord ++ tailWord_237383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237396 : List Nat := [2, 4, 1, 1, 3, 2, 2, 3, 2]
def baseStart_237396 : Nat := 118140960795 + 237396 * 2 ^ 59
def prefixEnd_237396 : Nat := 4983230072969 + 3 ^ 40 * 237396 * 2
def baseEnd_237396 : Nat := 108354003070985262896215

theorem tailTrace_237396 : CollatzResearch.WordTrace tailWord_237396 prefixEnd_237396 108354003070985262896215 := by
  unfold tailWord_237396
  simp only [CollatzResearch.WordTrace]
  refine ⟨4329271723981155427018021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5772362298641540569357361 4329271723981155427018021)
  ·
    refine ⟨811738448246466642565879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4329271723981155427018021 811738448246466642565879)
    ·
      refine ⟨1217607672369699963848819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 811738448246466642565879 1217607672369699963848819)
      ·
        refine ⟨1826411508554549945773229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1217607672369699963848819 1826411508554549945773229)
        ·
          refine ⟨684904315707956229664961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1826411508554549945773229 684904315707956229664961)
          ·
            refine ⟨513678236780967172248721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 684904315707956229664961 513678236780967172248721)
            ·
              refine ⟨385258677585725379186541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 513678236780967172248721 385258677585725379186541)
              ·
                refine ⟨144472004094647017194953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 385258677585725379186541 144472004094647017194953)
                ·
                  refine ⟨108354003070985262896215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144472004094647017194953 108354003070985262896215)
                  ·
                    rfl

theorem cell20_237396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_237396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237396 prefixEnd_237396 := by exact prefixLift 237396
  have htrace : WordTrace (prefixWord ++ tailWord_237396) baseStart_237396 baseEnd_237396 := by
    simpa [prefixWord, tailWord_237396, baseEnd_237396] using wordTrace_append hprefix tailTrace_237396
  have hstable : (prefixWord ++ tailWord_237396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237396).length < 2 ^ (prefixWord ++ tailWord_237396).sum := by decide
  have hdescent : baseEnd_237396 < baseStart_237396 := by decide
  rcases family_descends (prefixWord ++ tailWord_237396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237410 : List Nat := [3, 3, 2, 1, 2, 1, 3, 2, 3]
def baseStart_237410 : Nat := 118140960795 + 237410 * 2 ^ 59
def prefixEnd_237410 : Nat := 4983230072969 + 3 ^ 40 * 237410 * 2
def baseEnd_237410 : Nat := 108360393052463436429491

theorem tailTrace_237410 : CollatzResearch.WordTrace tailWord_237410 prefixEnd_237410 108360393052463436429491 := by
  unfold tailWord_237410
  simp only [CollatzResearch.WordTrace]
  refine ⟨2164763517477897811261421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5772702713274394163363789 2164763517477897811261421)
  ·
    refine ⟨811786319054211679223033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2164763517477897811261421 811786319054211679223033)
    ·
      refine ⟨608839739290658759417275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 811786319054211679223033 608839739290658759417275)
      ·
        refine ⟨913259608935988139125913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 608839739290658759417275 913259608935988139125913)
        ·
          refine ⟨684944706701991104344435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 913259608935988139125913 684944706701991104344435)
          ·
            refine ⟨1027417060052986656516653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 684944706701991104344435 1027417060052986656516653)
            ·
              refine ⟨385281397519869996193745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1027417060052986656516653 385281397519869996193745)
              ·
                refine ⟨288961048139902497145309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 385281397519869996193745 288961048139902497145309)
                ·
                  refine ⟨108360393052463436429491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 288961048139902497145309 108360393052463436429491)
                  ·
                    rfl

theorem cell20_237410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_237410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237410 prefixEnd_237410 := by exact prefixLift 237410
  have htrace : WordTrace (prefixWord ++ tailWord_237410) baseStart_237410 baseEnd_237410 := by
    simpa [prefixWord, tailWord_237410, baseEnd_237410] using wordTrace_append hprefix tailTrace_237410
  have hstable : (prefixWord ++ tailWord_237410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237410).length < 2 ^ (prefixWord ++ tailWord_237410).sum := by decide
  have hdescent : baseEnd_237410 < baseStart_237410 := by decide
  rcases family_descends (prefixWord ++ tailWord_237410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237476 : List Nat := [2, 3, 1, 2, 1, 3, 3, 1, 4]
def baseStart_237476 : Nat := 118140960795 + 237476 * 2 ^ 59
def prefixEnd_237476 : Nat := 4983230072969 + 3 ^ 40 * 237476 * 2
def baseEnd_237476 : Nat := 108390517250860540229221

theorem tailTrace_237476 : CollatzResearch.WordTrace tailWord_237476 prefixEnd_237476 108390517250860540229221 := by
  unfold tailWord_237476
  simp only [CollatzResearch.WordTrace]
  refine ⟨4330730643836242258474141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5774307525114989677965521 4330730643836242258474141)
  ·
    refine ⟨1624023991438590846927803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4330730643836242258474141 1624023991438590846927803)
    ·
      refine ⟨2436035987157886270391705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1624023991438590846927803 2436035987157886270391705)
      ·
        refine ⟨1827026990368414702793779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2436035987157886270391705 1827026990368414702793779)
        ·
          refine ⟨2740540485552622054190669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1827026990368414702793779 2740540485552622054190669)
          ·
            refine ⟨1027702682082233270321501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2740540485552622054190669 1027702682082233270321501)
            ·
              refine ⟨385388505780837476370563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1027702682082233270321501 385388505780837476370563)
              ·
                refine ⟨578082758671256214555845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385388505780837476370563 578082758671256214555845)
                ·
                  refine ⟨108390517250860540229221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 578082758671256214555845 108390517250860540229221)
                  ·
                    rfl

theorem cell20_237476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_237476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237476 prefixEnd_237476 := by exact prefixLift 237476
  have htrace : WordTrace (prefixWord ++ tailWord_237476) baseStart_237476 baseEnd_237476 := by
    simpa [prefixWord, tailWord_237476, baseEnd_237476] using wordTrace_append hprefix tailTrace_237476
  have hstable : (prefixWord ++ tailWord_237476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237476).length < 2 ^ (prefixWord ++ tailWord_237476).sum := by decide
  have hdescent : baseEnd_237476 < baseStart_237476 := by decide
  rcases family_descends (prefixWord ++ tailWord_237476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237497 : List Nat := [1, 2, 1, 4, 2, 1, 2, 1, 6]
def baseStart_237497 : Nat := 118140960795 + 237497 * 2 ^ 59
def prefixEnd_237497 : Nat := 4983230072969 + 3 ^ 40 * 237497 * 2
def baseEnd_237497 : Nat := 108400102223077800529135

theorem tailTrace_237497 : CollatzResearch.WordTrace tailWord_237497 prefixEnd_237497 108400102223077800529135 := by
  unfold tailWord_237497
  simp only [CollatzResearch.WordTrace]
  refine ⟨8662227220596405103462745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5774818147064270068975163 8662227220596405103462745)
  ·
    refine ⟨6496670415447303827597059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8662227220596405103462745 6496670415447303827597059)
    ·
      refine ⟨9745005623170955741395589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6496670415447303827597059 9745005623170955741395589)
      ·
        refine ⟨1827188554344554201511673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9745005623170955741395589 1827188554344554201511673)
        ·
          refine ⟨1370391415758415651133755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1827188554344554201511673 1370391415758415651133755)
          ·
            refine ⟨2055587123637623476700633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1370391415758415651133755 2055587123637623476700633)
            ·
              refine ⟨1541690342728217607525475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2055587123637623476700633 1541690342728217607525475)
              ·
                refine ⟨2312535514092326411288213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1541690342728217607525475 2312535514092326411288213)
                ·
                  refine ⟨108400102223077800529135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2312535514092326411288213 108400102223077800529135)
                  ·
                    rfl

theorem cell20_237497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_237497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237497 prefixEnd_237497 := by exact prefixLift 237497
  have htrace : WordTrace (prefixWord ++ tailWord_237497) baseStart_237497 baseEnd_237497 := by
    simpa [prefixWord, tailWord_237497, baseEnd_237497] using wordTrace_append hprefix tailTrace_237497
  have hstable : (prefixWord ++ tailWord_237497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237497).length < 2 ^ (prefixWord ++ tailWord_237497).sum := by decide
  have hdescent : baseEnd_237497 < baseStart_237497 := by decide
  rcases family_descends (prefixWord ++ tailWord_237497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237504 : List Nat := [2, 1, 1, 2, 3, 2, 1, 8]
def baseStart_237504 : Nat := 118140960795 + 237504 * 2 ^ 59
def prefixEnd_237504 : Nat := 4983230072969 + 3 ^ 40 * 237504 * 2
def baseEnd_237504 : Nat := 36134432404605629098591

theorem tailTrace_237504 : CollatzResearch.WordTrace tailWord_237504 prefixEnd_237504 36134432404605629098591 := by
  unfold tailWord_237504
  simp only [CollatzResearch.WordTrace]
  refine ⟨4331241265785522649483783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5774988354380696865978377 4331241265785522649483783)
  ·
    refine ⟨6496861898678283974225675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4331241265785522649483783 6496861898678283974225675)
    ·
      refine ⟨9745292848017425961338513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6496861898678283974225675 9745292848017425961338513)
      ·
        refine ⟨7308969636013069471003885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9745292848017425961338513 7308969636013069471003885)
        ·
          refine ⟨2740863613504901051626457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7308969636013069471003885 2740863613504901051626457)
          ·
            refine ⟨2055647710128675788719843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2740863613504901051626457 2055647710128675788719843)
            ·
              refine ⟨3083471565193013683079765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2055647710128675788719843 3083471565193013683079765)
              ·
                refine ⟨36134432404605629098591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3083471565193013683079765 36134432404605629098591)
                ·
                  rfl

theorem cell20_237504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 8].length) (baseStart_237504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237504 prefixEnd_237504 := by exact prefixLift 237504
  have htrace : WordTrace (prefixWord ++ tailWord_237504) baseStart_237504 baseEnd_237504 := by
    simpa [prefixWord, tailWord_237504, baseEnd_237504] using wordTrace_append hprefix tailTrace_237504
  have hstable : (prefixWord ++ tailWord_237504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237504).length < 2 ^ (prefixWord ++ tailWord_237504).sum := by decide
  have hdescent : baseEnd_237504 < baseStart_237504 := by decide
  rcases family_descends (prefixWord ++ tailWord_237504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237569 : List Nat := [1, 2, 4, 1, 2, 1, 4, 3, 2]
def baseStart_237569 : Nat := 118140960795 + 237569 * 2 ^ 59
def prefixEnd_237569 : Nat := 4983230072969 + 3 ^ 40 * 237569 * 2
def baseEnd_237569 : Nat := 108432964984965550128841

theorem tailTrace_237569 : CollatzResearch.WordTrace tailWord_237569 prefixEnd_237569 108432964984965550128841 := by
  unfold tailWord_237569
  simp only [CollatzResearch.WordTrace]
  refine ⟨8664853276335561400083761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5776568850890374266722507 8664853276335561400083761)
  ·
    refine ⟨6498639957251671050062821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8664853276335561400083761 6498639957251671050062821)
    ·
      refine ⟨1218494991984688321886779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6498639957251671050062821 1218494991984688321886779)
      ·
        refine ⟨1827742487977032482830169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1218494991984688321886779 1827742487977032482830169)
        ·
          refine ⟨1370806865982774362122627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1827742487977032482830169 1370806865982774362122627)
          ·
            refine ⟨2056210298974161543183941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1370806865982774362122627 2056210298974161543183941)
            ·
              refine ⟨385539431057655289346989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2056210298974161543183941 385539431057655289346989)
              ·
                refine ⟨144577286646620733505121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 385539431057655289346989 144577286646620733505121)
                ·
                  refine ⟨108432964984965550128841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144577286646620733505121 108432964984965550128841)
                  ·
                    rfl

theorem cell20_237569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 3, 2].length) (baseStart_237569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237569 prefixEnd_237569 := by exact prefixLift 237569
  have htrace : WordTrace (prefixWord ++ tailWord_237569) baseStart_237569 baseEnd_237569 := by
    simpa [prefixWord, tailWord_237569, baseEnd_237569] using wordTrace_append hprefix tailTrace_237569
  have hstable : (prefixWord ++ tailWord_237569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237569).length < 2 ^ (prefixWord ++ tailWord_237569).sum := by decide
  have hdescent : baseEnd_237569 < baseStart_237569 := by decide
  rcases family_descends (prefixWord ++ tailWord_237569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237580 : List Nat := [2, 2, 1, 2, 3, 1, 9]
def baseStart_237580 : Nat := 118140960795 + 237580 * 2 ^ 59
def prefixEnd_237580 : Nat := 4983230072969 + 3 ^ 40 * 237580 * 2
def baseEnd_237580 : Nat := 12048665076077600084681

theorem tailTrace_237580 : CollatzResearch.WordTrace tailWord_237580 prefixEnd_237580 12048665076077600084681 := by
  unfold tailWord_237580
  simp only [CollatzResearch.WordTrace]
  refine ⟨4332627239647855139367097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5776836319530473519156129 4332627239647855139367097)
  ·
    refine ⟨3249470429735891354525323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4332627239647855139367097 3249470429735891354525323)
    ·
      refine ⟨4874205644603837031787985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3249470429735891354525323 4874205644603837031787985)
      ·
        refine ⟨3655654233452877773840989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4874205644603837031787985 3655654233452877773840989)
        ·
          refine ⟨1370870337544829165190371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3655654233452877773840989 1370870337544829165190371)
          ·
            refine ⟨2056305506317243747785557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1370870337544829165190371 2056305506317243747785557)
            ·
              refine ⟨12048665076077600084681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2056305506317243747785557 12048665076077600084681)
              ·
                rfl

theorem cell20_237580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 9].length) (baseStart_237580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237580 prefixEnd_237580 := by exact prefixLift 237580
  have htrace : WordTrace (prefixWord ++ tailWord_237580) baseStart_237580 baseEnd_237580 := by
    simpa [prefixWord, tailWord_237580, baseEnd_237580] using wordTrace_append hprefix tailTrace_237580
  have hstable : (prefixWord ++ tailWord_237580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237580).length < 2 ^ (prefixWord ++ tailWord_237580).sum := by decide
  have hdescent : baseEnd_237580 < baseStart_237580 := by decide
  rcases family_descends (prefixWord ++ tailWord_237580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237614 : List Nat := [4, 1, 3, 1, 1, 2, 4, 4]
def baseStart_237614 : Nat := 118140960795 + 237614 * 2 ^ 59
def prefixEnd_237614 : Nat := 4983230072969 + 3 ^ 40 * 237614 * 2
def baseEnd_237614 : Nat := 36151168070381797876219

theorem tailTrace_237614 : CollatzResearch.WordTrace tailWord_237614 prefixEnd_237614 36151168070381797876219 := by
  unfold tailWord_237614
  simp only [CollatzResearch.WordTrace]
  refine ⟨1083311820146566760683987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5777663040781689390314597 1083311820146566760683987)
  ·
    refine ⟨1624967730219850141025981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1083311820146566760683987 1624967730219850141025981)
    ·
      refine ⟨609362898832443802884743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1624967730219850141025981 609362898832443802884743)
      ·
        refine ⟨914044348248665704327115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609362898832443802884743 914044348248665704327115)
        ·
          refine ⟨1371066522372998556490673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 914044348248665704327115 1371066522372998556490673)
          ·
            refine ⟨1028299891779748917368005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1371066522372998556490673 1028299891779748917368005)
            ·
              refine ⟨192806229708702922006501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1028299891779748917368005 192806229708702922006501)
              ·
                refine ⟨36151168070381797876219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 192806229708702922006501 36151168070381797876219)
                ·
                  rfl

theorem cell20_237614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_237614 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237614 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237614 prefixEnd_237614 := by exact prefixLift 237614
  have htrace : WordTrace (prefixWord ++ tailWord_237614) baseStart_237614 baseEnd_237614 := by
    simpa [prefixWord, tailWord_237614, baseEnd_237614] using wordTrace_append hprefix tailTrace_237614
  have hstable : (prefixWord ++ tailWord_237614).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237614).length < 2 ^ (prefixWord ++ tailWord_237614).sum := by decide
  have hdescent : baseEnd_237614 < baseStart_237614 := by decide
  rcases family_descends (prefixWord ++ tailWord_237614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237620 : List Nat := [2, 5, 1, 2, 3, 1, 1, 3, 2]
def baseStart_237620 : Nat := 118140960795 + 237620 * 2 ^ 59
def prefixEnd_237620 : Nat := 4983230072969 + 3 ^ 40 * 237620 * 2
def baseEnd_237620 : Nat := 108456242774636039428633

theorem tailTrace_237620 : CollatzResearch.WordTrace tailWord_237620 prefixEnd_237620 108456242774636039428633 := by
  unfold tailWord_237620
  simp only [CollatzResearch.WordTrace]
  refine ⟨4333356699575398555095157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5777808932767198073460209 4333356699575398555095157)
  ·
    refine ⟨406252190585193614540171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4333356699575398555095157 406252190585193614540171)
    ·
      refine ⟨609378285877790421810257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406252190585193614540171 609378285877790421810257)
      ·
        refine ⟨457033714408342816357693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 609378285877790421810257 457033714408342816357693)
        ·
          refine ⟨171387642903128556134135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 457033714408342816357693 171387642903128556134135)
          ·
            refine ⟨257081464354692834201203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171387642903128556134135 257081464354692834201203)
            ·
              refine ⟨385622196532039251301805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257081464354692834201203 385622196532039251301805)
              ·
                refine ⟨144608323699514719238177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 385622196532039251301805 144608323699514719238177)
                ·
                  refine ⟨108456242774636039428633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144608323699514719238177 108456242774636039428633)
                  ·
                    rfl

theorem cell20_237620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_237620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237620 prefixEnd_237620 := by exact prefixLift 237620
  have htrace : WordTrace (prefixWord ++ tailWord_237620) baseStart_237620 baseEnd_237620 := by
    simpa [prefixWord, tailWord_237620, baseEnd_237620] using wordTrace_append hprefix tailTrace_237620
  have hstable : (prefixWord ++ tailWord_237620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237620).length < 2 ^ (prefixWord ++ tailWord_237620).sum := by decide
  have hdescent : baseEnd_237620 < baseStart_237620 := by decide
  rcases family_descends (prefixWord ++ tailWord_237620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237624 : List Nat := [2, 1, 2, 1, 6, 2, 1, 3, 2]
def baseStart_237624 : Nat := 118140960795 + 237624 * 2 ^ 59
def prefixEnd_237624 : Nat := 4983230072969 + 3 ^ 40 * 237624 * 2
def baseEnd_237624 : Nat := 108458068483629803295283

theorem tailTrace_237624 : CollatzResearch.WordTrace tailWord_237624 prefixEnd_237624 108458068483629803295283 := by
  unfold tailWord_237624
  simp only [CollatzResearch.WordTrace]
  refine ⟨4333429645568152896667963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5777906194090870528890617 4333429645568152896667963)
  ·
    refine ⟨6500144468352229345001945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4333429645568152896667963 6500144468352229345001945)
    ·
      refine ⟨4875108351264172008751459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6500144468352229345001945 4875108351264172008751459)
      ·
        refine ⟨7312662526896258013127189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4875108351264172008751459 7312662526896258013127189)
        ·
          refine ⟨342781055948262094365337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7312662526896258013127189 342781055948262094365337)
          ·
            refine ⟨257085791961196570774003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342781055948262094365337 257085791961196570774003)
            ·
              refine ⟨385628687941794856161005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257085791961196570774003 385628687941794856161005)
              ·
                refine ⟨144610757978173071060377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 385628687941794856161005 144610757978173071060377)
                ·
                  refine ⟨108458068483629803295283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144610757978173071060377 108458068483629803295283)
                  ·
                    rfl

theorem cell20_237624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 3, 2].length) (baseStart_237624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237624 prefixEnd_237624 := by exact prefixLift 237624
  have htrace : WordTrace (prefixWord ++ tailWord_237624) baseStart_237624 baseEnd_237624 := by
    simpa [prefixWord, tailWord_237624, baseEnd_237624] using wordTrace_append hprefix tailTrace_237624
  have hstable : (prefixWord ++ tailWord_237624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237624).length < 2 ^ (prefixWord ++ tailWord_237624).sum := by decide
  have hdescent : baseEnd_237624 < baseStart_237624 := by decide
  rcases family_descends (prefixWord ++ tailWord_237624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237638 : List Nat := [6, 1, 1, 1, 1, 1, 2, 4, 3]
def baseStart_237638 : Nat := 118140960795 + 237638 * 2 ^ 59
def prefixEnd_237638 : Nat := 4983230072969 + 3 ^ 40 * 237638 * 2
def baseEnd_237638 : Nat := 108464458465107976828559

theorem tailTrace_237638 : CollatzResearch.WordTrace tailWord_237638 prefixEnd_237638 108464458465107976828559 := by
  unfold tailWord_237638
  simp only [CollatzResearch.WordTrace]
  refine ⟨270855309783924568260799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5778246608723724122897045 270855309783924568260799)
  ·
    refine ⟨406282964675886852391199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270855309783924568260799 406282964675886852391199)
    ·
      refine ⟨609424447013830278586799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406282964675886852391199 609424447013830278586799)
      ·
        refine ⟨914136670520745417880199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609424447013830278586799 914136670520745417880199)
        ·
          refine ⟨1371205005781118126820299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 914136670520745417880199 1371205005781118126820299)
          ·
            refine ⟨2056807508671677190230449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1371205005781118126820299 2056807508671677190230449)
            ·
              refine ⟨1542605631503757892672837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2056807508671677190230449 1542605631503757892672837)
              ·
                refine ⟨289238555906954604876157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1542605631503757892672837 289238555906954604876157)
                ·
                  refine ⟨108464458465107976828559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 289238555906954604876157 108464458465107976828559)
                  ·
                    rfl

theorem cell20_237638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_237638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237638 prefixEnd_237638 := by exact prefixLift 237638
  have htrace : WordTrace (prefixWord ++ tailWord_237638) baseStart_237638 baseEnd_237638 := by
    simpa [prefixWord, tailWord_237638, baseEnd_237638] using wordTrace_append hprefix tailTrace_237638
  have hstable : (prefixWord ++ tailWord_237638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237638).length < 2 ^ (prefixWord ++ tailWord_237638).sum := by decide
  have hdescent : baseEnd_237638 < baseStart_237638 := by decide
  rcases family_descends (prefixWord ++ tailWord_237638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237642 : List Nat := [3, 1, 2, 1, 1, 2, 1, 6, 3]
def baseStart_237642 : Nat := 118140960795 + 237642 * 2 ^ 59
def prefixEnd_237642 : Nat := 4983230072969 + 3 ^ 40 * 237642 * 2
def baseEnd_237642 : Nat := 108466284174101740695209

theorem tailTrace_237642 : CollatzResearch.WordTrace tailWord_237642 prefixEnd_237642 108466284174101740695209 := by
  unfold tailWord_237642
  simp only [CollatzResearch.WordTrace]
  refine ⟨2166878951267773716872795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5778343870047396578327453 2166878951267773716872795)
  ·
    refine ⟨3250318426901660575309193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2166878951267773716872795 3250318426901660575309193)
    ·
      refine ⟨2437738820176245431481895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3250318426901660575309193 2437738820176245431481895)
      ·
        refine ⟨3656608230264368147222843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2437738820176245431481895 3656608230264368147222843)
        ·
          refine ⟨5484912345396552220834265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3656608230264368147222843 5484912345396552220834265)
          ·
            refine ⟨4113684259047414165625699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5484912345396552220834265 4113684259047414165625699)
            ·
              refine ⟨6170526388571121248438549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4113684259047414165625699 6170526388571121248438549)
              ·
                refine ⟨289243424464271308520557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6170526388571121248438549 289243424464271308520557)
                ·
                  refine ⟨108466284174101740695209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 289243424464271308520557 108466284174101740695209)
                  ·
                    rfl

theorem cell20_237642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6, 3].length) (baseStart_237642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237642 prefixEnd_237642 := by exact prefixLift 237642
  have htrace : WordTrace (prefixWord ++ tailWord_237642) baseStart_237642 baseEnd_237642 := by
    simpa [prefixWord, tailWord_237642, baseEnd_237642] using wordTrace_append hprefix tailTrace_237642
  have hstable : (prefixWord ++ tailWord_237642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237642).length < 2 ^ (prefixWord ++ tailWord_237642).sum := by decide
  have hdescent : baseEnd_237642 < baseStart_237642 := by decide
  rcases family_descends (prefixWord ++ tailWord_237642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237656 : List Nat := [2, 1, 2, 2, 1, 4, 1, 7]
def baseStart_237656 : Nat := 118140960795 + 237656 * 2 ^ 59
def prefixEnd_237656 : Nat := 4983230072969 + 3 ^ 40 * 237656 * 2
def baseEnd_237656 : Nat := 36157558051859971409495

theorem tailTrace_237656 : CollatzResearch.WordTrace tailWord_237656 prefixEnd_237656 36157558051859971409495 := by
  unfold tailWord_237656
  simp only [CollatzResearch.WordTrace]
  refine ⟨4334013213510187629250411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5778684284680250172333881 4334013213510187629250411)
  ·
    refine ⟨6501019820265281443875617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4334013213510187629250411 6501019820265281443875617)
    ·
      refine ⟨4875764865198961082906713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6501019820265281443875617 4875764865198961082906713)
      ·
        refine ⟨3656823648899220812180035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4875764865198961082906713 3656823648899220812180035)
        ·
          refine ⟨5485235473348831218270053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3656823648899220812180035 5485235473348831218270053)
          ·
            refine ⟨1028481651252905853425635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5485235473348831218270053 1028481651252905853425635)
            ·
              refine ⟨1542722476879358780138453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1028481651252905853425635 1542722476879358780138453)
              ·
                refine ⟨36157558051859971409495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1542722476879358780138453 36157558051859971409495)
                ·
                  rfl

theorem cell20_237656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 7].length) (baseStart_237656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237656 prefixEnd_237656 := by exact prefixLift 237656
  have htrace : WordTrace (prefixWord ++ tailWord_237656) baseStart_237656 baseEnd_237656 := by
    simpa [prefixWord, tailWord_237656, baseEnd_237656] using wordTrace_append hprefix tailTrace_237656
  have hstable : (prefixWord ++ tailWord_237656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237656).length < 2 ^ (prefixWord ++ tailWord_237656).sum := by decide
  have hdescent : baseEnd_237656 < baseStart_237656 := by decide
  rcases family_descends (prefixWord ++ tailWord_237656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237663 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 7]
def baseStart_237663 : Nat := 118140960795 + 237663 * 2 ^ 59
def prefixEnd_237663 : Nat := 4983230072969 + 3 ^ 40 * 237663 * 2
def baseEnd_237663 : Nat := 108475869146319000995123

theorem tailTrace_237663 : CollatzResearch.WordTrace tailWord_237663 prefixEnd_237663 108475869146319000995123 := by
  unfold tailWord_237663
  simp only [CollatzResearch.WordTrace]
  refine ⟨8668281737995015454005643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5778854491996676969337095 8668281737995015454005643)
  ·
    refine ⟨13002422606992523181008465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8668281737995015454005643 13002422606992523181008465)
    ·
      refine ⟨9751816955244392385756349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13002422606992523181008465 9751816955244392385756349)
      ·
        refine ⟨3656931358216647144658631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9751816955244392385756349 3656931358216647144658631)
        ·
          refine ⟨5485397037324970716987947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3656931358216647144658631 5485397037324970716987947)
          ·
            refine ⟨8228095555987456075481921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5485397037324970716987947 8228095555987456075481921)
            ·
              refine ⟨6171071666990592056611441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8228095555987456075481921 6171071666990592056611441)
              ·
                refine ⟨4628303750242944042458581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6171071666990592056611441 4628303750242944042458581)
                ·
                  refine ⟨108475869146319000995123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4628303750242944042458581 108475869146319000995123)
                  ·
                    rfl

theorem cell20_237663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 7].length) (baseStart_237663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237663 prefixEnd_237663 := by exact prefixLift 237663
  have htrace : WordTrace (prefixWord ++ tailWord_237663) baseStart_237663 baseEnd_237663 := by
    simpa [prefixWord, tailWord_237663, baseEnd_237663] using wordTrace_append hprefix tailTrace_237663
  have hstable : (prefixWord ++ tailWord_237663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237663).length < 2 ^ (prefixWord ++ tailWord_237663).sum := by decide
  have hdescent : baseEnd_237663 < baseStart_237663 := by decide
  rcases family_descends (prefixWord ++ tailWord_237663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237725 : List Nat := [1, 4, 2, 1, 1, 3, 1, 1, 6]
def baseStart_237725 : Nat := 118140960795 + 237725 * 2 ^ 59
def prefixEnd_237725 : Nat := 4983230072969 + 3 ^ 40 * 237725 * 2
def baseEnd_237725 : Nat := 108504167635722340928203

theorem tailTrace_237725 : CollatzResearch.WordTrace tailWord_237725 prefixEnd_237725 108504167635722340928203 := by
  unfold tailWord_237725
  simp only [CollatzResearch.WordTrace]
  refine ⟨8670543063770400042762629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5780362042513600028508419 8670543063770400042762629)
  ·
    refine ⟨1625726824456950008017993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8670543063770400042762629 1625726824456950008017993)
    ·
      refine ⟨1219295118342712506013495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1625726824456950008017993 1219295118342712506013495)
      ·
        refine ⟨1828942677514068759020243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1219295118342712506013495 1828942677514068759020243)
        ·
          refine ⟨2743414016271103138530365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1828942677514068759020243 2743414016271103138530365)
          ·
            refine ⟨1028780256101663676948887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2743414016271103138530365 1028780256101663676948887)
            ·
              refine ⟨1543170384152495515423331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1028780256101663676948887 1543170384152495515423331)
              ·
                refine ⟨2314755576228743273134997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1543170384152495515423331 2314755576228743273134997)
                ·
                  refine ⟨108504167635722340928203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2314755576228743273134997 108504167635722340928203)
                  ·
                    rfl

theorem cell20_237725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_237725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237725 prefixEnd_237725 := by exact prefixLift 237725
  have htrace : WordTrace (prefixWord ++ tailWord_237725) baseStart_237725 baseEnd_237725 := by
    simpa [prefixWord, tailWord_237725, baseEnd_237725] using wordTrace_append hprefix tailTrace_237725
  have hstable : (prefixWord ++ tailWord_237725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237725).length < 2 ^ (prefixWord ++ tailWord_237725).sum := by decide
  have hdescent : baseEnd_237725 < baseStart_237725 := by decide
  rcases family_descends (prefixWord ++ tailWord_237725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237770 : List Nat := [3, 1, 2, 1, 3, 1, 2, 7]
def baseStart_237770 : Nat := 118140960795 + 237770 * 2 ^ 59
def prefixEnd_237770 : Nat := 4983230072969 + 3 ^ 40 * 237770 * 2
def baseEnd_237770 : Nat := 36174902287300728142673

theorem tailTrace_237770 : CollatzResearch.WordTrace tailWord_237770 prefixEnd_237770 36174902287300728142673 := by
  unfold tailWord_237770
  simp only [CollatzResearch.WordTrace]
  refine ⟨2168046087151843182037691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5781456232404915152100509 2168046087151843182037691)
  ·
    refine ⟨3252069130727764773056537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2168046087151843182037691 3252069130727764773056537)
    ·
      refine ⟨2439051848045823579792403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3252069130727764773056537 2439051848045823579792403)
      ·
        refine ⟨3658577772068735369688605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2439051848045823579792403 3658577772068735369688605)
        ·
          refine ⟨1371966664525775763633227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3658577772068735369688605 1371966664525775763633227)
          ·
            refine ⟨2057949996788663645449841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1371966664525775763633227 2057949996788663645449841)
            ·
              refine ⟨1543462497591497734087381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2057949996788663645449841 1543462497591497734087381)
              ·
                refine ⟨36174902287300728142673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1543462497591497734087381 36174902287300728142673)
                ·
                  rfl

theorem cell20_237770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_237770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237770 prefixEnd_237770 := by exact prefixLift 237770
  have htrace : WordTrace (prefixWord ++ tailWord_237770) baseStart_237770 baseEnd_237770 := by
    simpa [prefixWord, tailWord_237770, baseEnd_237770] using wordTrace_append hprefix tailTrace_237770
  have hstable : (prefixWord ++ tailWord_237770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237770).length < 2 ^ (prefixWord ++ tailWord_237770).sum := by decide
  have hdescent : baseEnd_237770 < baseStart_237770 := by decide
  rcases family_descends (prefixWord ++ tailWord_237770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237797 : List Nat := [1, 3, 1, 4, 2, 1, 3, 3, 2]
def baseStart_237797 : Nat := 118140960795 + 237797 * 2 ^ 59
def prefixEnd_237797 : Nat := 4983230072969 + 3 ^ 40 * 237797 * 2
def baseEnd_237797 : Nat := 108537030397610090527909

theorem tailTrace_237797 : CollatzResearch.WordTrace tailWord_237797 prefixEnd_237797 108537030397610090527909 := by
  unfold tailWord_237797
  simp only [CollatzResearch.WordTrace]
  refine ⟨8673169119509556339383645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5782112746339704226255763 8673169119509556339383645)
  ·
    refine ⟨3252438419816083627268867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8673169119509556339383645 3252438419816083627268867)
    ·
      refine ⟨4878657629724125440903301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3252438419816083627268867 4878657629724125440903301)
      ·
        refine ⟨914748305573273520169369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4878657629724125440903301 914748305573273520169369)
        ·
          refine ⟨686061229179955140127027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 914748305573273520169369 686061229179955140127027)
          ·
            refine ⟨1029091843769932710190541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 686061229179955140127027 1029091843769932710190541)
            ·
              refine ⟨385909441413724766321453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1029091843769932710190541 385909441413724766321453)
              ·
                refine ⟨144716040530146787370545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 385909441413724766321453 144716040530146787370545)
                ·
                  refine ⟨108537030397610090527909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144716040530146787370545 108537030397610090527909)
                  ·
                    rfl

theorem cell20_237797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 3, 2].length) (baseStart_237797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237797 prefixEnd_237797 := by exact prefixLift 237797
  have htrace : WordTrace (prefixWord ++ tailWord_237797) baseStart_237797 baseEnd_237797 := by
    simpa [prefixWord, tailWord_237797, baseEnd_237797] using wordTrace_append hprefix tailTrace_237797
  have hstable : (prefixWord ++ tailWord_237797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237797).length < 2 ^ (prefixWord ++ tailWord_237797).sum := by decide
  have hdescent : baseEnd_237797 < baseStart_237797 := by decide
  rcases family_descends (prefixWord ++ tailWord_237797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237818 : List Nat := [3, 1, 1, 1, 1, 7, 1, 1, 4]
def baseStart_237818 : Nat := 118140960795 + 237818 * 2 ^ 59
def prefixEnd_237818 : Nat := 4983230072969 + 3 ^ 40 * 237818 * 2
def baseEnd_237818 : Nat := 108546615369827350827823

theorem tailTrace_237818 : CollatzResearch.WordTrace tailWord_237818 prefixEnd_237818 108546615369827350827823 := by
  unfold tailWord_237818
  simp only [CollatzResearch.WordTrace]
  refine ⟨2168483763108369231474527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5782623368288984617265405 2168483763108369231474527)
  ·
    refine ⟨3252725644662553847211791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2168483763108369231474527 3252725644662553847211791)
    ·
      refine ⟨4879088466993830770817687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3252725644662553847211791 4879088466993830770817687)
      ·
        refine ⟨7318632700490746156226531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4879088466993830770817687 7318632700490746156226531)
        ·
          refine ⟨10977949050736119234339797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7318632700490746156226531 10977949050736119234339797)
          ·
            refine ⟨257295680876627794554839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 10977949050736119234339797 257295680876627794554839)
            ·
              refine ⟨385943521314941691832259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257295680876627794554839 385943521314941691832259)
              ·
                refine ⟨578915281972412537748389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385943521314941691832259 578915281972412537748389)
                ·
                  refine ⟨108546615369827350827823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 578915281972412537748389 108546615369827350827823)
                  ·
                    rfl

theorem cell20_237818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 4].length) (baseStart_237818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237818 prefixEnd_237818 := by exact prefixLift 237818
  have htrace : WordTrace (prefixWord ++ tailWord_237818) baseStart_237818 baseEnd_237818 := by
    simpa [prefixWord, tailWord_237818, baseEnd_237818] using wordTrace_append hprefix tailTrace_237818
  have hstable : (prefixWord ++ tailWord_237818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237818).length < 2 ^ (prefixWord ++ tailWord_237818).sum := by decide
  have hdescent : baseEnd_237818 < baseStart_237818 := by decide
  rcases family_descends (prefixWord ++ tailWord_237818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237866 : List Nat := [3, 1, 4, 2, 2, 1, 2, 2, 3]
def baseStart_237866 : Nat := 118140960795 + 237866 * 2 ^ 59
def prefixEnd_237866 : Nat := 4983230072969 + 3 ^ 40 * 237866 * 2
def baseEnd_237866 : Nat := 108568523877752517227627

theorem tailTrace_237866 : CollatzResearch.WordTrace tailWord_237866 prefixEnd_237866 108568523877752517227627 := by
  unfold tailWord_237866
  simp only [CollatzResearch.WordTrace]
  refine ⟨2168921439064895280911363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5783790504173054082430301 2168921439064895280911363)
  ·
    refine ⟨3253382158597342921367045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2168921439064895280911363 3253382158597342921367045)
    ·
      refine ⟨610009154737001797756321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3253382158597342921367045 610009154737001797756321)
      ·
        refine ⟨457506866052751348317241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 610009154737001797756321 457506866052751348317241)
        ·
          refine ⟨343130149539563511237931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457506866052751348317241 343130149539563511237931)
          ·
            refine ⟨514695224309345266856897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343130149539563511237931 514695224309345266856897)
            ·
              refine ⟨386021418232008950142673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 514695224309345266856897 386021418232008950142673)
              ·
                refine ⟨289516063674006712607005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 386021418232008950142673 289516063674006712607005)
                ·
                  refine ⟨108568523877752517227627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 289516063674006712607005 108568523877752517227627)
                  ·
                    rfl

theorem cell20_237866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2, 3].length) (baseStart_237866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237866 prefixEnd_237866 := by exact prefixLift 237866
  have htrace : WordTrace (prefixWord ++ tailWord_237866) baseStart_237866 baseEnd_237866 := by
    simpa [prefixWord, tailWord_237866, baseEnd_237866] using wordTrace_append hprefix tailTrace_237866
  have hstable : (prefixWord ++ tailWord_237866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237866).length < 2 ^ (prefixWord ++ tailWord_237866).sum := by decide
  have hdescent : baseEnd_237866 < baseStart_237866 := by decide
  rcases family_descends (prefixWord ++ tailWord_237866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237873 : List Nat := [1, 2, 2, 3, 4, 1, 1, 4, 2]
def baseStart_237873 : Nat := 118140960795 + 237873 * 2 ^ 59
def prefixEnd_237873 : Nat := 4983230072969 + 3 ^ 40 * 237873 * 2
def baseEnd_237873 : Nat := 108571718868491603994265

theorem tailTrace_237873 : CollatzResearch.WordTrace tailWord_237873 prefixEnd_237873 108571718868491603994265 := by
  unfold tailWord_237873
  simp only [CollatzResearch.WordTrace]
  refine ⟨8675941067234221319150273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5783960711489480879433515 8675941067234221319150273)
  ·
    refine ⟨6506955800425665989362705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8675941067234221319150273 6506955800425665989362705)
    ·
      refine ⟨4880216850319249492022029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6506955800425665989362705 4880216850319249492022029)
      ·
        refine ⟨1830081318869718559508261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4880216850319249492022029 1830081318869718559508261)
        ·
          refine ⟨343140247288072229907799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1830081318869718559508261 343140247288072229907799)
          ·
            refine ⟨514710370932108344861699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343140247288072229907799 514710370932108344861699)
            ·
              refine ⟨772065556398162517292549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 514710370932108344861699 772065556398162517292549)
              ·
                refine ⟨144762291824655471992353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 772065556398162517292549 144762291824655471992353)
                ·
                  refine ⟨108571718868491603994265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144762291824655471992353 108571718868491603994265)
                  ·
                    rfl

theorem cell20_237873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 4, 2].length) (baseStart_237873 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237873 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237873 prefixEnd_237873 := by exact prefixLift 237873
  have htrace : WordTrace (prefixWord ++ tailWord_237873) baseStart_237873 baseEnd_237873 := by
    simpa [prefixWord, tailWord_237873, baseEnd_237873] using wordTrace_append hprefix tailTrace_237873
  have hstable : (prefixWord ++ tailWord_237873).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237873).length < 2 ^ (prefixWord ++ tailWord_237873).sum := by decide
  have hdescent : baseEnd_237873 < baseStart_237873 := by decide
  rcases family_descends (prefixWord ++ tailWord_237873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237877 : List Nat := [1, 3, 3, 1, 2, 1, 2, 3, 4]
def baseStart_237877 : Nat := 118140960795 + 237877 * 2 ^ 59
def prefixEnd_237877 : Nat := 4983230072969 + 3 ^ 40 * 237877 * 2
def baseEnd_237877 : Nat := 108573544577485367860915

theorem tailTrace_237877 : CollatzResearch.WordTrace tailWord_237877 prefixEnd_237877 108573544577485367860915 := by
  unfold tailWord_237877
  simp only [CollatzResearch.WordTrace]
  refine ⟨8676086959219730002295885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5784057972813153334863923 8676086959219730002295885)
  ·
    refine ⟨3253532609707398750860957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8676086959219730002295885 3253532609707398750860957)
    ·
      refine ⟨1220074728640274531572859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3253532609707398750860957 1220074728640274531572859)
      ·
        refine ⟨1830112092960411797359289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1220074728640274531572859 1830112092960411797359289)
        ·
          refine ⟨1372584069720308848019467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1830112092960411797359289 1372584069720308848019467)
          ·
            refine ⟨2058876104580463272029201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1372584069720308848019467 2058876104580463272029201)
            ·
              refine ⟨1544157078435347454021901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2058876104580463272029201 1544157078435347454021901)
              ·
                refine ⟨579058904413255295258213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1544157078435347454021901 579058904413255295258213)
                ·
                  refine ⟨108573544577485367860915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 579058904413255295258213 108573544577485367860915)
                  ·
                    rfl

theorem cell20_237877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_237877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237877 prefixEnd_237877 := by exact prefixLift 237877
  have htrace : WordTrace (prefixWord ++ tailWord_237877) baseStart_237877 baseEnd_237877 := by
    simpa [prefixWord, tailWord_237877, baseEnd_237877] using wordTrace_append hprefix tailTrace_237877
  have hstable : (prefixWord ++ tailWord_237877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237877).length < 2 ^ (prefixWord ++ tailWord_237877).sum := by decide
  have hdescent : baseEnd_237877 < baseStart_237877 := by decide
  rcases family_descends (prefixWord ++ tailWord_237877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237925 : List Nat := [1, 3, 1, 3, 1, 5, 1, 2, 3]
def baseStart_237925 : Nat := 118140960795 + 237925 * 2 ^ 59
def prefixEnd_237925 : Nat := 4983230072969 + 3 ^ 40 * 237925 * 2
def baseEnd_237925 : Nat := 108595453085410534260719

theorem tailTrace_237925 : CollatzResearch.WordTrace tailWord_237925 prefixEnd_237925 108595453085410534260719 := by
  unfold tailWord_237925
  simp only [CollatzResearch.WordTrace]
  refine ⟨8677837663045834200043229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5785225108697222800028819 8677837663045834200043229)
  ·
    refine ⟨3254189123642187825016211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8677837663045834200043229 3254189123642187825016211)
    ·
      refine ⟨4881283685463281737524317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3254189123642187825016211 4881283685463281737524317)
      ·
        refine ⟨1830481382048730651571619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4881283685463281737524317 1830481382048730651571619)
        ·
          refine ⟨2745722073073095977357429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1830481382048730651571619 2745722073073095977357429)
          ·
            refine ⟨257411444350602747877259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2745722073073095977357429 257411444350602747877259)
            ·
              refine ⟨386117166525904121815889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257411444350602747877259 386117166525904121815889)
              ·
                refine ⟨289587874894428091361917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 386117166525904121815889 289587874894428091361917)
                ·
                  refine ⟨108595453085410534260719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 289587874894428091361917 108595453085410534260719)
                  ·
                    rfl

theorem cell20_237925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 2, 3].length) (baseStart_237925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237925 prefixEnd_237925 := by exact prefixLift 237925
  have htrace : WordTrace (prefixWord ++ tailWord_237925) baseStart_237925 baseEnd_237925 := by
    simpa [prefixWord, tailWord_237925, baseEnd_237925] using wordTrace_append hprefix tailTrace_237925
  have hstable : (prefixWord ++ tailWord_237925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237925).length < 2 ^ (prefixWord ++ tailWord_237925).sum := by decide
  have hdescent : baseEnd_237925 < baseStart_237925 := by decide
  rcases family_descends (prefixWord ++ tailWord_237925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237929 : List Nat := [1, 2, 1, 1, 1, 3, 5, 1, 5]
def baseStart_237929 : Nat := 118140960795 + 237929 * 2 ^ 59
def prefixEnd_237929 : Nat := 4983230072969 + 3 ^ 40 * 237929 * 2
def baseEnd_237929 : Nat := 108597278794404298127369

theorem tailTrace_237929 : CollatzResearch.WordTrace tailWord_237929 prefixEnd_237929 108597278794404298127369 := by
  unfold tailWord_237929
  simp only [CollatzResearch.WordTrace]
  refine ⟨8677983555031342883188841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5785322370020895255459227 8677983555031342883188841)
  ·
    refine ⟨6508487666273507162391631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8677983555031342883188841 6508487666273507162391631)
    ·
      refine ⟨9762731499410260743587447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6508487666273507162391631 9762731499410260743587447)
      ·
        refine ⟨14644097249115391115381171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9762731499410260743587447 14644097249115391115381171)
        ·
          refine ⟨21966145873673086673071757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14644097249115391115381171 21966145873673086673071757)
          ·
            refine ⟨8237304702627407502401909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21966145873673086673071757 8237304702627407502401909)
            ·
              refine ⟨772247315871319453350179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8237304702627407502401909 772247315871319453350179)
              ·
                refine ⟨1158370973806979180025269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 772247315871319453350179 1158370973806979180025269)
                ·
                  refine ⟨108597278794404298127369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1158370973806979180025269 108597278794404298127369)
                  ·
                    rfl

theorem cell20_237929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 5].length) (baseStart_237929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237929 prefixEnd_237929 := by exact prefixLift 237929
  have htrace : WordTrace (prefixWord ++ tailWord_237929) baseStart_237929 baseEnd_237929 := by
    simpa [prefixWord, tailWord_237929, baseEnd_237929] using wordTrace_append hprefix tailTrace_237929
  have hstable : (prefixWord ++ tailWord_237929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237929).length < 2 ^ (prefixWord ++ tailWord_237929).sum := by decide
  have hdescent : baseEnd_237929 < baseStart_237929 := by decide
  rcases family_descends (prefixWord ++ tailWord_237929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237932 : List Nat := [2, 2, 1, 1, 6, 1, 2, 1, 4]
def baseStart_237932 : Nat := 118140960795 + 237932 * 2 ^ 59
def prefixEnd_237932 : Nat := 4983230072969 + 3 ^ 40 * 237932 * 2
def baseEnd_237932 : Nat := 108598648076149621027357

theorem tailTrace_237932 : CollatzResearch.WordTrace tailWord_237932 prefixEnd_237932 108598648076149621027357 := by
  unfold tailWord_237932
  simp only [CollatzResearch.WordTrace]
  refine ⟨4339046487010237197774025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5785395316013649597032033 4339046487010237197774025)
  ·
    refine ⟨3254284865257677898330519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4339046487010237197774025 3254284865257677898330519)
    ·
      refine ⟨4881427297886516847495779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3254284865257677898330519 4881427297886516847495779)
      ·
        refine ⟨7322140946829775271243669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4881427297886516847495779 7322140946829775271243669)
        ·
          refine ⟨343225356882645715839547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7322140946829775271243669 343225356882645715839547)
          ·
            refine ⟨514838035323968573759321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343225356882645715839547 514838035323968573759321)
            ·
              refine ⟨386128526492976430319491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 514838035323968573759321 386128526492976430319491)
              ·
                refine ⟨579192789739464645479237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 386128526492976430319491 579192789739464645479237)
                ·
                  refine ⟨108598648076149621027357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 579192789739464645479237 108598648076149621027357)
                  ·
                    rfl

theorem cell20_237932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 4].length) (baseStart_237932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237932 prefixEnd_237932 := by exact prefixLift 237932
  have htrace : WordTrace (prefixWord ++ tailWord_237932) baseStart_237932 baseEnd_237932 := by
    simpa [prefixWord, tailWord_237932, baseEnd_237932] using wordTrace_append hprefix tailTrace_237932
  have hstable : (prefixWord ++ tailWord_237932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237932).length < 2 ^ (prefixWord ++ tailWord_237932).sum := by decide
  have hdescent : baseEnd_237932 < baseStart_237932 := by decide
  rcases family_descends (prefixWord ++ tailWord_237932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237960 : List Nat := [2, 1, 3, 3, 1, 1, 3, 6]
def baseStart_237960 : Nat := 118140960795 + 237960 * 2 ^ 59
def prefixEnd_237960 : Nat := 4983230072969 + 3 ^ 40 * 237960 * 2
def baseEnd_237960 : Nat := 36203809346368656031303

theorem tailTrace_237960 : CollatzResearch.WordTrace tailWord_237960 prefixEnd_237960 36203809346368656031303 := by
  unfold tailWord_237960
  simp only [CollatzResearch.WordTrace]
  refine ⟨4339557108959517588783667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5786076145279356785044889 4339557108959517588783667)
  ·
    refine ⟨6509335663439276383175501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4339557108959517588783667 6509335663439276383175501)
    ·
      refine ⟨2441000873789728643690813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6509335663439276383175501 2441000873789728643690813)
      ·
        refine ⟨915375327671148241384055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2441000873789728643690813 915375327671148241384055)
        ·
          refine ⟨1373062991506722362076083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 915375327671148241384055 1373062991506722362076083)
          ·
            refine ⟨2059594487260083543114125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1373062991506722362076083 2059594487260083543114125)
            ·
              refine ⟨772347932722531328667797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2059594487260083543114125 772347932722531328667797)
              ·
                refine ⟨36203809346368656031303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 772347932722531328667797 36203809346368656031303)
                ·
                  rfl

theorem cell20_237960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 6].length) (baseStart_237960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237960 prefixEnd_237960 := by exact prefixLift 237960
  have htrace : WordTrace (prefixWord ++ tailWord_237960) baseStart_237960 baseEnd_237960 := by
    simpa [prefixWord, tailWord_237960, baseEnd_237960] using wordTrace_append hprefix tailTrace_237960
  have hstable : (prefixWord ++ tailWord_237960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237960).length < 2 ^ (prefixWord ++ tailWord_237960).sum := by decide
  have hdescent : baseEnd_237960 < baseStart_237960 := by decide
  rcases family_descends (prefixWord ++ tailWord_237960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237966 : List Nat := [4, 1, 1, 4, 1, 3, 1, 3, 2]
def baseStart_237966 : Nat := 118140960795 + 237966 * 2 ^ 59
def prefixEnd_237966 : Nat := 4983230072969 + 3 ^ 40 * 237966 * 2
def baseEnd_237966 : Nat := 108614166602596613893885

theorem tailTrace_237966 : CollatzResearch.WordTrace tailWord_237966 prefixEnd_237966 108614166602596613893885 := by
  unfold tailWord_237966
  simp only [CollatzResearch.WordTrace]
  refine ⟨1084916631987162275285719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5786222037264865468190501 1084916631987162275285719)
  ·
    refine ⟨1627374947980743412928579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1084916631987162275285719 1627374947980743412928579)
    ·
      refine ⟨2441062421971115119392869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1627374947980743412928579 2441062421971115119392869)
      ·
        refine ⟨457699204119584084886163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2441062421971115119392869 457699204119584084886163)
        ·
          refine ⟨686548806179376127329245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457699204119584084886163 686548806179376127329245)
          ·
            refine ⟨257455802317266047748467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 686548806179376127329245 257455802317266047748467)
            ·
              refine ⟨386183703475899071622701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257455802317266047748467 386183703475899071622701)
              ·
                refine ⟨144818888803462151858513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 386183703475899071622701 144818888803462151858513)
                ·
                  refine ⟨108614166602596613893885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144818888803462151858513 108614166602596613893885)
                  ·
                    rfl

theorem cell20_237966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 3, 2].length) (baseStart_237966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237966 prefixEnd_237966 := by exact prefixLift 237966
  have htrace : WordTrace (prefixWord ++ tailWord_237966) baseStart_237966 baseEnd_237966 := by
    simpa [prefixWord, tailWord_237966, baseEnd_237966] using wordTrace_append hprefix tailTrace_237966
  have hstable : (prefixWord ++ tailWord_237966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237966).length < 2 ^ (prefixWord ++ tailWord_237966).sum := by decide
  have hdescent : baseEnd_237966 < baseStart_237966 := by decide
  rcases family_descends (prefixWord ++ tailWord_237966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237987 : List Nat := [1, 1, 1, 4, 1, 5, 3, 2, 2]
def baseStart_237987 : Nat := 118140960795 + 237987 * 2 ^ 59
def prefixEnd_237987 : Nat := 4983230072969 + 3 ^ 40 * 237987 * 2
def baseEnd_237987 : Nat := 108623751574813874193799

theorem tailTrace_237987 : CollatzResearch.WordTrace tailWord_237987 prefixEnd_237987 108623751574813874193799 := by
  unfold tailWord_237987
  simp only [CollatzResearch.WordTrace]
  refine ⟨8680098988821218788800215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5786732659214145859200143 8680098988821218788800215)
  ·
    refine ⟨13020148483231828183200323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8680098988821218788800215 13020148483231828183200323)
    ·
      refine ⟨19530222724847742274800485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13020148483231828183200323 19530222724847742274800485)
      ·
        refine ⟨3661916760908951676525091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19530222724847742274800485 3661916760908951676525091)
        ·
          refine ⟨5492875141363427514787637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3661916760908951676525091 5492875141363427514787637)
          ·
            refine ⟨514957044502821329511341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5492875141363427514787637 514957044502821329511341)
            ·
              refine ⟨193108891688557998566753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 514957044502821329511341 193108891688557998566753)
              ·
                refine ⟨144831668766418498925065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193108891688557998566753 144831668766418498925065)
                ·
                  refine ⟨108623751574813874193799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144831668766418498925065 108623751574813874193799)
                  ·
                    rfl

theorem cell20_237987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 2, 2].length) (baseStart_237987 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237987 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237987 prefixEnd_237987 := by exact prefixLift 237987
  have htrace : WordTrace (prefixWord ++ tailWord_237987) baseStart_237987 baseEnd_237987 := by
    simpa [prefixWord, tailWord_237987, baseEnd_237987] using wordTrace_append hprefix tailTrace_237987
  have hstable : (prefixWord ++ tailWord_237987).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237987).length < 2 ^ (prefixWord ++ tailWord_237987).sum := by decide
  have hdescent : baseEnd_237987 < baseStart_237987 := by decide
  rcases family_descends (prefixWord ++ tailWord_237987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237997 : List Nat := [1, 5, 2, 2, 2, 2, 2, 1, 3]
def baseStart_237997 : Nat := 118140960795 + 237997 * 2 ^ 59
def prefixEnd_237997 : Nat := 4983230072969 + 3 ^ 40 * 237997 * 2
def baseEnd_237997 : Nat := 108628315847298283860425

theorem tailTrace_237997 : CollatzResearch.WordTrace tailWord_237997 prefixEnd_237997 108628315847298283860425 := by
  unfold tailWord_237997
  simp only [CollatzResearch.WordTrace]
  refine ⟨8680463718784990496664245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5786975812523326997776163 8680463718784990496664245)
  ·
    refine ⟨813793473636092859062273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8680463718784990496664245 813793473636092859062273)
    ·
      refine ⟨610345105227069644296705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 813793473636092859062273 610345105227069644296705)
      ·
        refine ⟨457758828920302233222529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 610345105227069644296705 457758828920302233222529)
        ·
          refine ⟨343319121690226674916897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457758828920302233222529 343319121690226674916897)
          ·
            refine ⟨257489341267670006187673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 343319121690226674916897 257489341267670006187673)
            ·
              refine ⟨193117005950752504640755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257489341267670006187673 193117005950752504640755)
              ·
                refine ⟨289675508926128756961133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193117005950752504640755 289675508926128756961133)
                ·
                  refine ⟨108628315847298283860425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 289675508926128756961133 108628315847298283860425)
                  ·
                    rfl

theorem cell20_237997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_237997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237997 prefixEnd_237997 := by exact prefixLift 237997
  have htrace : WordTrace (prefixWord ++ tailWord_237997) baseStart_237997 baseEnd_237997 := by
    simpa [prefixWord, tailWord_237997, baseEnd_237997] using wordTrace_append hprefix tailTrace_237997
  have hstable : (prefixWord ++ tailWord_237997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237997).length < 2 ^ (prefixWord ++ tailWord_237997).sum := by decide
  have hdescent : baseEnd_237997 < baseStart_237997 := by decide
  rcases family_descends (prefixWord ++ tailWord_237997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238001 : List Nat := [1, 2, 2, 4, 1, 2, 4, 1, 3]
def baseStart_238001 : Nat := 118140960795 + 238001 * 2 ^ 59
def prefixEnd_238001 : Nat := 4983230072969 + 3 ^ 40 * 238001 * 2
def baseEnd_238001 : Nat := 108630141556292047727075

theorem tailTrace_238001 : CollatzResearch.WordTrace tailWord_238001 prefixEnd_238001 108630141556292047727075 := by
  unfold tailWord_238001
  simp only [CollatzResearch.WordTrace]
  refine ⟨8680609610770499179809857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5787073073846999453206571 8680609610770499179809857)
  ·
    refine ⟨6510457208077874384857393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8680609610770499179809857 6510457208077874384857393)
    ·
      refine ⟨4882842906058405788643045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6510457208077874384857393 4882842906058405788643045)
      ·
        refine ⟨915533044885951085370571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4882842906058405788643045 915533044885951085370571)
        ·
          refine ⟨1373299567328926628055857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 915533044885951085370571 1373299567328926628055857)
          ·
            refine ⟨1029974675496694971041893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1373299567328926628055857 1029974675496694971041893)
            ·
              refine ⟨193120251655630307070355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1029974675496694971041893 193120251655630307070355)
              ·
                refine ⟨289680377483445460605533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193120251655630307070355 289680377483445460605533)
                ·
                  refine ⟨108630141556292047727075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 289680377483445460605533 108630141556292047727075)
                  ·
                    rfl

theorem cell20_238001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 1, 3].length) (baseStart_238001 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238001 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238001 prefixEnd_238001 := by exact prefixLift 238001
  have htrace : WordTrace (prefixWord ++ tailWord_238001) baseStart_238001 baseEnd_238001 := by
    simpa [prefixWord, tailWord_238001, baseEnd_238001] using wordTrace_append hprefix tailTrace_238001
  have hstable : (prefixWord ++ tailWord_238001).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238001).length < 2 ^ (prefixWord ++ tailWord_238001).sum := by decide
  have hdescent : baseEnd_238001 < baseStart_238001 := by decide
  rcases family_descends (prefixWord ++ tailWord_238001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238036 : List Nat := [2, 4, 1, 2, 2, 9]
def baseStart_238036 : Nat := 118140960795 + 238036 * 2 ^ 59
def prefixEnd_238036 : Nat := 4983230072969 + 3 ^ 40 * 238036 * 2
def baseEnd_238036 : Nat := 4023930241110647465195

theorem tailTrace_238036 : CollatzResearch.WordTrace tailWord_238036 prefixEnd_238036 4023930241110647465195 := by
  unfold tailWord_238036
  simp only [CollatzResearch.WordTrace]
  refine ⟨4340943082821850078666981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5787924110429133438222641 4340943082821850078666981)
  ·
    refine ⟨813926828029096889750059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4340943082821850078666981 813926828029096889750059)
    ·
      refine ⟨1220890242043645334625089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 813926828029096889750059 1220890242043645334625089)
      ·
        refine ⟨915667681532734000968817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1220890242043645334625089 915667681532734000968817)
        ·
          refine ⟨686750761149550500726613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 915667681532734000968817 686750761149550500726613)
          ·
            refine ⟨4023930241110647465195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 686750761149550500726613 4023930241110647465195)
            ·
              rfl

theorem cell20_238036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 9].length) (baseStart_238036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238036 prefixEnd_238036 := by exact prefixLift 238036
  have htrace : WordTrace (prefixWord ++ tailWord_238036) baseStart_238036 baseEnd_238036 := by
    simpa [prefixWord, tailWord_238036, baseEnd_238036] using wordTrace_append hprefix tailTrace_238036
  have hstable : (prefixWord ++ tailWord_238036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238036).length < 2 ^ (prefixWord ++ tailWord_238036).sum := by decide
  have hdescent : baseEnd_238036 < baseStart_238036 := by decide
  rcases family_descends (prefixWord ++ tailWord_238036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238057 : List Nat := [1, 2, 1, 1, 1, 2, 1, 11]
def baseStart_238057 : Nat := 118140960795 + 238057 * 2 ^ 59
def prefixEnd_238057 : Nat := 4983230072969 + 3 ^ 40 * 238057 * 2
def baseEnd_238057 : Nat := 36218567160734913953393

theorem tailTrace_238057 : CollatzResearch.WordTrace tailWord_238057 prefixEnd_238057 36218567160734913953393 := by
  unfold tailWord_238057
  simp only [CollatzResearch.WordTrace]
  refine ⟨8682652098567620743848425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5788434732378413829232283 8682652098567620743848425)
  ·
    refine ⟨6511989073925715557886319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8682652098567620743848425 6511989073925715557886319)
    ·
      refine ⟨9767983610888573336829479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6511989073925715557886319 9767983610888573336829479)
      ·
        refine ⟨14651975416332860005244219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9767983610888573336829479 14651975416332860005244219)
        ·
          refine ⟨21977963124499290007866329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14651975416332860005244219 21977963124499290007866329)
          ·
            refine ⟨16483472343374467505899747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21977963124499290007866329 16483472343374467505899747)
            ·
              refine ⟨24725208515061701258849621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16483472343374467505899747 24725208515061701258849621)
              ·
                refine ⟨36218567160734913953393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 24725208515061701258849621 36218567160734913953393)
                ·
                  rfl

theorem cell20_238057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 11].length) (baseStart_238057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238057 prefixEnd_238057 := by exact prefixLift 238057
  have htrace : WordTrace (prefixWord ++ tailWord_238057) baseStart_238057 baseEnd_238057 := by
    simpa [prefixWord, tailWord_238057, baseEnd_238057] using wordTrace_append hprefix tailTrace_238057
  have hstable : (prefixWord ++ tailWord_238057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238057).length < 2 ^ (prefixWord ++ tailWord_238057).sum := by decide
  have hdescent : baseEnd_238057 < baseStart_238057 := by decide
  rcases family_descends (prefixWord ++ tailWord_238057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238088 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 8]
def baseStart_238088 : Nat := 118140960795 + 238088 * 2 ^ 59
def prefixEnd_238088 : Nat := 4983230072969 + 3 ^ 40 * 238088 * 2
def baseEnd_238088 : Nat := 108669850726906411826719

theorem tailTrace_238088 : CollatzResearch.WordTrace tailWord_238088 prefixEnd_238088 108669850726906411826719 := by
  unfold tailWord_238088
  simp only [CollatzResearch.WordTrace]
  refine ⟨4341891380727656519113459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5789188507636875358817945 4341891380727656519113459)
  ·
    refine ⟨6512837071091484778670189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4341891380727656519113459 6512837071091484778670189)
    ·
      refine ⟨2442313901659306792001321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6512837071091484778670189 2442313901659306792001321)
      ·
        refine ⟨1831735426244480094000991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2442313901659306792001321 1831735426244480094000991)
        ·
          refine ⟨2747603139366720141001487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1831735426244480094000991 2747603139366720141001487)
          ·
            refine ⟨4121404709050080211502231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2747603139366720141001487 4121404709050080211502231)
            ·
              refine ⟨6182107063575120317253347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4121404709050080211502231 6182107063575120317253347)
              ·
                refine ⟨9273160595362680475880021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6182107063575120317253347 9273160595362680475880021)
                ·
                  refine ⟨108669850726906411826719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9273160595362680475880021 108669850726906411826719)
                  ·
                    rfl

theorem cell20_238088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_238088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238088 prefixEnd_238088 := by exact prefixLift 238088
  have htrace : WordTrace (prefixWord ++ tailWord_238088) baseStart_238088 baseEnd_238088 := by
    simpa [prefixWord, tailWord_238088, baseEnd_238088] using wordTrace_append hprefix tailTrace_238088
  have hstable : (prefixWord ++ tailWord_238088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238088).length < 2 ^ (prefixWord ++ tailWord_238088).sum := by decide
  have hdescent : baseEnd_238088 < baseStart_238088 := by decide
  rcases family_descends (prefixWord ++ tailWord_238088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238115 : List Nat := [1, 1, 1, 4, 4, 2, 3, 1, 3]
def baseStart_238115 : Nat := 118140960795 + 238115 * 2 ^ 59
def prefixEnd_238115 : Nat := 4983230072969 + 3 ^ 40 * 238115 * 2
def baseEnd_238115 : Nat := 108682174262614317926609

theorem tailTrace_238115 : CollatzResearch.WordTrace tailWord_238115 prefixEnd_238115 108682174262614317926609 := by
  unfold tailWord_238115
  simp only [CollatzResearch.WordTrace]
  refine ⟨8684767532357496649459799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5789845021571664432973199 8684767532357496649459799)
  ·
    refine ⟨13027151298536244974189699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8684767532357496649459799 13027151298536244974189699)
    ·
      refine ⟨19540726947804367461284549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13027151298536244974189699 19540726947804367461284549)
      ·
        refine ⟨3663886302713318898990853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19540726947804367461284549 3663886302713318898990853)
        ·
          refine ⟨686978681758747293560785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3663886302713318898990853 686978681758747293560785)
          ·
            refine ⟨515234011319060470170589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 686978681758747293560785 515234011319060470170589)
            ·
              refine ⟨193212754244647676313971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 515234011319060470170589 193212754244647676313971)
              ·
                refine ⟨289819131366971514470957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193212754244647676313971 289819131366971514470957)
                ·
                  refine ⟨108682174262614317926609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 289819131366971514470957 108682174262614317926609)
                  ·
                    rfl

theorem cell20_238115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 1, 3].length) (baseStart_238115 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238115 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238115 prefixEnd_238115 := by exact prefixLift 238115
  have htrace : WordTrace (prefixWord ++ tailWord_238115) baseStart_238115 baseEnd_238115 := by
    simpa [prefixWord, tailWord_238115, baseEnd_238115] using wordTrace_append hprefix tailTrace_238115
  have hstable : (prefixWord ++ tailWord_238115).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238115).length < 2 ^ (prefixWord ++ tailWord_238115).sum := by decide
  have hdescent : baseEnd_238115 < baseStart_238115 := by decide
  rcases family_descends (prefixWord ++ tailWord_238115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238125 : List Nat := [1, 5, 4, 1, 1, 1, 1, 6]
def baseStart_238125 : Nat := 118140960795 + 238125 * 2 ^ 59
def prefixEnd_238125 : Nat := 4983230072969 + 3 ^ 40 * 238125 * 2
def baseEnd_238125 : Nat := 36228912845032909197745

theorem tailTrace_238125 : CollatzResearch.WordTrace tailWord_238125 prefixEnd_238125 36228912845032909197745 := by
  unfold tailWord_238125
  simp only [CollatzResearch.WordTrace]
  refine ⟨8685132262321268357323829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5790088174880845571549219 8685132262321268357323829)
  ·
    refine ⟨814231149592618908499109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8685132262321268357323829 814231149592618908499109)
    ·
      refine ⟨152668340548616045343583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 814231149592618908499109 152668340548616045343583)
      ·
        refine ⟨229002510822924068015375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152668340548616045343583 229002510822924068015375)
        ·
          refine ⟨343503766234386102023063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229002510822924068015375 343503766234386102023063)
          ·
            refine ⟨515255649351579153034595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343503766234386102023063 515255649351579153034595)
            ·
              refine ⟨772883474027368729551893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 515255649351579153034595 772883474027368729551893)
              ·
                refine ⟨36228912845032909197745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 772883474027368729551893 36228912845032909197745)
                ·
                  rfl

theorem cell20_238125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 6].length) (baseStart_238125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238125 prefixEnd_238125 := by exact prefixLift 238125
  have htrace : WordTrace (prefixWord ++ tailWord_238125) baseStart_238125 baseEnd_238125 := by
    simpa [prefixWord, tailWord_238125, baseEnd_238125] using wordTrace_append hprefix tailTrace_238125
  have hstable : (prefixWord ++ tailWord_238125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238125).length < 2 ^ (prefixWord ++ tailWord_238125).sum := by decide
  have hdescent : baseEnd_238125 < baseStart_238125 := by decide
  rcases family_descends (prefixWord ++ tailWord_238125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238212 : List Nat := [2, 3, 2, 1, 3, 1, 1, 4, 3]
def baseStart_238212 : Nat := 118140960795 + 238212 * 2 ^ 59
def prefixEnd_238212 : Nat := 4983230072969 + 3 ^ 40 * 238212 * 2
def baseEnd_238212 : Nat := 108726447705713091692879

theorem tailTrace_238212 : CollatzResearch.WordTrace tailWord_238212 prefixEnd_238212 108726447705713091692879 := by
  unfold tailWord_238212
  simp only [CollatzResearch.WordTrace]
  refine ⟨4344152706503041107870445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5792203608670721477160593 4344152706503041107870445)
  ·
    refine ⟨1629057264938640415451417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4344152706503041107870445 1629057264938640415451417)
    ·
      refine ⟨1221792948703980311588563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1629057264938640415451417 1221792948703980311588563)
      ·
        refine ⟨1832689423055970467382845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1221792948703980311588563 1832689423055970467382845)
        ·
          refine ⟨687258533645988925268567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1832689423055970467382845 687258533645988925268567)
          ·
            refine ⟨1030887800468983387902851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 687258533645988925268567 1030887800468983387902851)
            ·
              refine ⟨1546331700703475081854277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1030887800468983387902851 1546331700703475081854277)
              ·
                refine ⟨289937193881901577847677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1546331700703475081854277 289937193881901577847677)
                ·
                  refine ⟨108726447705713091692879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 289937193881901577847677 108726447705713091692879)
                  ·
                    rfl

theorem cell20_238212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_238212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238212 prefixEnd_238212 := by exact prefixLift 238212
  have htrace : WordTrace (prefixWord ++ tailWord_238212) baseStart_238212 baseEnd_238212 := by
    simpa [prefixWord, tailWord_238212, baseEnd_238212] using wordTrace_append hprefix tailTrace_238212
  have hstable : (prefixWord ++ tailWord_238212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238212).length < 2 ^ (prefixWord ++ tailWord_238212).sum := by decide
  have hdescent : baseEnd_238212 < baseStart_238212 := by decide
  rcases family_descends (prefixWord ++ tailWord_238212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238233 : List Nat := [1, 2, 1, 2, 1, 2, 3, 5, 3]
def baseStart_238233 : Nat := 118140960795 + 238233 * 2 ^ 59
def prefixEnd_238233 : Nat := 4983230072969 + 3 ^ 40 * 238233 * 2
def baseEnd_238233 : Nat := 108736032677930351992793

theorem tailTrace_238233 : CollatzResearch.WordTrace tailWord_238233 prefixEnd_238233 108736032677930351992793 := by
  unfold tailWord_238233
  simp only [CollatzResearch.WordTrace]
  refine ⟨8689071345930002802255353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5792714230620001868170235 8689071345930002802255353)
  ·
    refine ⟨6516803509447502101691515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8689071345930002802255353 6516803509447502101691515)
    ·
      refine ⟨9775205264171253152537273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6516803509447502101691515 9775205264171253152537273)
      ·
        refine ⟨7331403948128439864402955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9775205264171253152537273 7331403948128439864402955)
        ·
          refine ⟨10997105922192659796604433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7331403948128439864402955 10997105922192659796604433)
          ·
            refine ⟨8247829441644494847453325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10997105922192659796604433 8247829441644494847453325)
            ·
              refine ⟨3092936040616685567794997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8247829441644494847453325 3092936040616685567794997)
              ·
                refine ⟨289962753807814271980781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3092936040616685567794997 289962753807814271980781)
                ·
                  refine ⟨108736032677930351992793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 289962753807814271980781 108736032677930351992793)
                  ·
                    rfl

theorem cell20_238233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5, 3].length) (baseStart_238233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238233 prefixEnd_238233 := by exact prefixLift 238233
  have htrace : WordTrace (prefixWord ++ tailWord_238233) baseStart_238233 baseEnd_238233 := by
    simpa [prefixWord, tailWord_238233, baseEnd_238233] using wordTrace_append hprefix tailTrace_238233
  have hstable : (prefixWord ++ tailWord_238233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238233).length < 2 ^ (prefixWord ++ tailWord_238233).sum := by decide
  have hdescent : baseEnd_238233 < baseStart_238233 := by decide
  rcases family_descends (prefixWord ++ tailWord_238233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238253 : List Nat := [1, 5, 2, 1, 1, 3, 2, 3, 2]
def baseStart_238253 : Nat := 118140960795 + 238253 * 2 ^ 59
def prefixEnd_238253 : Nat := 4983230072969 + 3 ^ 40 * 238253 * 2
def baseEnd_238253 : Nat := 108745161222899171326045

theorem tailTrace_238253 : CollatzResearch.WordTrace tailWord_238253 prefixEnd_238253 108745161222899171326045 := by
  unfold tailWord_238253
  simp only [CollatzResearch.WordTrace]
  refine ⟨8689800805857546217983413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5793200537238364145322275 8689800805857546217983413)
  ·
    refine ⟨814668825549144957935945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8689800805857546217983413 814668825549144957935945)
    ·
      refine ⟨611001619161858718451959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 814668825549144957935945 611001619161858718451959)
      ·
        refine ⟨916502428742788077677939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 611001619161858718451959 916502428742788077677939)
        ·
          refine ⟨1374753643114182116516909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 916502428742788077677939 1374753643114182116516909)
          ·
            refine ⟨515532616167818293693841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1374753643114182116516909 515532616167818293693841)
            ·
              refine ⟨386649462125863720270381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 515532616167818293693841 386649462125863720270381)
              ·
                refine ⟨144993548297198895101393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 386649462125863720270381 144993548297198895101393)
                ·
                  refine ⟨108745161222899171326045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144993548297198895101393 108745161222899171326045)
                  ·
                    rfl

theorem cell20_238253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_238253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238253 prefixEnd_238253 := by exact prefixLift 238253
  have htrace : WordTrace (prefixWord ++ tailWord_238253) baseStart_238253 baseEnd_238253 := by
    simpa [prefixWord, tailWord_238253, baseEnd_238253] using wordTrace_append hprefix tailTrace_238253
  have hstable : (prefixWord ++ tailWord_238253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238253).length < 2 ^ (prefixWord ++ tailWord_238253).sum := by decide
  have hdescent : baseEnd_238253 < baseStart_238253 := by decide
  rcases family_descends (prefixWord ++ tailWord_238253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238271 : List Nat := [1, 1, 2, 2, 2, 5, 1, 1, 5]
def baseStart_238271 : Nat := 118140960795 + 238271 * 2 ^ 59
def prefixEnd_238271 : Nat := 4983230072969 + 3 ^ 40 * 238271 * 2
def baseEnd_238271 : Nat := 108753376913371108725971

theorem tailTrace_238271 : CollatzResearch.WordTrace tailWord_238271 prefixEnd_238271 108753376913371108725971 := by
  unfold tailWord_238271
  simp only [CollatzResearch.WordTrace]
  refine ⟨8690457319792335292138667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5793638213194890194759111 8690457319792335292138667)
  ·
    refine ⟨13035685979688502938208001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8690457319792335292138667 13035685979688502938208001)
    ·
      refine ⟨9776764484766377203656001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13035685979688502938208001 9776764484766377203656001)
      ·
        refine ⟨7332573363574782902742001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9776764484766377203656001 7332573363574782902742001)
        ·
          refine ⟨5499430022681087177056501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7332573363574782902742001 5499430022681087177056501)
          ·
            refine ⟨515571564626351922849047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5499430022681087177056501 515571564626351922849047)
            ·
              refine ⟨773357346939527884273571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 515571564626351922849047 773357346939527884273571)
              ·
                refine ⟨1160036020409291826410357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 773357346939527884273571 1160036020409291826410357)
                ·
                  refine ⟨108753376913371108725971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1160036020409291826410357 108753376913371108725971)
                  ·
                    rfl

theorem cell20_238271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 5].length) (baseStart_238271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238271 prefixEnd_238271 := by exact prefixLift 238271
  have htrace : WordTrace (prefixWord ++ tailWord_238271) baseStart_238271 baseEnd_238271 := by
    simpa [prefixWord, tailWord_238271, baseEnd_238271] using wordTrace_append hprefix tailTrace_238271
  have hstable : (prefixWord ++ tailWord_238271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238271).length < 2 ^ (prefixWord ++ tailWord_238271).sum := by decide
  have hdescent : baseEnd_238271 < baseStart_238271 := by decide
  rcases family_descends (prefixWord ++ tailWord_238271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238309 : List Nat := [1, 3, 1, 4, 1, 2, 1, 2, 5]
def baseStart_238309 : Nat := 118140960795 + 238309 * 2 ^ 59
def prefixEnd_238309 : Nat := 4983230072969 + 3 ^ 40 * 238309 * 2
def baseEnd_238309 : Nat := 108770721148811865459149

theorem tailTrace_238309 : CollatzResearch.WordTrace tailWord_238309 prefixEnd_238309 108770721148811865459149 := by
  unfold tailWord_238309
  simp only [CollatzResearch.WordTrace]
  refine ⟨8691843293654667782021981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5794562195769778521347987 8691843293654667782021981)
  ·
    refine ⟨3259441235120500418258243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8691843293654667782021981 3259441235120500418258243)
    ·
      refine ⟨4889161852680750627387365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3259441235120500418258243 4889161852680750627387365)
      ·
        refine ⟨916717847377640742635131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4889161852680750627387365 916717847377640742635131)
        ·
          refine ⟨1375076771066461113952697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 916717847377640742635131 1375076771066461113952697)
          ·
            refine ⟨1031307578299845835464523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1375076771066461113952697 1031307578299845835464523)
            ·
              refine ⟨1546961367449768753196785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1031307578299845835464523 1546961367449768753196785)
              ·
                refine ⟨1160221025587326564897589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1546961367449768753196785 1160221025587326564897589)
                ·
                  refine ⟨108770721148811865459149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1160221025587326564897589 108770721148811865459149)
                  ·
                    rfl

theorem cell20_238309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_238309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238309 prefixEnd_238309 := by exact prefixLift 238309
  have htrace : WordTrace (prefixWord ++ tailWord_238309) baseStart_238309 baseEnd_238309 := by
    simpa [prefixWord, tailWord_238309, baseEnd_238309] using wordTrace_append hprefix tailTrace_238309
  have hstable : (prefixWord ++ tailWord_238309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238309).length < 2 ^ (prefixWord ++ tailWord_238309).sum := by decide
  have hdescent : baseEnd_238309 < baseStart_238309 := by decide
  rcases family_descends (prefixWord ++ tailWord_238309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238325 : List Nat := [1, 3, 6, 1, 2, 1, 1, 1, 4]
def baseStart_238325 : Nat := 118140960795 + 238325 * 2 ^ 59
def prefixEnd_238325 : Nat := 4983230072969 + 3 ^ 40 * 238325 * 2
def baseEnd_238325 : Nat := 108778023984786920925751

theorem tailTrace_238325 : CollatzResearch.WordTrace tailWord_238325 prefixEnd_238325 108778023984786920925751 := by
  unfold tailWord_238325
  simp only [CollatzResearch.WordTrace]
  refine ⟨8692426861596702514604429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5794951241064468343069619 8692426861596702514604429)
  ·
    refine ⟨3259660073098763442976661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8692426861596702514604429 3259660073098763442976661)
    ·
      refine ⟨152796565926504536389531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3259660073098763442976661 152796565926504536389531)
      ·
        refine ⟨229194848889756804584297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152796565926504536389531 229194848889756804584297)
        ·
          refine ⟨171896136667317603438223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229194848889756804584297 171896136667317603438223)
          ·
            refine ⟨257844205000976405157335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171896136667317603438223 257844205000976405157335)
            ·
              refine ⟨386766307501464607736003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257844205000976405157335 386766307501464607736003)
              ·
                refine ⟨580149461252196911604005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 386766307501464607736003 580149461252196911604005)
                ·
                  refine ⟨108778023984786920925751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 580149461252196911604005 108778023984786920925751)
                  ·
                    rfl

theorem cell20_238325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 4].length) (baseStart_238325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238325 prefixEnd_238325 := by exact prefixLift 238325
  have htrace : WordTrace (prefixWord ++ tailWord_238325) baseStart_238325 baseEnd_238325 := by
    simpa [prefixWord, tailWord_238325, baseEnd_238325] using wordTrace_append hprefix tailTrace_238325
  have hstable : (prefixWord ++ tailWord_238325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238325).length < 2 ^ (prefixWord ++ tailWord_238325).sum := by decide
  have hdescent : baseEnd_238325 < baseStart_238325 := by decide
  rcases family_descends (prefixWord ++ tailWord_238325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238326 : List Nat := [5, 1, 1, 1, 1, 2, 2, 4, 3]
def baseStart_238326 : Nat := 118140960795 + 238326 * 2 ^ 59
def prefixEnd_238326 : Nat := 4983230072969 + 3 ^ 40 * 238326 * 2
def baseEnd_238326 : Nat := 108778480412035361892413

theorem tailTrace_238326 : CollatzResearch.WordTrace tailWord_238326 prefixEnd_238326 108778480412035361892413 := by
  unfold tailWord_238326
  simp only [CollatzResearch.WordTrace]
  refine ⟨543278958412067480336927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5794975556395386456927221 543278958412067480336927)
  ·
    refine ⟨814918437618101220505391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 543278958412067480336927 814918437618101220505391)
    ·
      refine ⟨1222377656427151830758087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 814918437618101220505391 1222377656427151830758087)
      ·
        refine ⟨1833566484640727746137131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1222377656427151830758087 1833566484640727746137131)
        ·
          refine ⟨2750349726961091619205697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1833566484640727746137131 2750349726961091619205697)
          ·
            refine ⟨2062762295220818714404273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2750349726961091619205697 2062762295220818714404273)
            ·
              refine ⟨1547071721415614035803205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2062762295220818714404273 1547071721415614035803205)
              ·
                refine ⟨290075947765427631713101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1547071721415614035803205 290075947765427631713101)
                ·
                  refine ⟨108778480412035361892413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 290075947765427631713101 108778480412035361892413)
                  ·
                    rfl

theorem cell20_238326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_238326 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238326 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238326 prefixEnd_238326 := by exact prefixLift 238326
  have htrace : WordTrace (prefixWord ++ tailWord_238326) baseStart_238326 baseEnd_238326 := by
    simpa [prefixWord, tailWord_238326, baseEnd_238326] using wordTrace_append hprefix tailTrace_238326
  have hstable : (prefixWord ++ tailWord_238326).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238326).length < 2 ^ (prefixWord ++ tailWord_238326).sum := by decide
  have hdescent : baseEnd_238326 < baseStart_238326 := by decide
  rcases family_descends (prefixWord ++ tailWord_238326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238340 : List Nat := [2, 3, 2, 2, 1, 1, 4, 5]
def baseStart_238340 : Nat := 118140960795 + 238340 * 2 ^ 59
def prefixEnd_238340 : Nat := 4983230072969 + 3 ^ 40 * 238340 * 2
def baseEnd_238340 : Nat := 36261623464504511808563

theorem tailTrace_238340 : CollatzResearch.WordTrace tailWord_238340 prefixEnd_238340 36261623464504511808563 := by
  unfold tailWord_238340
  simp only [CollatzResearch.WordTrace]
  refine ⟨4346486978271180038200237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5795315971028240050933649 4346486978271180038200237)
  ·
    refine ⟨1629932616851692514325089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4346486978271180038200237 1629932616851692514325089)
    ·
      refine ⟨1222449462638769385743817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1629932616851692514325089 1222449462638769385743817)
      ·
        refine ⟨916837096979077039307863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1222449462638769385743817 916837096979077039307863)
        ·
          refine ⟨1375255645468615558961795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 916837096979077039307863 1375255645468615558961795)
          ·
            refine ⟨2062883468202923338442693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1375255645468615558961795 2062883468202923338442693)
            ·
              refine ⟨386790650288048125958005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2062883468202923338442693 386790650288048125958005)
              ·
                refine ⟨36261623464504511808563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 386790650288048125958005 36261623464504511808563)
                ·
                  rfl

theorem cell20_238340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 5].length) (baseStart_238340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238340 prefixEnd_238340 := by exact prefixLift 238340
  have htrace : WordTrace (prefixWord ++ tailWord_238340) baseStart_238340 baseEnd_238340 := by
    simpa [prefixWord, tailWord_238340, baseEnd_238340] using wordTrace_append hprefix tailTrace_238340
  have hstable : (prefixWord ++ tailWord_238340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238340).length < 2 ^ (prefixWord ++ tailWord_238340).sum := by decide
  have hdescent : baseEnd_238340 < baseStart_238340 := by decide
  rcases family_descends (prefixWord ++ tailWord_238340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238343 : List Nat := [1, 1, 4, 4, 1, 1, 4, 1, 3]
def baseStart_238343 : Nat := 118140960795 + 238343 * 2 ^ 59
def prefixEnd_238343 : Nat := 4983230072969 + 3 ^ 40 * 238343 * 2
def baseEnd_238343 : Nat := 108786239675258858325677

theorem tailTrace_238343 : CollatzResearch.WordTrace tailWord_238343 prefixEnd_238343 108786239675258858325677 := by
  unfold tailWord_238343
  simp only [CollatzResearch.WordTrace]
  refine ⟨8693083375531491588759683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5795388917020994392506455 8693083375531491588759683)
  ·
    refine ⟨13039625063297237383139525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8693083375531491588759683 13039625063297237383139525)
    ·
      refine ⟨2444929699368232009338661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13039625063297237383139525 2444929699368232009338661)
      ·
        refine ⟨458424318631543501750999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2444929699368232009338661 458424318631543501750999)
        ·
          refine ⟨687636477947315252626499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458424318631543501750999 687636477947315252626499)
          ·
            refine ⟨1031454716920972878939749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 687636477947315252626499 1031454716920972878939749)
            ·
              refine ⟨193397759422682414801203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1031454716920972878939749 193397759422682414801203)
              ·
                refine ⟨290096639134023622201805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193397759422682414801203 290096639134023622201805)
                ·
                  refine ⟨108786239675258858325677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 290096639134023622201805 108786239675258858325677)
                  ·
                    rfl

theorem cell20_238343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 3].length) (baseStart_238343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238343 prefixEnd_238343 := by exact prefixLift 238343
  have htrace : WordTrace (prefixWord ++ tailWord_238343) baseStart_238343 baseEnd_238343 := by
    simpa [prefixWord, tailWord_238343, baseEnd_238343] using wordTrace_append hprefix tailTrace_238343
  have hstable : (prefixWord ++ tailWord_238343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238343).length < 2 ^ (prefixWord ++ tailWord_238343).sum := by decide
  have hdescent : baseEnd_238343 < baseStart_238343 := by decide
  rcases family_descends (prefixWord ++ tailWord_238343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238371 : List Nat := [1, 1, 1, 4, 2, 1, 1, 7, 2]
def baseStart_238371 : Nat := 118140960795 + 238371 * 2 ^ 59
def prefixEnd_238371 : Nat := 4983230072969 + 3 ^ 40 * 238371 * 2
def baseEnd_238371 : Nat := 108799019638215205392229

theorem tailTrace_238371 : CollatzResearch.WordTrace tailWord_238371 prefixEnd_238371 108799019638215205392229 := by
  unfold tailWord_238371
  simp only [CollatzResearch.WordTrace]
  refine ⟨8694104619430052370778967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5796069746286701580519311 8694104619430052370778967)
  ·
    refine ⟨13041156929145078556168451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8694104619430052370778967 13041156929145078556168451)
    ·
      refine ⟨19561735393717617834252677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13041156929145078556168451 19561735393717617834252677)
      ·
        refine ⟨3667825386322053343922377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19561735393717617834252677 3667825386322053343922377)
        ·
          refine ⟨2750869039741540007941783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3667825386322053343922377 2750869039741540007941783)
          ·
            refine ⟨4126303559612310011912675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2750869039741540007941783 4126303559612310011912675)
            ·
              refine ⟨6189455339418465017869013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4126303559612310011912675 6189455339418465017869013)
              ·
                refine ⟨145065359517620273856305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6189455339418465017869013 145065359517620273856305)
                ·
                  refine ⟨108799019638215205392229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145065359517620273856305 108799019638215205392229)
                  ·
                    rfl

theorem cell20_238371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 7, 2].length) (baseStart_238371 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238371 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238371 prefixEnd_238371 := by exact prefixLift 238371
  have htrace : WordTrace (prefixWord ++ tailWord_238371) baseStart_238371 baseEnd_238371 := by
    simpa [prefixWord, tailWord_238371, baseEnd_238371] using wordTrace_append hprefix tailTrace_238371
  have hstable : (prefixWord ++ tailWord_238371).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238371).length < 2 ^ (prefixWord ++ tailWord_238371).sum := by decide
  have hdescent : baseEnd_238371 < baseStart_238371 := by decide
  rcases family_descends (prefixWord ++ tailWord_238371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238378 : List Nat := [3, 1, 4, 3, 9]
def baseStart_238378 : Nat := 118140960795 + 238378 * 2 ^ 59
def prefixEnd_238378 : Nat := 4983230072969 + 3 ^ 40 * 238378 * 2
def baseEnd_238378 : Nat := 1343237217641411014307

theorem tailTrace_238378 : CollatzResearch.WordTrace tailWord_238378 prefixEnd_238378 1343237217641411014307 := by
  unfold tailWord_238378
  simp only [CollatzResearch.WordTrace]
  refine ⟨2173589982601173141570947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5796239953603128377522525 2173589982601173141570947)
  ·
    refine ⟨3260384973901759712356421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2173589982601173141570947 3260384973901759712356421)
    ·
      refine ⟨611322182606579946066829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3260384973901759712356421 611322182606579946066829)
      ·
        refine ⟨229245818477467479775061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 611322182606579946066829 229245818477467479775061)
        ·
          refine ⟨1343237217641411014307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 229245818477467479775061 1343237217641411014307)
          ·
            rfl

theorem cell20_238378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 9].length) (baseStart_238378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238378 prefixEnd_238378 := by exact prefixLift 238378
  have htrace : WordTrace (prefixWord ++ tailWord_238378) baseStart_238378 baseEnd_238378 := by
    simpa [prefixWord, tailWord_238378, baseEnd_238378] using wordTrace_append hprefix tailTrace_238378
  have hstable : (prefixWord ++ tailWord_238378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238378).length < 2 ^ (prefixWord ++ tailWord_238378).sum := by decide
  have hdescent : baseEnd_238378 < baseStart_238378 := by decide
  rcases family_descends (prefixWord ++ tailWord_238378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238392 : List Nat := [2, 1, 2, 1, 3, 2, 2, 3, 4]
def baseStart_238392 : Nat := 118140960795 + 238392 * 2 ^ 59
def prefixEnd_238392 : Nat := 4983230072969 + 3 ^ 40 * 238392 * 2
def baseEnd_238392 : Nat := 108808604610432465692143

theorem tailTrace_238392 : CollatzResearch.WordTrace tailWord_238392 prefixEnd_238392 108808604610432465692143 := by
  unfold tailWord_238392
  simp only [CollatzResearch.WordTrace]
  refine ⟨4347435276176986478646715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5796580368235981971528953 4347435276176986478646715)
  ·
    refine ⟨6521152914265479717970073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4347435276176986478646715 6521152914265479717970073)
    ·
      refine ⟨4890864685699109788477555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6521152914265479717970073 4890864685699109788477555)
      ·
        refine ⟨7336297028548664682716333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4890864685699109788477555 7336297028548664682716333)
        ·
          refine ⟨2751111385705749256018625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7336297028548664682716333 2751111385705749256018625)
          ·
            refine ⟨2063333539279311942013969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2751111385705749256018625 2063333539279311942013969)
            ·
              refine ⟨1547500154459483956510477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2063333539279311942013969 1547500154459483956510477)
              ·
                refine ⟨580312557922306483691429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1547500154459483956510477 580312557922306483691429)
                ·
                  refine ⟨108808604610432465692143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 580312557922306483691429 108808604610432465692143)
                  ·
                    rfl

theorem cell20_238392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 4].length) (baseStart_238392 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238392 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238392 prefixEnd_238392 := by exact prefixLift 238392
  have htrace : WordTrace (prefixWord ++ tailWord_238392) baseStart_238392 baseEnd_238392 := by
    simpa [prefixWord, tailWord_238392, baseEnd_238392] using wordTrace_append hprefix tailTrace_238392
  have hstable : (prefixWord ++ tailWord_238392).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238392).length < 2 ^ (prefixWord ++ tailWord_238392).sum := by decide
  have hdescent : baseEnd_238392 < baseStart_238392 := by decide
  rcases family_descends (prefixWord ++ tailWord_238392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238426 : List Nat := [3, 1, 1, 2, 1, 5, 2, 3, 2]
def baseStart_238426 : Nat := 118140960795 + 238426 * 2 ^ 59
def prefixEnd_238426 : Nat := 4983230072969 + 3 ^ 40 * 238426 * 2
def baseEnd_238426 : Nat := 108824123136879458558671

theorem tailTrace_238426 : CollatzResearch.WordTrace tailWord_238426 prefixEnd_238426 108824123136879458558671 := by
  unfold tailWord_238426
  simp only [CollatzResearch.WordTrace]
  refine ⟨2174027658557699191007783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5797407089487197842687421 2174027658557699191007783)
  ·
    refine ⟨3261041487836548786511675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2174027658557699191007783 3261041487836548786511675)
    ·
      refine ⟨4891562231754823179767513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3261041487836548786511675 4891562231754823179767513)
      ·
        refine ⟨3668671673816117384825635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4891562231754823179767513 3668671673816117384825635)
        ·
          refine ⟨5503007510724176077238453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3668671673816117384825635 5503007510724176077238453)
          ·
            refine ⟨515906954130391507241105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5503007510724176077238453 515906954130391507241105)
            ·
              refine ⟨386930215597793630430829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 515906954130391507241105 386930215597793630430829)
              ·
                refine ⟨145098830849172611411561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 386930215597793630430829 145098830849172611411561)
                ·
                  refine ⟨108824123136879458558671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145098830849172611411561 108824123136879458558671)
                  ·
                    rfl

theorem cell20_238426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 3, 2].length) (baseStart_238426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238426 prefixEnd_238426 := by exact prefixLift 238426
  have htrace : WordTrace (prefixWord ++ tailWord_238426) baseStart_238426 baseEnd_238426 := by
    simpa [prefixWord, tailWord_238426, baseEnd_238426] using wordTrace_append hprefix tailTrace_238426
  have hstable : (prefixWord ++ tailWord_238426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238426).length < 2 ^ (prefixWord ++ tailWord_238426).sum := by decide
  have hdescent : baseEnd_238426 < baseStart_238426 := by decide
  rcases family_descends (prefixWord ++ tailWord_238426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238440 : List Nat := [2, 1, 4, 2, 1, 2, 3, 2, 3]
def baseStart_238440 : Nat := 118140960795 + 238440 * 2 ^ 59
def prefixEnd_238440 : Nat := 4983230072969 + 3 ^ 40 * 238440 * 2
def baseEnd_238440 : Nat := 108830513118357632091947

theorem tailTrace_238440 : CollatzResearch.WordTrace tailWord_238440 prefixEnd_238440 108830513118357632091947 := by
  unfold tailWord_238440
  simp only [CollatzResearch.WordTrace]
  refine ⟨4348310628090038577520387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5797747504120051436693849 4348310628090038577520387)
  ·
    refine ⟨6522465942135057866280581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4348310628090038577520387 6522465942135057866280581)
    ·
      refine ⟨1222962364150323349927609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6522465942135057866280581 1222962364150323349927609)
      ·
        refine ⟨917221773112742512445707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1222962364150323349927609 917221773112742512445707)
        ·
          refine ⟨1375832659669113768668561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 917221773112742512445707 1375832659669113768668561)
          ·
            refine ⟨1031874494751835326501421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1375832659669113768668561 1031874494751835326501421)
            ·
              refine ⟨386952935531938247438033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1031874494751835326501421 386952935531938247438033)
              ·
                refine ⟨290214701648953685578525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 386952935531938247438033 290214701648953685578525)
                ·
                  refine ⟨108830513118357632091947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 290214701648953685578525 108830513118357632091947)
                  ·
                    rfl

theorem cell20_238440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2, 3].length) (baseStart_238440 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238440 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238440 prefixEnd_238440 := by exact prefixLift 238440
  have htrace : WordTrace (prefixWord ++ tailWord_238440) baseStart_238440 baseEnd_238440 := by
    simpa [prefixWord, tailWord_238440, baseEnd_238440] using wordTrace_append hprefix tailTrace_238440
  have hstable : (prefixWord ++ tailWord_238440).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238440).length < 2 ^ (prefixWord ++ tailWord_238440).sum := by decide
  have hdescent : baseEnd_238440 < baseStart_238440 := by decide
  rcases family_descends (prefixWord ++ tailWord_238440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238461 : List Nat := [1, 4, 1, 1, 2, 1, 2, 5, 3]
def baseStart_238461 : Nat := 118140960795 + 238461 * 2 ^ 59
def prefixEnd_238461 : Nat := 4983230072969 + 3 ^ 40 * 238461 * 2
def baseEnd_238461 : Nat := 108840098090574892391861

theorem tailTrace_238461 : CollatzResearch.WordTrace tailWord_238461 prefixEnd_238461 108840098090574892391861 := by
  unfold tailWord_238461
  simp only [CollatzResearch.WordTrace]
  refine ⟨8697387189103997741555237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5798258126069331827703491 8697387189103997741555237)
  ·
    refine ⟨1630760097956999576541607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8697387189103997741555237 1630760097956999576541607)
    ·
      refine ⟨2446140146935499364812411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1630760097956999576541607 2446140146935499364812411)
      ·
        refine ⟨3669210220403249047218617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2446140146935499364812411 3669210220403249047218617)
        ·
          refine ⟨2751907665302436785413963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3669210220403249047218617 2751907665302436785413963)
          ·
            refine ⟨4127861497953655178120945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2751907665302436785413963 4127861497953655178120945)
            ·
              refine ⟨3095896123465241383590709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4127861497953655178120945 3095896123465241383590709)
              ·
                refine ⟨290240261574866379711629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3095896123465241383590709 290240261574866379711629)
                ·
                  refine ⟨108840098090574892391861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 290240261574866379711629 108840098090574892391861)
                  ·
                    rfl

theorem cell20_238461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_238461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238461 prefixEnd_238461 := by exact prefixLift 238461
  have htrace : WordTrace (prefixWord ++ tailWord_238461) baseStart_238461 baseEnd_238461 := by
    simpa [prefixWord, tailWord_238461, baseEnd_238461] using wordTrace_append hprefix tailTrace_238461
  have hstable : (prefixWord ++ tailWord_238461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238461).length < 2 ^ (prefixWord ++ tailWord_238461).sum := by decide
  have hdescent : baseEnd_238461 < baseStart_238461 := by decide
  rcases family_descends (prefixWord ++ tailWord_238461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238471 : List Nat := [1, 1, 4, 2, 3, 3, 2, 4]
def baseStart_238471 : Nat := 118140960795 + 238471 * 2 ^ 59
def prefixEnd_238471 : Nat := 4983230072969 + 3 ^ 40 * 238471 * 2
def baseEnd_238471 : Nat := 36281554121019767352829

theorem tailTrace_238471 : CollatzResearch.WordTrace tailWord_238471 prefixEnd_238471 36281554121019767352829 := by
  unfold tailWord_238471
  simp only [CollatzResearch.WordTrace]
  refine ⟨8697751919067769449419267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5798501279378512966279511 8697751919067769449419267)
  ·
    refine ⟨13046627878601654174128901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8697751919067769449419267 13046627878601654174128901)
    ·
      refine ⟨2446242727237810157649169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13046627878601654174128901 2446242727237810157649169)
      ·
        refine ⟨1834682045428357618236877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2446242727237810157649169 1834682045428357618236877)
        ·
          refine ⟨688005767035634106838829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1834682045428357618236877 688005767035634106838829)
          ·
            refine ⟨258002162638362790064561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 688005767035634106838829 258002162638362790064561)
            ·
              refine ⟨193501621978772092548421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258002162638362790064561 193501621978772092548421)
              ·
                refine ⟨36281554121019767352829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 193501621978772092548421 36281554121019767352829)
                ·
                  rfl

theorem cell20_238471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 4].length) (baseStart_238471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238471 prefixEnd_238471 := by exact prefixLift 238471
  have htrace : WordTrace (prefixWord ++ tailWord_238471) baseStart_238471 baseEnd_238471 := by
    simpa [prefixWord, tailWord_238471, baseEnd_238471] using wordTrace_append hprefix tailTrace_238471
  have hstable : (prefixWord ++ tailWord_238471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238471).length < 2 ^ (prefixWord ++ tailWord_238471).sum := by decide
  have hdescent : baseEnd_238471 < baseStart_238471 := by decide
  rcases family_descends (prefixWord ++ tailWord_238471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238554 : List Nat := [3, 1, 1, 2, 4, 2, 2, 2, 3]
def baseStart_238554 : Nat := 118140960795 + 238554 * 2 ^ 59
def prefixEnd_238554 : Nat := 4983230072969 + 3 ^ 40 * 238554 * 2
def baseEnd_238554 : Nat := 108882545824679902291481

theorem tailTrace_238554 : CollatzResearch.WordTrace tailWord_238554 prefixEnd_238554 108882545824679902291481 := by
  unfold tailWord_238554
  simp only [CollatzResearch.WordTrace]
  refine ⟨2175194794441768656172679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5800519451844716416460477 2175194794441768656172679)
  ·
    refine ⟨3262792191662652984259019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2175194794441768656172679 3262792191662652984259019)
    ·
      refine ⟨4894188287493979476388529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3262792191662652984259019 4894188287493979476388529)
      ·
        refine ⟨3670641215620484607291397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4894188287493979476388529 3670641215620484607291397)
        ·
          refine ⟨688245227928840863867137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3670641215620484607291397 688245227928840863867137)
          ·
            refine ⟨516183920946630647900353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 688245227928840863867137 516183920946630647900353)
            ·
              refine ⟨387137940709972985925265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 516183920946630647900353 387137940709972985925265)
              ·
                refine ⟨290353455532479739443949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 387137940709972985925265 290353455532479739443949)
                ·
                  refine ⟨108882545824679902291481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 290353455532479739443949 108882545824679902291481)
                  ·
                    rfl

theorem cell20_238554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2, 3].length) (baseStart_238554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238554 prefixEnd_238554 := by exact prefixLift 238554
  have htrace : WordTrace (prefixWord ++ tailWord_238554) baseStart_238554 baseEnd_238554 := by
    simpa [prefixWord, tailWord_238554, baseEnd_238554] using wordTrace_append hprefix tailTrace_238554
  have hstable : (prefixWord ++ tailWord_238554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238554).length < 2 ^ (prefixWord ++ tailWord_238554).sum := by decide
  have hdescent : baseEnd_238554 < baseStart_238554 := by decide
  rcases family_descends (prefixWord ++ tailWord_238554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238557 : List Nat := [1, 4, 3, 1, 2, 1, 4, 2, 2]
def baseStart_238557 : Nat := 118140960795 + 238557 * 2 ^ 59
def prefixEnd_238557 : Nat := 4983230072969 + 3 ^ 40 * 238557 * 2
def baseEnd_238557 : Nat := 108883915106425225191469

theorem tailTrace_238557 : CollatzResearch.WordTrace tailWord_238557 prefixEnd_238557 108883915106425225191469 := by
  unfold tailWord_238557
  simp only [CollatzResearch.WordTrace]
  refine ⟨8700888596756206137049925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5800592397837470758033283 8700888596756206137049925)
  ·
    refine ⟨1631416611891788650696861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8700888596756206137049925 1631416611891788650696861)
    ·
      refine ⟨611781229459420744011323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1631416611891788650696861 611781229459420744011323)
      ·
        refine ⟨917671844189131116016985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 611781229459420744011323 917671844189131116016985)
        ·
          refine ⟨688253883141848337012739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 917671844189131116016985 688253883141848337012739)
          ·
            refine ⟨1032380824712772505519109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 688253883141848337012739 1032380824712772505519109)
            ·
              refine ⟨193571404633644844784833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1032380824712772505519109 193571404633644844784833)
              ·
                refine ⟨145178553475233633588625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193571404633644844784833 145178553475233633588625)
                ·
                  refine ⟨108883915106425225191469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145178553475233633588625 108883915106425225191469)
                  ·
                    rfl

theorem cell20_238557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 2, 2].length) (baseStart_238557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238557 prefixEnd_238557 := by exact prefixLift 238557
  have htrace : WordTrace (prefixWord ++ tailWord_238557) baseStart_238557 baseEnd_238557 := by
    simpa [prefixWord, tailWord_238557, baseEnd_238557] using wordTrace_append hprefix tailTrace_238557
  have hstable : (prefixWord ++ tailWord_238557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238557).length < 2 ^ (prefixWord ++ tailWord_238557).sum := by decide
  have hdescent : baseEnd_238557 < baseStart_238557 := by decide
  rcases family_descends (prefixWord ++ tailWord_238557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238575 : List Nat := [1, 1, 2, 1, 4, 3, 2, 3, 3]
def baseStart_238575 : Nat := 118140960795 + 238575 * 2 ^ 59
def prefixEnd_238575 : Nat := 4983230072969 + 3 ^ 40 * 238575 * 2
def baseEnd_238575 : Nat := 108892130796897162591395

theorem tailTrace_238575 : CollatzResearch.WordTrace tailWord_238575 prefixEnd_238575 108892130796897162591395 := by
  unfold tailWord_238575
  simp only [CollatzResearch.WordTrace]
  refine ⟨8701545110690995211205179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5801030073793996807470119 8701545110690995211205179)
  ·
    refine ⟨13052317666036492816807769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8701545110690995211205179 13052317666036492816807769)
    ·
      refine ⟨9789238249527369612605827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13052317666036492816807769 9789238249527369612605827)
      ·
        refine ⟨14683857374291054418908741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9789238249527369612605827 14683857374291054418908741)
        ·
          refine ⟨2753223257679572703545389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14683857374291054418908741 2753223257679572703545389)
          ·
            refine ⟨1032458721629839763829521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2753223257679572703545389 1032458721629839763829521)
            ·
              refine ⟨774344041222379822872141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1032458721629839763829521 774344041222379822872141)
              ·
                refine ⟨290379015458392433577053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 774344041222379822872141 290379015458392433577053)
                ·
                  refine ⟨108892130796897162591395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 290379015458392433577053 108892130796897162591395)
                  ·
                    rfl

theorem cell20_238575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3, 3].length) (baseStart_238575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238575 prefixEnd_238575 := by exact prefixLift 238575
  have htrace : WordTrace (prefixWord ++ tailWord_238575) baseStart_238575 baseEnd_238575 := by
    simpa [prefixWord, tailWord_238575, baseEnd_238575] using wordTrace_append hprefix tailTrace_238575
  have hstable : (prefixWord ++ tailWord_238575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238575).length < 2 ^ (prefixWord ++ tailWord_238575).sum := by decide
  have hdescent : baseEnd_238575 < baseStart_238575 := by decide
  rcases family_descends (prefixWord ++ tailWord_238575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238578 : List Nat := [3, 2, 1, 5, 1, 1, 1, 2, 4]
def baseStart_238578 : Nat := 118140960795 + 238578 * 2 ^ 59
def prefixEnd_238578 : Nat := 4983230072969 + 3 ^ 40 * 238578 * 2
def baseEnd_238578 : Nat := 108893500078642485491383

theorem tailTrace_238578 : CollatzResearch.WordTrace tailWord_238578 prefixEnd_238578 108893500078642485491383 := by
  unfold tailWord_238578
  simp only [CollatzResearch.WordTrace]
  refine ⟨2175413632420031680891097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5801103019786751149042925 2175413632420031680891097)
  ·
    refine ⟨1631560224315023760668323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2175413632420031680891097 1631560224315023760668323)
    ·
      refine ⟨2447340336472535641002485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1631560224315023760668323 2447340336472535641002485)
      ·
        refine ⟨229438156544300216343983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2447340336472535641002485 229438156544300216343983)
        ·
          refine ⟨344157234816450324515975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229438156544300216343983 344157234816450324515975)
          ·
            refine ⟨516235852224675486773963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344157234816450324515975 516235852224675486773963)
            ·
              refine ⟨774353778337013230160945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 516235852224675486773963 774353778337013230160945)
              ·
                refine ⟨580765333752759922620709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 774353778337013230160945 580765333752759922620709)
                ·
                  refine ⟨108893500078642485491383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 580765333752759922620709 108893500078642485491383)
                  ·
                    rfl

theorem cell20_238578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_238578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238578 prefixEnd_238578 := by exact prefixLift 238578
  have htrace : WordTrace (prefixWord ++ tailWord_238578) baseStart_238578 baseEnd_238578 := by
    simpa [prefixWord, tailWord_238578, baseEnd_238578] using wordTrace_append hprefix tailTrace_238578
  have hstable : (prefixWord ++ tailWord_238578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238578).length < 2 ^ (prefixWord ++ tailWord_238578).sum := by decide
  have hdescent : baseEnd_238578 < baseStart_238578 := by decide
  rcases family_descends (prefixWord ++ tailWord_238578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238613 : List Nat := [1, 3, 2, 1, 4, 2, 1, 1, 5]
def baseStart_238613 : Nat := 118140960795 + 238613 * 2 ^ 59
def prefixEnd_238613 : Nat := 4983230072969 + 3 ^ 40 * 238613 * 2
def baseEnd_238613 : Nat := 108909475032337919324573

theorem tailTrace_238613 : CollatzResearch.WordTrace tailWord_238613 prefixEnd_238613 108909475032337919324573 := by
  unfold tailWord_238613
  simp only [CollatzResearch.WordTrace]
  refine ⟨8702931084553327701088493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5801954056368885134058995 8702931084553327701088493)
  ·
    refine ⟨3263599156707497887908185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8702931084553327701088493 3263599156707497887908185)
    ·
      refine ⟨2447699367530623415931139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3263599156707497887908185 2447699367530623415931139)
      ·
        refine ⟨3671549051295935123896709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2447699367530623415931139 3671549051295935123896709)
        ·
          refine ⟨688415447117987835730633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3671549051295935123896709 688415447117987835730633)
          ·
            refine ⟨516311585338490876797975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 688415447117987835730633 516311585338490876797975)
            ·
              refine ⟨774467378007736315196963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 516311585338490876797975 774467378007736315196963)
              ·
                refine ⟨1161701067011604472795445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 774467378007736315196963 1161701067011604472795445)
                ·
                  refine ⟨108909475032337919324573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1161701067011604472795445 108909475032337919324573)
                  ·
                    rfl

theorem cell20_238613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_238613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238613 prefixEnd_238613 := by exact prefixLift 238613
  have htrace : WordTrace (prefixWord ++ tailWord_238613) baseStart_238613 baseEnd_238613 := by
    simpa [prefixWord, tailWord_238613, baseEnd_238613] using wordTrace_append hprefix tailTrace_238613
  have hstable : (prefixWord ++ tailWord_238613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238613).length < 2 ^ (prefixWord ++ tailWord_238613).sum := by decide
  have hdescent : baseEnd_238613 < baseStart_238613 := by decide
  rcases family_descends (prefixWord ++ tailWord_238613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238678 : List Nat := [5, 2, 2, 1, 2, 1, 2, 5]
def baseStart_238678 : Nat := 118140960795 + 238678 * 2 ^ 59
def prefixEnd_238678 : Nat := 4983230072969 + 3 ^ 40 * 238678 * 2
def baseEnd_238678 : Nat := 36313047601162194052547

theorem tailTrace_238678 : CollatzResearch.WordTrace tailWord_238678 prefixEnd_238678 36313047601162194052547 := by
  unfold tailWord_238678
  simp only [CollatzResearch.WordTrace]
  refine ⟨544081364332365237637793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5803534552878562534803125 544081364332365237637793)
  ·
    refine ⟨408061023249273928228345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 544081364332365237637793 408061023249273928228345)
    ·
      refine ⟨306045767436955446171259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408061023249273928228345 306045767436955446171259)
      ·
        refine ⟨459068651155433169256889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306045767436955446171259 459068651155433169256889)
        ·
          refine ⟨344301488366574876942667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 459068651155433169256889 344301488366574876942667)
          ·
            refine ⟨516452232549862315414001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344301488366574876942667 516452232549862315414001)
            ·
              refine ⟨387339174412396736560501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 516452232549862315414001 387339174412396736560501)
              ·
                refine ⟨36313047601162194052547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 387339174412396736560501 36313047601162194052547)
                ·
                  rfl

theorem cell20_238678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_238678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238678 prefixEnd_238678 := by exact prefixLift 238678
  have htrace : WordTrace (prefixWord ++ tailWord_238678) baseStart_238678 baseEnd_238678 := by
    simpa [prefixWord, tailWord_238678, baseEnd_238678] using wordTrace_append hprefix tailTrace_238678
  have hstable : (prefixWord ++ tailWord_238678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238678).length < 2 ^ (prefixWord ++ tailWord_238678).sum := by decide
  have hdescent : baseEnd_238678 < baseStart_238678 := by decide
  rcases family_descends (prefixWord ++ tailWord_238678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238685 : List Nat := [1, 4, 4, 1, 2, 1, 1, 3, 3]
def baseStart_238685 : Nat := 118140960795 + 238685 * 2 ^ 59
def prefixEnd_238685 : Nat := 4983230072969 + 3 ^ 40 * 238685 * 2
def baseEnd_238685 : Nat := 108942337794225668924279

theorem tailTrace_238685 : CollatzResearch.WordTrace tailWord_238685 prefixEnd_238685 108942337794225668924279 := by
  unfold tailWord_238685
  simp only [CollatzResearch.WordTrace]
  refine ⟨8705557140292483997709509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5803704760194989331806339 8705557140292483997709509)
  ·
    refine ⟨1632291963804840749570533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8705557140292483997709509 1632291963804840749570533)
    ·
      refine ⟨306054743213407640544475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1632291963804840749570533 306054743213407640544475)
      ·
        refine ⟨459082114820111460816713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306054743213407640544475 459082114820111460816713)
        ·
          refine ⟨344311586115083595612535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 459082114820111460816713 344311586115083595612535)
          ·
            refine ⟨516467379172625393418803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344311586115083595612535 516467379172625393418803)
            ·
              refine ⟨774701068758938090128205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 516467379172625393418803 774701068758938090128205)
              ·
                refine ⟨290512900784601783798077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 774701068758938090128205 290512900784601783798077)
                ·
                  refine ⟨108942337794225668924279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 290512900784601783798077 108942337794225668924279)
                  ·
                    rfl

theorem cell20_238685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_238685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238685 prefixEnd_238685 := by exact prefixLift 238685
  have htrace : WordTrace (prefixWord ++ tailWord_238685) baseStart_238685 baseEnd_238685 := by
    simpa [prefixWord, tailWord_238685, baseEnd_238685] using wordTrace_append hprefix tailTrace_238685
  have hstable : (prefixWord ++ tailWord_238685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238685).length < 2 ^ (prefixWord ++ tailWord_238685).sum := by decide
  have hdescent : baseEnd_238685 < baseStart_238685 := by decide
  rcases family_descends (prefixWord ++ tailWord_238685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238751 : List Nat := [1, 1, 2, 6, 2, 1, 1, 2, 4]
def baseStart_238751 : Nat := 118140960795 + 238751 * 2 ^ 59
def prefixEnd_238751 : Nat := 4983230072969 + 3 ^ 40 * 238751 * 2
def baseEnd_238751 : Nat := 108972461992622772724009

theorem tailTrace_238751 : CollatzResearch.WordTrace tailWord_238751 prefixEnd_238751 108972461992622772724009 := by
  unfold tailWord_238751
  simp only [CollatzResearch.WordTrace]
  refine ⟨8707964358053377269612107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5805309572035584846408071 8707964358053377269612107)
  ·
    refine ⟨13061946537080065904418161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8707964358053377269612107 13061946537080065904418161)
    ·
      refine ⟨9796459902810049428313621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13061946537080065904418161 9796459902810049428313621)
      ·
        refine ⟨459209057944221066952201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9796459902810049428313621 459209057944221066952201)
        ·
          refine ⟨344406793458165800214151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 459209057944221066952201 344406793458165800214151)
          ·
            refine ⟨516610190187248700321227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344406793458165800214151 516610190187248700321227)
            ·
              refine ⟨774915285280873050481841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 516610190187248700321227 774915285280873050481841)
              ·
                refine ⟨581186463960654787861381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 774915285280873050481841 581186463960654787861381)
                ·
                  refine ⟨108972461992622772724009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 581186463960654787861381 108972461992622772724009)
                  ·
                    rfl

theorem cell20_238751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 4].length) (baseStart_238751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238751 prefixEnd_238751 := by exact prefixLift 238751
  have htrace : WordTrace (prefixWord ++ tailWord_238751) baseStart_238751 baseEnd_238751 := by
    simpa [prefixWord, tailWord_238751, baseEnd_238751] using wordTrace_append hprefix tailTrace_238751
  have hstable : (prefixWord ++ tailWord_238751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238751).length < 2 ^ (prefixWord ++ tailWord_238751).sum := by decide
  have hdescent : baseEnd_238751 < baseStart_238751 := by decide
  rcases family_descends (prefixWord ++ tailWord_238751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238782 : List Nat := [4, 2, 1, 1, 3, 1, 3, 2, 3]
def baseStart_238782 : Nat := 118140960795 + 238782 * 2 ^ 59
def prefixEnd_238782 : Nat := 4983230072969 + 3 ^ 40 * 238782 * 2
def baseEnd_238782 : Nat := 108986611237324442690549

theorem tailTrace_238782 : CollatzResearch.WordTrace tailWord_238782 prefixEnd_238782 108986611237324442690549 := by
  unfold tailWord_238782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1088636877617633695498825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5806063347294046375993733 1088636877617633695498825)
  ·
    refine ⟨816477658213225271624119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1088636877617633695498825 816477658213225271624119)
    ·
      refine ⟨1224716487319837907436179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 816477658213225271624119 1224716487319837907436179)
      ·
        refine ⟨1837074730979756861154269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1224716487319837907436179 1837074730979756861154269)
        ·
          refine ⟨688903024117408822932851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1837074730979756861154269 688903024117408822932851)
          ·
            refine ⟨1033354536176113234399277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 688903024117408822932851 1033354536176113234399277)
            ·
              refine ⟨387507951066042462899729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1033354536176113234399277 387507951066042462899729)
              ·
                refine ⟨290630963299531847174797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 387507951066042462899729 290630963299531847174797)
                ·
                  refine ⟨108986611237324442690549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 290630963299531847174797 108986611237324442690549)
                  ·
                    rfl

theorem cell20_238782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_238782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238782 prefixEnd_238782 := by exact prefixLift 238782
  have htrace : WordTrace (prefixWord ++ tailWord_238782) baseStart_238782 baseEnd_238782 := by
    simpa [prefixWord, tailWord_238782, baseEnd_238782] using wordTrace_append hprefix tailTrace_238782
  have hstable : (prefixWord ++ tailWord_238782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238782).length < 2 ^ (prefixWord ++ tailWord_238782).sum := by decide
  have hdescent : baseEnd_238782 < baseStart_238782 := by decide
  rcases family_descends (prefixWord ++ tailWord_238782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238817 : List Nat := [1, 2, 3, 1, 3, 3, 1, 6]
def baseStart_238817 : Nat := 118140960795 + 238817 * 2 ^ 59
def prefixEnd_238817 : Nat := 4983230072969 + 3 ^ 40 * 238817 * 2
def baseEnd_238817 : Nat := 36334195397006625507913

theorem tailTrace_238817 : CollatzResearch.WordTrace tailWord_238817 prefixEnd_238817 36334195397006625507913 := by
  unfold tailWord_238817
  simp only [CollatzResearch.WordTrace]
  refine ⟨8710371575814270541514705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5806914383876180361009803 8710371575814270541514705)
  ·
    refine ⟨6532778681860702906136029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8710371575814270541514705 6532778681860702906136029)
    ·
      refine ⟨2449792005697763589801011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6532778681860702906136029 2449792005697763589801011)
      ·
        refine ⟨3674688008546645384701517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2449792005697763589801011 3674688008546645384701517)
        ·
          refine ⟨1378008003204992019263069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3674688008546645384701517 1378008003204992019263069)
          ·
            refine ⟨516753001201872007223651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1378008003204992019263069 516753001201872007223651)
            ·
              refine ⟨775129501802808010835477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 516753001201872007223651 775129501802808010835477)
              ·
                refine ⟨36334195397006625507913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 775129501802808010835477 36334195397006625507913)
                ·
                  rfl

theorem cell20_238817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 6].length) (baseStart_238817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238817 prefixEnd_238817 := by exact prefixLift 238817
  have htrace : WordTrace (prefixWord ++ tailWord_238817) baseStart_238817 baseEnd_238817 := by
    simpa [prefixWord, tailWord_238817, baseEnd_238817] using wordTrace_append hprefix tailTrace_238817
  have hstable : (prefixWord ++ tailWord_238817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238817).length < 2 ^ (prefixWord ++ tailWord_238817).sum := by decide
  have hdescent : baseEnd_238817 < baseStart_238817 := by decide
  rcases family_descends (prefixWord ++ tailWord_238817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238823 : List Nat := [1, 1, 5, 3, 2, 2, 1, 3, 2]
def baseStart_238823 : Nat := 118140960795 + 238823 * 2 ^ 59
def prefixEnd_238823 : Nat := 4983230072969 + 3 ^ 40 * 238823 * 2
def baseEnd_238823 : Nat := 109005324754510522323715

theorem tailTrace_238823 : CollatzResearch.WordTrace tailWord_238823 prefixEnd_238823 109005324754510522323715 := by
  unfold tailWord_238823
  simp only [CollatzResearch.WordTrace]
  refine ⟨8710590413792533566233123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5807060275861689044155415 8710590413792533566233123)
  ·
    refine ⟨13065885620688800349349685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8710590413792533566233123 13065885620688800349349685)
    ·
      refine ⟨1224926776939575032751533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13065885620688800349349685 1224926776939575032751533)
      ·
        refine ⟨459347541352340637281825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1224926776939575032751533 459347541352340637281825)
        ·
          refine ⟨344510656014255477961369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 459347541352340637281825 344510656014255477961369)
          ·
            refine ⟨258382992010691608471027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344510656014255477961369 258382992010691608471027)
            ·
              refine ⟨387574488016037412706541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258382992010691608471027 387574488016037412706541)
              ·
                refine ⟨145340433006014029764953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 387574488016037412706541 145340433006014029764953)
                ·
                  refine ⟨109005324754510522323715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145340433006014029764953 109005324754510522323715)
                  ·
                    rfl

theorem cell20_238823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 3, 2].length) (baseStart_238823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238823 prefixEnd_238823 := by exact prefixLift 238823
  have htrace : WordTrace (prefixWord ++ tailWord_238823) baseStart_238823 baseEnd_238823 := by
    simpa [prefixWord, tailWord_238823, baseEnd_238823] using wordTrace_append hprefix tailTrace_238823
  have hstable : (prefixWord ++ tailWord_238823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238823).length < 2 ^ (prefixWord ++ tailWord_238823).sum := by decide
  have hdescent : baseEnd_238823 < baseStart_238823 := by decide
  rcases family_descends (prefixWord ++ tailWord_238823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238824 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 7]
def baseStart_238824 : Nat := 118140960795 + 238824 * 2 ^ 59
def prefixEnd_238824 : Nat := 4983230072969 + 3 ^ 40 * 238824 * 2
def baseEnd_238824 : Nat := 109005781181758963290377

theorem tailTrace_238824 : CollatzResearch.WordTrace tailWord_238824 prefixEnd_238824 109005781181758963290377 := by
  unfold tailWord_238824
  simp only [CollatzResearch.WordTrace]
  refine ⟨4355313443394455368509763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5807084591192607158013017 4355313443394455368509763)
  ·
    refine ⟨6532970165091683052764645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4355313443394455368509763 6532970165091683052764645)
    ·
      refine ⟨1224931905954690572393371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6532970165091683052764645 1224931905954690572393371)
      ·
        refine ⟨1837397858932035858590057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1224931905954690572393371 1837397858932035858590057)
        ·
          refine ⟨1378048394199026893942543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1837397858932035858590057 1378048394199026893942543)
          ·
            refine ⟨2067072591298540340913815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1378048394199026893942543 2067072591298540340913815)
            ·
              refine ⟨3100608886947810511370723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2067072591298540340913815 3100608886947810511370723)
              ·
                refine ⟨4650913330421715767056085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3100608886947810511370723 4650913330421715767056085)
                ·
                  refine ⟨109005781181758963290377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4650913330421715767056085 109005781181758963290377)
                  ·
                    rfl

theorem cell20_238824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_238824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238824 prefixEnd_238824 := by exact prefixLift 238824
  have htrace : WordTrace (prefixWord ++ tailWord_238824) baseStart_238824 baseEnd_238824 := by
    simpa [prefixWord, tailWord_238824, baseEnd_238824] using wordTrace_append hprefix tailTrace_238824
  have hstable : (prefixWord ++ tailWord_238824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238824).length < 2 ^ (prefixWord ++ tailWord_238824).sum := by decide
  have hdescent : baseEnd_238824 < baseStart_238824 := by decide
  rcases family_descends (prefixWord ++ tailWord_238824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238827 : List Nat := [1, 1, 1, 1, 2, 6, 3, 3, 2]
def baseStart_238827 : Nat := 118140960795 + 238827 * 2 ^ 59
def prefixEnd_238827 : Nat := 4983230072969 + 3 ^ 40 * 238827 * 2
def baseEnd_238827 : Nat := 109007150463504286190365

theorem tailTrace_238827 : CollatzResearch.WordTrace tailWord_238827 prefixEnd_238827 109007150463504286190365 := by
  unfold tailWord_238827
  simp only [CollatzResearch.WordTrace]
  refine ⟨8710736305778042249378735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5807157537185361499585823 8710736305778042249378735)
  ·
    refine ⟨13066104458667063374068103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8710736305778042249378735 13066104458667063374068103)
    ·
      refine ⟨19599156688000595061102155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13066104458667063374068103 19599156688000595061102155)
      ·
        refine ⟨29398735032000892591653233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19599156688000595061102155 29398735032000892591653233)
        ·
          refine ⟨22049051274000669443739925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29398735032000892591653233 22049051274000669443739925)
          ·
            refine ⟨1033549278468781380175309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22049051274000669443739925 1033549278468781380175309)
            ·
              refine ⟨387580979425793017565741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1033549278468781380175309 387580979425793017565741)
              ·
                refine ⟨145342867284672381587153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 387580979425793017565741 145342867284672381587153)
                ·
                  refine ⟨109007150463504286190365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145342867284672381587153 109007150463504286190365)
                  ·
                    rfl

theorem cell20_238827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 3, 2].length) (baseStart_238827 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238827 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238827 prefixEnd_238827 := by exact prefixLift 238827
  have htrace : WordTrace (prefixWord ++ tailWord_238827) baseStart_238827 baseEnd_238827 := by
    simpa [prefixWord, tailWord_238827, baseEnd_238827] using wordTrace_append hprefix tailTrace_238827
  have hstable : (prefixWord ++ tailWord_238827).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238827).length < 2 ^ (prefixWord ++ tailWord_238827).sum := by decide
  have hdescent : baseEnd_238827 < baseStart_238827 := by decide
  rcases family_descends (prefixWord ++ tailWord_238827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238834 : List Nat := [3, 2, 1, 3, 3, 2, 6]
def baseStart_238834 : Nat := 118140960795 + 238834 * 2 ^ 59
def prefixEnd_238834 : Nat := 4983230072969 + 3 ^ 40 * 238834 * 2
def baseEnd_238834 : Nat := 12112260606027041439667

theorem tailTrace_238834 : CollatzResearch.WordTrace tailWord_238834 prefixEnd_238834 12112260606027041439667 := by
  unfold tailWord_238834
  simp only [CollatzResearch.WordTrace]
  refine ⟨2177747904188170611220889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5807327744501788296589037 2177747904188170611220889)
  ·
    refine ⟨1633310928141127958415667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2177747904188170611220889 1633310928141127958415667)
    ·
      refine ⟨2449966392211691937623501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1633310928141127958415667 2449966392211691937623501)
      ·
        refine ⟨918737397079384476608813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2449966392211691937623501 918737397079384476608813)
        ·
          refine ⟨344526523904769178728305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 918737397079384476608813 344526523904769178728305)
          ·
            refine ⟨258394892928576884046229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344526523904769178728305 258394892928576884046229)
            ·
              refine ⟨12112260606027041439667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 258394892928576884046229 12112260606027041439667)
              ·
                rfl

theorem cell20_238834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 6].length) (baseStart_238834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238834 prefixEnd_238834 := by exact prefixLift 238834
  have htrace : WordTrace (prefixWord ++ tailWord_238834) baseStart_238834 baseEnd_238834 := by
    simpa [prefixWord, tailWord_238834, baseEnd_238834] using wordTrace_append hprefix tailTrace_238834
  have hstable : (prefixWord ++ tailWord_238834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238834).length < 2 ^ (prefixWord ++ tailWord_238834).sum := by decide
  have hdescent : baseEnd_238834 < baseStart_238834 := by decide
  rcases family_descends (prefixWord ++ tailWord_238834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238844 : List Nat := [2, 2, 2, 1, 6, 1, 1, 1, 4]
def baseStart_238844 : Nat := 118140960795 + 238844 * 2 ^ 59
def prefixEnd_238844 : Nat := 4983230072969 + 3 ^ 40 * 238844 * 2
def baseEnd_238844 : Nat := 109014909726727782623629

theorem tailTrace_238844 : CollatzResearch.WordTrace tailWord_238844 prefixEnd_238844 109014909726727782623629 := by
  unfold tailWord_238844
  simp only [CollatzResearch.WordTrace]
  refine ⟨4355678173358227076373793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5807570897810969435165057 4355678173358227076373793)
  ·
    refine ⟨3266758630018670307280345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4355678173358227076373793 3266758630018670307280345)
    ·
      refine ⟨2450068972514002730460259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3266758630018670307280345 2450068972514002730460259)
      ·
        refine ⟨3675103458771004095690389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2450068972514002730460259 3675103458771004095690389)
        ·
          refine ⟨172270474629890816985487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3675103458771004095690389 172270474629890816985487)
          ·
            refine ⟨258405711944836225478231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172270474629890816985487 258405711944836225478231)
            ·
              refine ⟨387608567917254338217347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258405711944836225478231 387608567917254338217347)
              ·
                refine ⟨581412851875881507326021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 387608567917254338217347 581412851875881507326021)
                ·
                  refine ⟨109014909726727782623629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 581412851875881507326021 109014909726727782623629)
                  ·
                    rfl

theorem cell20_238844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 4].length) (baseStart_238844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238844 prefixEnd_238844 := by exact prefixLift 238844
  have htrace : WordTrace (prefixWord ++ tailWord_238844) baseStart_238844 baseEnd_238844 := by
    simpa [prefixWord, tailWord_238844, baseEnd_238844] using wordTrace_append hprefix tailTrace_238844
  have hstable : (prefixWord ++ tailWord_238844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238844).length < 2 ^ (prefixWord ++ tailWord_238844).sum := by decide
  have hdescent : baseEnd_238844 < baseStart_238844 := by decide
  rcases family_descends (prefixWord ++ tailWord_238844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238869 : List Nat := [1, 3, 2, 1, 2, 1, 1, 3, 6]
def baseStart_238869 : Nat := 118140960795 + 238869 * 2 ^ 59
def prefixEnd_238869 : Nat := 4983230072969 + 3 ^ 40 * 238869 * 2
def baseEnd_238869 : Nat := 109026320407938806790193

theorem tailTrace_238869 : CollatzResearch.WordTrace tailWord_238869 prefixEnd_238869 109026320407938806790193 := by
  unfold tailWord_238869
  simp only [CollatzResearch.WordTrace]
  refine ⟨8712268171625883422407661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5808178781083922281605107 8712268171625883422407661)
  ·
    refine ⟨3267100564359706283402873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8712268171625883422407661 3267100564359706283402873)
    ·
      refine ⟨2450325423269779712552155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3267100564359706283402873 2450325423269779712552155)
      ·
        refine ⟨3675488134904669568828233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2450325423269779712552155 3675488134904669568828233)
        ·
          refine ⟨2756616101178502176621175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3675488134904669568828233 2756616101178502176621175)
          ·
            refine ⟨4134924151767753264931763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2756616101178502176621175 4134924151767753264931763)
            ·
              refine ⟨6202386227651629897397645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4134924151767753264931763 6202386227651629897397645)
              ·
                refine ⟨2325894835369361211524117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6202386227651629897397645 2325894835369361211524117)
                ·
                  refine ⟨109026320407938806790193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2325894835369361211524117 109026320407938806790193)
                  ·
                    rfl

theorem cell20_238869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_238869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238869 prefixEnd_238869 := by exact prefixLift 238869
  have htrace : WordTrace (prefixWord ++ tailWord_238869) baseStart_238869 baseEnd_238869 := by
    simpa [prefixWord, tailWord_238869, baseEnd_238869] using wordTrace_append hprefix tailTrace_238869
  have hstable : (prefixWord ++ tailWord_238869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238869).length < 2 ^ (prefixWord ++ tailWord_238869).sum := by decide
  have hdescent : baseEnd_238869 < baseStart_238869 := by decide
  rcases family_descends (prefixWord ++ tailWord_238869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238924 : List Nat := [2, 2, 1, 3, 2, 3, 1, 2, 4]
def baseStart_238924 : Nat := 118140960795 + 238924 * 2 ^ 59
def prefixEnd_238924 : Nat := 4983230072969 + 3 ^ 40 * 238924 * 2
def baseEnd_238924 : Nat := 109051423906603059956635

theorem tailTrace_238924 : CollatzResearch.WordTrace tailWord_238924 prefixEnd_238924 109051423906603059956635 := by
  unfold tailWord_238924
  simp only [CollatzResearch.WordTrace]
  refine ⟨4357137093213313907829913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5809516124284418543773217 4357137093213313907829913)
  ·
    refine ⟨3267852819909985430872435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4357137093213313907829913 3267852819909985430872435)
    ·
      refine ⟨4901779229864978146308653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3267852819909985430872435 4901779229864978146308653)
      ·
        refine ⟨1838167211199366804865745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4901779229864978146308653 1838167211199366804865745)
        ·
          refine ⟨1378625408399525103649309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1838167211199366804865745 1378625408399525103649309)
          ·
            refine ⟨516984528149821913868491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1378625408399525103649309 516984528149821913868491)
            ·
              refine ⟨775476792224732870802737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 516984528149821913868491 775476792224732870802737)
              ·
                refine ⟨581607594168549653102053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 775476792224732870802737 581607594168549653102053)
                ·
                  refine ⟨109051423906603059956635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 581607594168549653102053 109051423906603059956635)
                  ·
                    rfl

theorem cell20_238924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_238924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238924 prefixEnd_238924 := by exact prefixLift 238924
  have htrace : WordTrace (prefixWord ++ tailWord_238924) baseStart_238924 baseEnd_238924 := by
    simpa [prefixWord, tailWord_238924, baseEnd_238924] using wordTrace_append hprefix tailTrace_238924
  have hstable : (prefixWord ++ tailWord_238924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238924).length < 2 ^ (prefixWord ++ tailWord_238924).sum := by decide
  have hdescent : baseEnd_238924 < baseStart_238924 := by decide
  rcases family_descends (prefixWord ++ tailWord_238924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238931 : List Nat := [1, 1, 1, 2, 1, 1, 9, 4]
def baseStart_238931 : Nat := 118140960795 + 238931 * 2 ^ 59
def prefixEnd_238931 : Nat := 4983230072969 + 3 ^ 40 * 238931 * 2
def baseEnd_238931 : Nat := 36351539632447382241091

theorem tailTrace_238931 : CollatzResearch.WordTrace tailWord_238931 prefixEnd_238931 36351539632447382241091 := by
  unfold tailWord_238931
  simp only [CollatzResearch.WordTrace]
  refine ⟨8714529497401268011164647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5809686331600845340776431 8714529497401268011164647)
  ·
    refine ⟨13071794246101902016746971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8714529497401268011164647 13071794246101902016746971)
    ·
      refine ⟨19607691369152853025120457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13071794246101902016746971 19607691369152853025120457)
      ·
        refine ⟨14705768526864639768840343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19607691369152853025120457 14705768526864639768840343)
        ·
          refine ⟨22058652790296959653260515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14705768526864639768840343 22058652790296959653260515)
          ·
            refine ⟨33087979185445439479890773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22058652790296959653260515 33087979185445439479890773)
            ·
              refine ⟨193874878039719371952485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 33087979185445439479890773 193874878039719371952485)
              ·
                refine ⟨36351539632447382241091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 193874878039719371952485 36351539632447382241091)
                ·
                  rfl

theorem cell20_238931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 4].length) (baseStart_238931 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238931 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238931 prefixEnd_238931 := by exact prefixLift 238931
  have htrace : WordTrace (prefixWord ++ tailWord_238931) baseStart_238931 baseEnd_238931 := by
    simpa [prefixWord, tailWord_238931, baseEnd_238931] using wordTrace_append hprefix tailTrace_238931
  have hstable : (prefixWord ++ tailWord_238931).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238931).length < 2 ^ (prefixWord ++ tailWord_238931).sum := by decide
  have hdescent : baseEnd_238931 < baseStart_238931 := by decide
  rcases family_descends (prefixWord ++ tailWord_238931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238951 : List Nat := [1, 1, 5, 1, 5, 1, 1, 2, 3]
def baseStart_238951 : Nat := 118140960795 + 238951 * 2 ^ 59
def prefixEnd_238951 : Nat := 4983230072969 + 3 ^ 40 * 238951 * 2
def baseEnd_238951 : Nat := 109063747442310966056525

theorem tailTrace_238951 : CollatzResearch.WordTrace tailWord_238951 prefixEnd_238951 109063747442310966056525 := by
  unfold tailWord_238951
  simp only [CollatzResearch.WordTrace]
  refine ⟨8715258957328811426892707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5810172638219207617928471 8715258957328811426892707)
  ·
    refine ⟨13072888435993217140339061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8715258957328811426892707 13072888435993217140339061)
    ·
      refine ⟨1225583290874364106906787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13072888435993217140339061 1225583290874364106906787)
      ·
        refine ⟨1838374936311546160360181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1225583290874364106906787 1838374936311546160360181)
        ·
          refine ⟨172347650279207452533767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1838374936311546160360181 172347650279207452533767)
          ·
            refine ⟨258521475418811178800651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172347650279207452533767 258521475418811178800651)
            ·
              refine ⟨387782213128216768200977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258521475418811178800651 387782213128216768200977)
              ·
                refine ⟨290836659846162576150733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 387782213128216768200977 290836659846162576150733)
                ·
                  refine ⟨109063747442310966056525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 290836659846162576150733 109063747442310966056525)
                  ·
                    rfl

theorem cell20_238951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 2, 3].length) (baseStart_238951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238951 prefixEnd_238951 := by exact prefixLift 238951
  have htrace : WordTrace (prefixWord ++ tailWord_238951) baseStart_238951 baseEnd_238951 := by
    simpa [prefixWord, tailWord_238951, baseEnd_238951] using wordTrace_append hprefix tailTrace_238951
  have hstable : (prefixWord ++ tailWord_238951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238951).length < 2 ^ (prefixWord ++ tailWord_238951).sum := by decide
  have hdescent : baseEnd_238951 < baseStart_238951 := by decide
  rcases family_descends (prefixWord ++ tailWord_238951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238958 : List Nat := [4, 1, 2, 4, 1, 1, 2, 1, 4]
def baseStart_238958 : Nat := 118140960795 + 238958 * 2 ^ 59
def prefixEnd_238958 : Nat := 4983230072969 + 3 ^ 40 * 238958 * 2
def baseEnd_238958 : Nat := 109066942433050052823163

theorem tailTrace_238958 : CollatzResearch.WordTrace tailWord_238958 prefixEnd_238958 109066942433050052823163 := by
  unfold tailWord_238958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1089439283537931452799691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5810342845535634414931685 1089439283537931452799691)
  ·
    refine ⟨1634158925306897179199537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1089439283537931452799691 1634158925306897179199537)
    ·
      refine ⟨1225619193980172884399653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1634158925306897179199537 1225619193980172884399653)
      ·
        refine ⟨229803598871282415824935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1225619193980172884399653 229803598871282415824935)
        ·
          refine ⟨344705398306923623737403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229803598871282415824935 344705398306923623737403)
          ·
            refine ⟨517058097460385435606105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344705398306923623737403 517058097460385435606105)
            ·
              refine ⟨387793573095289076704579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 517058097460385435606105 387793573095289076704579)
              ·
                refine ⟨581690359642933615056869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 387793573095289076704579 581690359642933615056869)
                ·
                  refine ⟨109066942433050052823163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 581690359642933615056869 109066942433050052823163)
                  ·
                    rfl

theorem cell20_238958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_238958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238958 prefixEnd_238958 := by exact prefixLift 238958
  have htrace : WordTrace (prefixWord ++ tailWord_238958) baseStart_238958 baseEnd_238958 := by
    simpa [prefixWord, tailWord_238958, baseEnd_238958] using wordTrace_append hprefix tailTrace_238958
  have hstable : (prefixWord ++ tailWord_238958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238958).length < 2 ^ (prefixWord ++ tailWord_238958).sum := by decide
  have hdescent : baseEnd_238958 < baseStart_238958 := by decide
  rcases family_descends (prefixWord ++ tailWord_238958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238962 : List Nat := [3, 2, 1, 2, 1, 2, 4, 1, 4]
def baseStart_238962 : Nat := 118140960795 + 238962 * 2 ^ 59
def prefixEnd_238962 : Nat := 4983230072969 + 3 ^ 40 * 238962 * 2
def baseEnd_238962 : Nat := 109068768142043816689813

theorem tailTrace_238962 : CollatzResearch.WordTrace tailWord_238962 prefixEnd_238962 109068768142043816689813 := by
  unfold tailWord_238962
  simp only [CollatzResearch.WordTrace]
  refine ⟨2178915040072240076385785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5810440106859306870362093 2178915040072240076385785)
  ·
    refine ⟨1634186280054180057289339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2178915040072240076385785 1634186280054180057289339)
    ·
      refine ⟨2451279420081270085934009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1634186280054180057289339 2451279420081270085934009)
      ·
        refine ⟨1838459565060952564450507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2451279420081270085934009 1838459565060952564450507)
        ·
          refine ⟨2757689347591428846675761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1838459565060952564450507 2757689347591428846675761)
          ·
            refine ⟨2068267010693571635006821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2757689347591428846675761 2068267010693571635006821)
            ·
              refine ⟨387800064505044681563779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2068267010693571635006821 387800064505044681563779)
              ·
                refine ⟨581700096757567022345669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 387800064505044681563779 581700096757567022345669)
                ·
                  refine ⟨109068768142043816689813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 581700096757567022345669 109068768142043816689813)
                  ·
                    rfl

theorem cell20_238962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_238962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238962 prefixEnd_238962 := by exact prefixLift 238962
  have htrace : WordTrace (prefixWord ++ tailWord_238962) baseStart_238962 baseEnd_238962 := by
    simpa [prefixWord, tailWord_238962, baseEnd_238962] using wordTrace_append hprefix tailTrace_238962
  have hstable : (prefixWord ++ tailWord_238962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238962).length < 2 ^ (prefixWord ++ tailWord_238962).sum := by decide
  have hdescent : baseEnd_238962 < baseStart_238962 := by decide
  rcases family_descends (prefixWord ++ tailWord_238962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238976 : List Nat := [2, 1, 1, 2, 1, 2, 1, 7, 3]
def baseStart_238976 : Nat := 118140960795 + 238976 * 2 ^ 59
def prefixEnd_238976 : Nat := 4983230072969 + 3 ^ 40 * 238976 * 2
def baseEnd_238976 : Nat := 109075158123521990223089

theorem tailTrace_238976 : CollatzResearch.WordTrace tailWord_238976 prefixEnd_238976 109075158123521990223089 := by
  unfold tailWord_238976
  simp only [CollatzResearch.WordTrace]
  refine ⟨4358085391119120348276391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5810780521492160464368521 4358085391119120348276391)
  ·
    refine ⟨6537128086678680522414587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4358085391119120348276391 6537128086678680522414587)
    ·
      refine ⟨9805692130018020783621881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6537128086678680522414587 9805692130018020783621881)
      ·
        refine ⟨7354269097513515587716411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9805692130018020783621881 7354269097513515587716411)
        ·
          refine ⟨11031403646270273381574617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7354269097513515587716411 11031403646270273381574617)
          ·
            refine ⟨8273552734702705036180963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11031403646270273381574617 8273552734702705036180963)
            ·
              refine ⟨12410329102054057554271445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8273552734702705036180963 12410329102054057554271445)
              ·
                refine ⟨290867088329391973928237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 12410329102054057554271445 290867088329391973928237)
                ·
                  refine ⟨109075158123521990223089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 290867088329391973928237 109075158123521990223089)
                  ·
                    rfl

theorem cell20_238976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7, 3].length) (baseStart_238976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238976 prefixEnd_238976 := by exact prefixLift 238976
  have htrace : WordTrace (prefixWord ++ tailWord_238976) baseStart_238976 baseEnd_238976 := by
    simpa [prefixWord, tailWord_238976, baseEnd_238976] using wordTrace_append hprefix tailTrace_238976
  have hstable : (prefixWord ++ tailWord_238976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238976).length < 2 ^ (prefixWord ++ tailWord_238976).sum := by decide
  have hdescent : baseEnd_238976 < baseStart_238976 := by decide
  rcases family_descends (prefixWord ++ tailWord_238976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238996 : List Nat := [2, 4, 2, 1, 2, 1, 3, 3, 2]
def baseStart_238996 : Nat := 118140960795 + 238996 * 2 ^ 59
def prefixEnd_238996 : Nat := 4983230072969 + 3 ^ 40 * 238996 * 2
def baseEnd_238996 : Nat := 109084286668490809556341

theorem tailTrace_238996 : CollatzResearch.WordTrace tailWord_238996 prefixEnd_238996 109084286668490809556341 := by
  unfold tailWord_238996
  simp only [CollatzResearch.WordTrace]
  refine ⟨4358450121082892056140421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5811266828110522741520561 4358450121082892056140421)
  ·
    refine ⟨817209397703042260526329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4358450121082892056140421 817209397703042260526329)
    ·
      refine ⟨612907048277281695394747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 817209397703042260526329 612907048277281695394747)
      ·
        refine ⟨919360572415922543092121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 612907048277281695394747 919360572415922543092121)
        ·
          refine ⟨689520429311941907319091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 919360572415922543092121 689520429311941907319091)
          ·
            refine ⟨1034280643967912860978637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 689520429311941907319091 1034280643967912860978637)
            ·
              refine ⟨387855241487967322866989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1034280643967912860978637 387855241487967322866989)
              ·
                refine ⟨145445715557987746075121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 387855241487967322866989 145445715557987746075121)
                ·
                  refine ⟨109084286668490809556341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145445715557987746075121 109084286668490809556341)
                  ·
                    rfl

theorem cell20_238996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_238996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_238996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_238996 prefixEnd_238996 := by exact prefixLift 238996
  have htrace : WordTrace (prefixWord ++ tailWord_238996) baseStart_238996 baseEnd_238996 := by
    simpa [prefixWord, tailWord_238996, baseEnd_238996] using wordTrace_append hprefix tailTrace_238996
  have hstable : (prefixWord ++ tailWord_238996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238996).length < 2 ^ (prefixWord ++ tailWord_238996).sum := by decide
  have hdescent : baseEnd_238996 < baseStart_238996 := by decide
  rcases family_descends (prefixWord ++ tailWord_238996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239007 : List Nat := [1, 1, 2, 5, 1, 4, 6]
def baseStart_239007 : Nat := 118140960795 + 239007 * 2 ^ 59
def prefixEnd_239007 : Nat := 4983230072969 + 3 ^ 40 * 239007 * 2
def baseEnd_239007 : Nat := 12121034152024851132181

theorem tailTrace_239007 : CollatzResearch.WordTrace tailWord_239007 prefixEnd_239007 12121034152024851132181 := by
  unfold tailWord_239007
  simp only [CollatzResearch.WordTrace]
  refine ⟨8717301445125932990931275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5811534296750621993954183 8717301445125932990931275)
  ·
    refine ⟨13075952167688899486396913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8717301445125932990931275 13075952167688899486396913)
    ·
      refine ⟨9806964125766674614797685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13075952167688899486396913 9806964125766674614797685)
      ·
        refine ⟨919402886790625745137283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9806964125766674614797685 919402886790625745137283)
        ·
          refine ⟨1379104330185938617705925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 919402886790625745137283 1379104330185938617705925)
          ·
            refine ⟨258582061909863490819861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1379104330185938617705925 258582061909863490819861)
            ·
              refine ⟨12121034152024851132181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 258582061909863490819861 12121034152024851132181)
              ·
                rfl

theorem cell20_239007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 6].length) (baseStart_239007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239007 prefixEnd_239007 := by exact prefixLift 239007
  have htrace : WordTrace (prefixWord ++ tailWord_239007) baseStart_239007 baseEnd_239007 := by
    simpa [prefixWord, tailWord_239007, baseEnd_239007] using wordTrace_append hprefix tailTrace_239007
  have hstable : (prefixWord ++ tailWord_239007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239007).length < 2 ^ (prefixWord ++ tailWord_239007).sum := by decide
  have hdescent : baseEnd_239007 < baseStart_239007 := by decide
  rcases family_descends (prefixWord ++ tailWord_239007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239066 : List Nat := [3, 1, 1, 2, 3, 10]
def baseStart_239066 : Nat := 118140960795 + 239066 * 2 ^ 59
def prefixEnd_239066 : Nat := 4983230072969 + 3 ^ 40 * 239066 * 2
def baseEnd_239066 : Nat := 4041342095403025082323

theorem tailTrace_239066 : CollatzResearch.WordTrace tailWord_239066 prefixEnd_239066 4041342095403025082323 := by
  unfold tailWord_239066
  simp only [CollatzResearch.WordTrace]
  refine ⟨2179863337978046516832263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5812968901274790711552701 2179863337978046516832263)
  ·
    refine ⟨3269795006967069775248395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2179863337978046516832263 3269795006967069775248395)
    ·
      refine ⟨4904692510450604662872593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3269795006967069775248395 4904692510450604662872593)
      ·
        refine ⟨3678519382837953497154445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4904692510450604662872593 3678519382837953497154445)
        ·
          refine ⟨1379444768564232561432917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3678519382837953497154445 1379444768564232561432917)
          ·
            refine ⟨4041342095403025082323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1379444768564232561432917 4041342095403025082323)
            ·
              rfl

theorem cell20_239066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 10].length) (baseStart_239066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239066 prefixEnd_239066 := by exact prefixLift 239066
  have htrace : WordTrace (prefixWord ++ tailWord_239066) baseStart_239066 baseEnd_239066 := by
    simpa [prefixWord, tailWord_239066, baseEnd_239066] using wordTrace_append hprefix tailTrace_239066
  have hstable : (prefixWord ++ tailWord_239066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239066).length < 2 ^ (prefixWord ++ tailWord_239066).sum := by decide
  have hdescent : baseEnd_239066 < baseStart_239066 := by decide
  rcases family_descends (prefixWord ++ tailWord_239066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239069 : List Nat := [1, 4, 3, 1, 1, 2, 1, 4, 3]
def baseStart_239069 : Nat := 118140960795 + 239069 * 2 ^ 59
def prefixEnd_239069 : Nat := 4983230072969 + 3 ^ 40 * 239069 * 2
def baseEnd_239069 : Nat := 109117605857627000122709

theorem tailTrace_239069 : CollatzResearch.WordTrace tailWord_239069 prefixEnd_239069 109117605857627000122709 := by
  unfold tailWord_239069
  simp only [CollatzResearch.WordTrace]
  refine ⟨8719562770901317579688261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5813041847267545053125507 8719562770901317579688261)
  ·
    refine ⟨1634918019543997046191549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8719562770901317579688261 1634918019543997046191549)
    ·
      refine ⟨613094257328998892321831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1634918019543997046191549 613094257328998892321831)
      ·
        refine ⟨919641385993498338482747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613094257328998892321831 919641385993498338482747)
        ·
          refine ⟨1379462078990247507724121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 919641385993498338482747 1379462078990247507724121)
          ·
            refine ⟨1034596559242685630793091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1379462078990247507724121 1034596559242685630793091)
            ·
              refine ⟨1551894838864028446189637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1034596559242685630793091 1551894838864028446189637)
              ·
                refine ⟨290980282287005333660557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1551894838864028446189637 290980282287005333660557)
                ·
                  refine ⟨109117605857627000122709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 290980282287005333660557 109117605857627000122709)
                  ·
                    rfl

theorem cell20_239069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_239069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239069 prefixEnd_239069 := by exact prefixLift 239069
  have htrace : WordTrace (prefixWord ++ tailWord_239069) baseStart_239069 baseEnd_239069 := by
    simpa [prefixWord, tailWord_239069, baseEnd_239069] using wordTrace_append hprefix tailTrace_239069
  have hstable : (prefixWord ++ tailWord_239069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239069).length < 2 ^ (prefixWord ++ tailWord_239069).sum := by decide
  have hdescent : baseEnd_239069 < baseStart_239069 := by decide
  rcases family_descends (prefixWord ++ tailWord_239069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239093 : List Nat := [1, 3, 5, 1, 1, 2, 1, 2, 4]
def baseStart_239093 : Nat := 118140960795 + 239093 * 2 ^ 59
def prefixEnd_239093 : Nat := 4983230072969 + 3 ^ 40 * 239093 * 2
def baseEnd_239093 : Nat := 109128560111589583322611

theorem tailTrace_239093 : CollatzResearch.WordTrace tailWord_239093 prefixEnd_239093 109128560111589583322611 := by
  unfold tailWord_239093
  simp only [CollatzResearch.WordTrace]
  refine ⟨8720438122814369678561933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5813625415209579785707955 8720438122814369678561933)
  ·
    refine ⟨3270164296055388629460725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8720438122814369678561933 3270164296055388629460725)
    ·
      refine ⟨306577902755192684011943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3270164296055388629460725 306577902755192684011943)
      ·
        refine ⟨459866854132789026017915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306577902755192684011943 459866854132789026017915)
        ·
          refine ⟨689800281199183539026873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459866854132789026017915 689800281199183539026873)
          ·
            refine ⟨517350210899387654270155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 689800281199183539026873 517350210899387654270155)
            ·
              refine ⟨776025316349081481405233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517350210899387654270155 776025316349081481405233)
              ·
                refine ⟨582018987261811111053925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 776025316349081481405233 582018987261811111053925)
                ·
                  refine ⟨109128560111589583322611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 582018987261811111053925 109128560111589583322611)
                  ·
                    rfl

theorem cell20_239093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 4].length) (baseStart_239093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239093 prefixEnd_239093 := by exact prefixLift 239093
  have htrace : WordTrace (prefixWord ++ tailWord_239093) baseStart_239093 baseEnd_239093 := by
    simpa [prefixWord, tailWord_239093, baseEnd_239093] using wordTrace_append hprefix tailTrace_239093
  have hstable : (prefixWord ++ tailWord_239093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239093).length < 2 ^ (prefixWord ++ tailWord_239093).sum := by decide
  have hdescent : baseEnd_239093 < baseStart_239093 := by decide
  rcases family_descends (prefixWord ++ tailWord_239093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239117 : List Nat := [1, 7, 1, 1, 2, 1, 7]
def baseStart_239117 : Nat := 118140960795 + 239117 * 2 ^ 59
def prefixEnd_239117 : Nat := 4983230072969 + 3 ^ 40 * 239117 * 2
def baseEnd_239117 : Nat := 12126612707283574058057

theorem tailTrace_239117 : CollatzResearch.WordTrace tailWord_239117 prefixEnd_239117 12126612707283574058057 := by
  unfold tailWord_239117
  simp only [CollatzResearch.WordTrace]
  refine ⟨8721313474727421777435605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5814208983151614518290403 8721313474727421777435605)
  ·
    refine ⟨204405784563923947908647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 8721313474727421777435605 204405784563923947908647)
    ·
      refine ⟨306608676845885921862971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204405784563923947908647 306608676845885921862971)
      ·
        refine ⟨459913015268828882794457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306608676845885921862971 459913015268828882794457)
        ·
          refine ⟨344934761451621662095843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 459913015268828882794457 344934761451621662095843)
          ·
            refine ⟨517402142177432493143765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344934761451621662095843 517402142177432493143765)
            ·
              refine ⟨12126612707283574058057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 517402142177432493143765 12126612707283574058057)
              ·
                rfl

theorem cell20_239117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 7].length) (baseStart_239117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239117 prefixEnd_239117 := by exact prefixLift 239117
  have htrace : WordTrace (prefixWord ++ tailWord_239117) baseStart_239117 baseEnd_239117 := by
    simpa [prefixWord, tailWord_239117, baseEnd_239117] using wordTrace_append hprefix tailTrace_239117
  have hstable : (prefixWord ++ tailWord_239117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239117).length < 2 ^ (prefixWord ++ tailWord_239117).sum := by decide
  have hdescent : baseEnd_239117 < baseStart_239117 := by decide
  rcases family_descends (prefixWord ++ tailWord_239117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239124 : List Nat := [2, 4, 3, 1, 2, 1, 1, 1, 5]
def baseStart_239124 : Nat := 118140960795 + 239124 * 2 ^ 59
def prefixEnd_239124 : Nat := 4983230072969 + 3 ^ 40 * 239124 * 2
def baseEnd_239124 : Nat := 109142709356291253289151

theorem tailTrace_239124 : CollatzResearch.WordTrace tailWord_239124 prefixEnd_239124 109142709356291253289151 := by
  unfold tailWord_239124
  simp only [CollatzResearch.WordTrace]
  refine ⟨4360784392851030986470213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5814379190468041315293617 4360784392851030986470213)
  ·
    refine ⟨817647073659568309963165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4360784392851030986470213 817647073659568309963165)
    ·
      refine ⟨306617652622338116236187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 817647073659568309963165 306617652622338116236187)
      ·
        refine ⟨459926478933507174354281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306617652622338116236187 459926478933507174354281)
        ·
          refine ⟨344944859200130380765711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 459926478933507174354281 344944859200130380765711)
          ·
            refine ⟨517417288800195571148567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344944859200130380765711 517417288800195571148567)
            ·
              refine ⟨776125933200293356722851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517417288800195571148567 776125933200293356722851)
              ·
                refine ⟨1164188899800440035084277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 776125933200293356722851 1164188899800440035084277)
                ·
                  refine ⟨109142709356291253289151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1164188899800440035084277 109142709356291253289151)
                  ·
                    rfl

theorem cell20_239124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_239124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239124 prefixEnd_239124 := by exact prefixLift 239124
  have htrace : WordTrace (prefixWord ++ tailWord_239124) baseStart_239124 baseEnd_239124 := by
    simpa [prefixWord, tailWord_239124, baseEnd_239124] using wordTrace_append hprefix tailTrace_239124
  have hstable : (prefixWord ++ tailWord_239124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239124).length < 2 ^ (prefixWord ++ tailWord_239124).sum := by decide
  have hdescent : baseEnd_239124 < baseStart_239124 := by decide
  rcases family_descends (prefixWord ++ tailWord_239124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239135 : List Nat := [1, 1, 2, 4, 1, 1, 3, 3, 4]
def baseStart_239135 : Nat := 118140960795 + 239135 * 2 ^ 59
def prefixEnd_239135 : Nat := 4983230072969 + 3 ^ 40 * 239135 * 2
def baseEnd_239135 : Nat := 109147730056024103922439

theorem tailTrace_239135 : CollatzResearch.WordTrace tailWord_239135 prefixEnd_239135 109147730056024103922439 := by
  unfold tailWord_239135
  simp only [CollatzResearch.WordTrace]
  refine ⟨8721969988662210851590859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5814646659108140567727239 8721969988662210851590859)
  ·
    refine ⟨13082954982993316277386289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8721969988662210851590859 13082954982993316277386289)
    ·
      refine ⟨9812216237244987208039717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13082954982993316277386289 9812216237244987208039717)
      ·
        refine ⟨1839790544483435101507447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9812216237244987208039717 1839790544483435101507447)
        ·
          refine ⟨2759685816725152652261171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1839790544483435101507447 2759685816725152652261171)
          ·
            refine ⟨4139528725087728978391757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2759685816725152652261171 4139528725087728978391757)
            ·
              refine ⟨1552323271907898366896909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4139528725087728978391757 1552323271907898366896909)
              ·
                refine ⟨582121226965461887586341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1552323271907898366896909 582121226965461887586341)
                ·
                  refine ⟨109147730056024103922439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 582121226965461887586341 109147730056024103922439)
                  ·
                    rfl

theorem cell20_239135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 4].length) (baseStart_239135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239135 prefixEnd_239135 := by exact prefixLift 239135
  have htrace : WordTrace (prefixWord ++ tailWord_239135) baseStart_239135 baseEnd_239135 := by
    simpa [prefixWord, tailWord_239135, baseEnd_239135] using wordTrace_append hprefix tailTrace_239135
  have hstable : (prefixWord ++ tailWord_239135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239135).length < 2 ^ (prefixWord ++ tailWord_239135).sum := by decide
  have hdescent : baseEnd_239135 < baseStart_239135 := by decide
  rcases family_descends (prefixWord ++ tailWord_239135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239159 : List Nat := [1, 1, 3, 1, 2, 4, 4, 4]
def baseStart_239159 : Nat := 118140960795 + 239159 * 2 ^ 59
def prefixEnd_239159 : Nat := 4983230072969 + 3 ^ 40 * 239159 * 2
def baseEnd_239159 : Nat := 36386228103328895707447

theorem tailTrace_239159 : CollatzResearch.WordTrace tailWord_239159 prefixEnd_239159 36386228103328895707447 := by
  unfold tailWord_239159
  simp only [CollatzResearch.WordTrace]
  refine ⟨8722845340575262950464531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5815230227050175300309687 8722845340575262950464531)
  ·
    refine ⟨13084268010862894425696797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8722845340575262950464531 13084268010862894425696797)
    ·
      refine ⟨4906600504073585409636299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13084268010862894425696797 4906600504073585409636299)
      ·
        refine ⟨7359900756110378114454449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4906600504073585409636299 7359900756110378114454449)
        ·
          refine ⟨5519925567082783585840837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7359900756110378114454449 5519925567082783585840837)
          ·
            refine ⟨1034986043828021922345157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5519925567082783585840837 1034986043828021922345157)
            ·
              refine ⟨194059883217754110439717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1034986043828021922345157 194059883217754110439717)
              ·
                refine ⟨36386228103328895707447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 194059883217754110439717 36386228103328895707447)
                ·
                  rfl

theorem cell20_239159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 4].length) (baseStart_239159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239159 prefixEnd_239159 := by exact prefixLift 239159
  have htrace : WordTrace (prefixWord ++ tailWord_239159) baseStart_239159 baseEnd_239159 := by
    simpa [prefixWord, tailWord_239159, baseEnd_239159] using wordTrace_append hprefix tailTrace_239159
  have hstable : (prefixWord ++ tailWord_239159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239159).length < 2 ^ (prefixWord ++ tailWord_239159).sum := by decide
  have hdescent : baseEnd_239159 < baseStart_239159 := by decide
  rcases family_descends (prefixWord ++ tailWord_239159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239165 : List Nat := [1, 4, 1, 3, 4, 1, 1, 3, 2]
def baseStart_239165 : Nat := 118140960795 + 239165 * 2 ^ 59
def prefixEnd_239165 : Nat := 4983230072969 + 3 ^ 40 * 239165 * 2
def baseEnd_239165 : Nat := 109161422873477332922317

theorem tailTrace_239165 : CollatzResearch.WordTrace tailWord_239165 prefixEnd_239165 109161422873477332922317 := by
  unfold tailWord_239165
  simp only [CollatzResearch.WordTrace]
  refine ⟨8723064178553525975182949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5815376119035683983455299 8723064178553525975182949)
  ·
    refine ⟨1635574533478786120346803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8723064178553525975182949 1635574533478786120346803)
    ·
      refine ⟨2453361800218179180520205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1635574533478786120346803 2453361800218179180520205)
      ·
        refine ⟨920010675081817192695077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2453361800218179180520205 920010675081817192695077)
        ·
          refine ⟨172502001577840723630327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 920010675081817192695077 172502001577840723630327)
          ·
            refine ⟨258753002366761085445491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172502001577840723630327 258753002366761085445491)
            ·
              refine ⟨388129503550141628168237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258753002366761085445491 388129503550141628168237)
              ·
                refine ⟨145548563831303110563089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 388129503550141628168237 145548563831303110563089)
                ·
                  refine ⟨109161422873477332922317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145548563831303110563089 109161422873477332922317)
                  ·
                    rfl

theorem cell20_239165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 3, 2].length) (baseStart_239165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239165 prefixEnd_239165 := by exact prefixLift 239165
  have htrace : WordTrace (prefixWord ++ tailWord_239165) baseStart_239165 baseEnd_239165 := by
    simpa [prefixWord, tailWord_239165, baseEnd_239165] using wordTrace_append hprefix tailTrace_239165
  have hstable : (prefixWord ++ tailWord_239165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239165).length < 2 ^ (prefixWord ++ tailWord_239165).sum := by decide
  have hdescent : baseEnd_239165 < baseStart_239165 := by decide
  rcases family_descends (prefixWord ++ tailWord_239165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239180 : List Nat := [2, 2, 1, 3, 1, 3, 8]
def baseStart_239180 : Nat := 118140960795 + 239180 * 2 ^ 59
def prefixEnd_239180 : Nat := 4983230072969 + 3 ^ 40 * 239180 * 2
def baseEnd_239180 : Nat := 12129807698022660824695

theorem tailTrace_239180 : CollatzResearch.WordTrace tailWord_239180 prefixEnd_239180 12129807698022660824695 := by
  unfold tailWord_239180
  simp only [CollatzResearch.WordTrace]
  refine ⟨4361805636749591768489497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5815740848999455691319329 4361805636749591768489497)
  ·
    refine ⟨3271354227562193826367123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4361805636749591768489497 3271354227562193826367123)
    ·
      refine ⟨4907031341343290739550685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3271354227562193826367123 4907031341343290739550685)
      ·
        refine ⟨1840136753003734027331507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4907031341343290739550685 1840136753003734027331507)
        ·
          refine ⟨2760205129505601040997261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1840136753003734027331507 2760205129505601040997261)
          ·
            refine ⟨1035076923564600390373973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2760205129505601040997261 1035076923564600390373973)
            ·
              refine ⟨12129807698022660824695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1035076923564600390373973 12129807698022660824695)
              ·
                rfl

theorem cell20_239180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 8].length) (baseStart_239180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239180 prefixEnd_239180 := by exact prefixLift 239180
  have htrace : WordTrace (prefixWord ++ tailWord_239180) baseStart_239180 baseEnd_239180 := by
    simpa [prefixWord, tailWord_239180, baseEnd_239180] using wordTrace_append hprefix tailTrace_239180
  have hstable : (prefixWord ++ tailWord_239180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239180).length < 2 ^ (prefixWord ++ tailWord_239180).sum := by decide
  have hdescent : baseEnd_239180 < baseStart_239180 := by decide
  rcases family_descends (prefixWord ++ tailWord_239180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239186 : List Nat := [3, 2, 2, 1, 2, 3, 3, 2, 2]
def baseStart_239186 : Nat := 118140960795 + 239186 * 2 ^ 59
def prefixEnd_239186 : Nat := 4983230072969 + 3 ^ 40 * 239186 * 2
def baseEnd_239186 : Nat := 109171007845694593222231

theorem tailTrace_239186 : CollatzResearch.WordTrace tailWord_239186 prefixEnd_239186 109171007845694593222231 := by
  unfold tailWord_239186
  simp only [CollatzResearch.WordTrace]
  refine ⟨2180957527869361640424353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5815886740984964374464941 2180957527869361640424353)
  ·
    refine ⟨1635718145902021230318265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2180957527869361640424353 1635718145902021230318265)
    ·
      refine ⟨1226788609426515922738699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1635718145902021230318265 1226788609426515922738699)
      ·
        refine ⟨1840182914139773884108049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1226788609426515922738699 1840182914139773884108049)
        ·
          refine ⟨1380137185604830413081037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1840182914139773884108049 1380137185604830413081037)
          ·
            refine ⟨517551444601811404905389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1380137185604830413081037 517551444601811404905389)
            ·
              refine ⟨194081791725679276839521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 517551444601811404905389 194081791725679276839521)
              ·
                refine ⟨145561343794259457629641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194081791725679276839521 145561343794259457629641)
                ·
                  refine ⟨109171007845694593222231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145561343794259457629641 109171007845694593222231)
                  ·
                    rfl

theorem cell20_239186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 2, 2].length) (baseStart_239186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239186 prefixEnd_239186 := by exact prefixLift 239186
  have htrace : WordTrace (prefixWord ++ tailWord_239186) baseStart_239186 baseEnd_239186 := by
    simpa [prefixWord, tailWord_239186, baseEnd_239186] using wordTrace_append hprefix tailTrace_239186
  have hstable : (prefixWord ++ tailWord_239186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239186).length < 2 ^ (prefixWord ++ tailWord_239186).sum := by decide
  have hdescent : baseEnd_239186 < baseStart_239186 := by decide
  rcases family_descends (prefixWord ++ tailWord_239186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239228 : List Nat := [2, 2, 2, 1, 1, 2, 1, 7, 2]
def baseStart_239228 : Nat := 118140960795 + 239228 * 2 ^ 59
def prefixEnd_239228 : Nat := 4983230072969 + 3 ^ 40 * 239228 * 2
def baseEnd_239228 : Nat := 109190177790129113822059

theorem tailTrace_239228 : CollatzResearch.WordTrace tailWord_239228 prefixEnd_239228 109190177790129113822059 := by
  unfold tailWord_239228
  simp only [CollatzResearch.WordTrace]
  refine ⟨4362680988662643867363169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5816907984883525156484225 4362680988662643867363169)
  ·
    refine ⟨3272010741496982900522377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4362680988662643867363169 3272010741496982900522377)
    ·
      refine ⟨2454008056122737175391783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3272010741496982900522377 2454008056122737175391783)
      ·
        refine ⟨3681012084184105763087675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2454008056122737175391783 3681012084184105763087675)
        ·
          refine ⟨5521518126276158644631513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3681012084184105763087675 5521518126276158644631513)
          ·
            refine ⟨4141138594707118983473635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5521518126276158644631513 4141138594707118983473635)
            ·
              refine ⟨6211707892060678475210453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4141138594707118983473635 6211707892060678475210453)
              ·
                refine ⟨145586903720172151762745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6211707892060678475210453 145586903720172151762745)
                ·
                  refine ⟨109190177790129113822059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145586903720172151762745 109190177790129113822059)
                  ·
                    rfl

theorem cell20_239228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 7, 2].length) (baseStart_239228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239228 prefixEnd_239228 := by exact prefixLift 239228
  have htrace : WordTrace (prefixWord ++ tailWord_239228) baseStart_239228 baseEnd_239228 := by
    simpa [prefixWord, tailWord_239228, baseEnd_239228] using wordTrace_append hprefix tailTrace_239228
  have hstable : (prefixWord ++ tailWord_239228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239228).length < 2 ^ (prefixWord ++ tailWord_239228).sum := by decide
  have hdescent : baseEnd_239228 < baseStart_239228 := by decide
  rcases family_descends (prefixWord ++ tailWord_239228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239301 : List Nat := [1, 3, 1, 1, 1, 1, 2, 5, 5]
def baseStart_239301 : Nat := 118140960795 + 239301 * 2 ^ 59
def prefixEnd_239301 : Nat := 4983230072969 + 3 ^ 40 * 239301 * 2
def baseEnd_239301 : Nat := 109223496979265304388427

theorem tailTrace_239301 : CollatzResearch.WordTrace tailWord_239301 prefixEnd_239301 109223496979265304388427 := by
  unfold tailWord_239301
  simp only [CollatzResearch.WordTrace]
  refine ⟨8728024506060821202133757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5818683004040547468089171 8728024506060821202133757)
  ·
    refine ⟨3273009189772807950800159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8728024506060821202133757 3273009189772807950800159)
    ·
      refine ⟨4909513784659211926200239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3273009189772807950800159 4909513784659211926200239)
      ·
        refine ⟨7364270676988817889300359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4909513784659211926200239 7364270676988817889300359)
        ·
          refine ⟨11046406015483226833950539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7364270676988817889300359 11046406015483226833950539)
          ·
            refine ⟨16569609023224840250925809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11046406015483226833950539 16569609023224840250925809)
            ·
              refine ⟨12427206767418630188194357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16569609023224840250925809 12427206767418630188194357)
              ·
                refine ⟨1165050634445496580143221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12427206767418630188194357 1165050634445496580143221)
                ·
                  refine ⟨109223496979265304388427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1165050634445496580143221 109223496979265304388427)
                  ·
                    rfl

theorem cell20_239301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_239301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239301 prefixEnd_239301 := by exact prefixLift 239301
  have htrace : WordTrace (prefixWord ++ tailWord_239301) baseStart_239301 baseEnd_239301 := by
    simpa [prefixWord, tailWord_239301, baseEnd_239301] using wordTrace_append hprefix tailTrace_239301
  have hstable : (prefixWord ++ tailWord_239301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239301).length < 2 ^ (prefixWord ++ tailWord_239301).sum := by decide
  have hdescent : baseEnd_239301 < baseStart_239301 := by decide
  rcases family_descends (prefixWord ++ tailWord_239301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239304 : List Nat := [2, 1, 3, 1, 2, 2, 1, 6, 2]
def baseStart_239304 : Nat := 118140960795 + 239304 * 2 ^ 59
def prefixEnd_239304 : Nat := 4983230072969 + 3 ^ 40 * 239304 * 2
def baseEnd_239304 : Nat := 109224866261010627288415

theorem tailTrace_239304 : CollatzResearch.WordTrace tailWord_239304 prefixEnd_239304 109224866261010627288415 := by
  unfold tailWord_239304
  simp only [CollatzResearch.WordTrace]
  refine ⟨4364066962524976357246483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5818755950033301809661977 4364066962524976357246483)
  ·
    refine ⟨6546100443787464535869725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4364066962524976357246483 6546100443787464535869725)
    ·
      refine ⟨2454787666420299200951147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6546100443787464535869725 2454787666420299200951147)
      ·
        refine ⟨3682181499630448801426721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2454787666420299200951147 3682181499630448801426721)
        ·
          refine ⟨2761636124722836601070041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3682181499630448801426721 2761636124722836601070041)
          ·
            refine ⟨2071227093542127450802531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2761636124722836601070041 2071227093542127450802531)
            ·
              refine ⟨3106840640313191176203797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2071227093542127450802531 3106840640313191176203797)
              ·
                refine ⟨145633155014680836384553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3106840640313191176203797 145633155014680836384553)
                ·
                  refine ⟨109224866261010627288415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145633155014680836384553 109224866261010627288415)
                  ·
                    rfl

theorem cell20_239304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 6, 2].length) (baseStart_239304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239304 prefixEnd_239304 := by exact prefixLift 239304
  have htrace : WordTrace (prefixWord ++ tailWord_239304) baseStart_239304 baseEnd_239304 := by
    simpa [prefixWord, tailWord_239304, baseEnd_239304] using wordTrace_append hprefix tailTrace_239304
  have hstable : (prefixWord ++ tailWord_239304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239304).length < 2 ^ (prefixWord ++ tailWord_239304).sum := by decide
  have hdescent : baseEnd_239304 < baseStart_239304 := by decide
  rcases family_descends (prefixWord ++ tailWord_239304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239314 : List Nat := [3, 2, 2, 2, 2, 2, 3, 1, 3]
def baseStart_239314 : Nat := 118140960795 + 239314 * 2 ^ 59
def prefixEnd_239314 : Nat := 4983230072969 + 3 ^ 40 * 239314 * 2
def baseEnd_239314 : Nat := 109229430533495036955041

theorem tailTrace_239314 : CollatzResearch.WordTrace tailWord_239314 prefixEnd_239314 109229430533495036955041 := by
  unfold tailWord_239314
  simp only [CollatzResearch.WordTrace]
  refine ⟨2182124663753431105589249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5818999103342482948237997 2182124663753431105589249)
  ·
    refine ⟨1636593497815073329191937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2182124663753431105589249 1636593497815073329191937)
    ·
      refine ⟨1227445123361304996893953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1636593497815073329191937 1227445123361304996893953)
      ·
        refine ⟨920583842520978747670465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1227445123361304996893953 920583842520978747670465)
        ·
          refine ⟨690437881890734060752849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 920583842520978747670465 690437881890734060752849)
          ·
            refine ⟨517828411418050545564637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 690437881890734060752849 517828411418050545564637)
            ·
              refine ⟨194185654281768954586739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 517828411418050545564637 194185654281768954586739)
              ·
                refine ⟨291278481422653431880109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194185654281768954586739 291278481422653431880109)
                ·
                  refine ⟨109229430533495036955041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 291278481422653431880109 109229430533495036955041)
                  ·
                    rfl

theorem cell20_239314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_239314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239314 prefixEnd_239314 := by exact prefixLift 239314
  have htrace : WordTrace (prefixWord ++ tailWord_239314) baseStart_239314 baseEnd_239314 := by
    simpa [prefixWord, tailWord_239314, baseEnd_239314] using wordTrace_append hprefix tailTrace_239314
  have hstable : (prefixWord ++ tailWord_239314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239314).length < 2 ^ (prefixWord ++ tailWord_239314).sum := by decide
  have hdescent : baseEnd_239314 < baseStart_239314 := by decide
  rcases family_descends (prefixWord ++ tailWord_239314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239324 : List Nat := [2, 2, 5, 1, 3, 1, 2, 4]
def baseStart_239324 : Nat := 118140960795 + 239324 * 2 ^ 59
def prefixEnd_239324 : Nat := 4983230072969 + 3 ^ 40 * 239324 * 2
def baseEnd_239324 : Nat := 36411331601993148873889

theorem tailTrace_239324 : CollatzResearch.WordTrace tailWord_239324 prefixEnd_239324 36411331601993148873889 := by
  unfold tailWord_239324
  simp only [CollatzResearch.WordTrace]
  refine ⟨4364431692488748065110513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5819242256651664086814017 4364431692488748065110513)
  ·
    refine ⟨3273323769366561048832885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4364431692488748065110513 3273323769366561048832885)
    ·
      refine ⟨306874103378115098328083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3273323769366561048832885 306874103378115098328083)
      ·
        refine ⟨460311155067172647492125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306874103378115098328083 460311155067172647492125)
        ·
          refine ⟨172616683150189742809547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 460311155067172647492125 172616683150189742809547)
          ·
            refine ⟨258925024725284614214321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172616683150189742809547 258925024725284614214321)
            ·
              refine ⟨194193768543963460660741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258925024725284614214321 194193768543963460660741)
              ·
                refine ⟨36411331601993148873889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 194193768543963460660741 36411331601993148873889)
                ·
                  rfl

theorem cell20_239324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 4].length) (baseStart_239324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239324 prefixEnd_239324 := by exact prefixLift 239324
  have htrace : WordTrace (prefixWord ++ tailWord_239324) baseStart_239324 baseEnd_239324 := by
    simpa [prefixWord, tailWord_239324, baseEnd_239324] using wordTrace_append hprefix tailTrace_239324
  have hstable : (prefixWord ++ tailWord_239324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239324).length < 2 ^ (prefixWord ++ tailWord_239324).sum := by decide
  have hdescent : baseEnd_239324 < baseStart_239324 := by decide
  rcases family_descends (prefixWord ++ tailWord_239324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239332 : List Nat := [2, 3, 1, 1, 1, 3, 3, 6]
def baseStart_239332 : Nat := 118140960795 + 239332 * 2 ^ 59
def prefixEnd_239332 : Nat := 4983230072969 + 3 ^ 40 * 239332 * 2
def baseEnd_239332 : Nat := 36412548741322324784989

theorem tailTrace_239332 : CollatzResearch.WordTrace tailWord_239332 prefixEnd_239332 36412548741322324784989 := by
  unfold tailWord_239332
  simp only [CollatzResearch.WordTrace]
  refine ⟨4364577584474256748256125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5819436779299008997674833 4364577584474256748256125)
  ·
    refine ⟨1636716594177846280596047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4364577584474256748256125 1636716594177846280596047)
    ·
      refine ⟨2455074891266769420894071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1636716594177846280596047 2455074891266769420894071)
      ·
        refine ⟨3682612336900154131341107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2455074891266769420894071 3682612336900154131341107)
        ·
          refine ⟨5523918505350231197011661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3682612336900154131341107 5523918505350231197011661)
          ·
            refine ⟨2071469439506336698879373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5523918505350231197011661 2071469439506336698879373)
            ·
              refine ⟨776801039814876262079765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2071469439506336698879373 776801039814876262079765)
              ·
                refine ⟨36412548741322324784989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 776801039814876262079765 36412548741322324784989)
                ·
                  rfl

theorem cell20_239332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 6].length) (baseStart_239332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239332 prefixEnd_239332 := by exact prefixLift 239332
  have htrace : WordTrace (prefixWord ++ tailWord_239332) baseStart_239332 baseEnd_239332 := by
    simpa [prefixWord, tailWord_239332, baseEnd_239332] using wordTrace_append hprefix tailTrace_239332
  have hstable : (prefixWord ++ tailWord_239332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239332).length < 2 ^ (prefixWord ++ tailWord_239332).sum := by decide
  have hdescent : baseEnd_239332 < baseStart_239332 := by decide
  rcases family_descends (prefixWord ++ tailWord_239332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239339 : List Nat := [1, 1, 1, 1, 2, 4, 3, 2, 5]
def baseStart_239339 : Nat := 118140960795 + 239339 * 2 ^ 59
def prefixEnd_239339 : Nat := 4983230072969 + 3 ^ 40 * 239339 * 2
def baseEnd_239339 : Nat := 109240841214706061121605

theorem tailTrace_239339 : CollatzResearch.WordTrace tailWord_239339 prefixEnd_239339 109240841214706061121605 := by
  unfold tailWord_239339
  simp only [CollatzResearch.WordTrace]
  refine ⟨8729410479923153692017071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5819606986615435794678047 8729410479923153692017071)
  ·
    refine ⟨13094115719884730538025607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8729410479923153692017071 13094115719884730538025607)
    ·
      refine ⟨19641173579827095807038411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13094115719884730538025607 19641173579827095807038411)
      ·
        refine ⟨29461760369740643710557617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19641173579827095807038411 29461760369740643710557617)
        ·
          refine ⟨22096320277305482782918213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29461760369740643710557617 22096320277305482782918213)
          ·
            refine ⟨4143060051994778021797165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22096320277305482782918213 4143060051994778021797165)
            ·
              refine ⟨1553647519498041758173937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4143060051994778021797165 1553647519498041758173937)
              ·
                refine ⟨1165235639623531318630453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1553647519498041758173937 1165235639623531318630453)
                ·
                  refine ⟨109240841214706061121605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1165235639623531318630453 109240841214706061121605)
                  ·
                    rfl

theorem cell20_239339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 5].length) (baseStart_239339 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239339 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239339 prefixEnd_239339 := by exact prefixLift 239339
  have htrace : WordTrace (prefixWord ++ tailWord_239339) baseStart_239339 baseEnd_239339 := by
    simpa [prefixWord, tailWord_239339, baseEnd_239339] using wordTrace_append hprefix tailTrace_239339
  have hstable : (prefixWord ++ tailWord_239339).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239339).length < 2 ^ (prefixWord ++ tailWord_239339).sum := by decide
  have hdescent : baseEnd_239339 < baseStart_239339 := by decide
  rcases family_descends (prefixWord ++ tailWord_239339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239356 : List Nat := [2, 2, 2, 1, 3, 1, 2, 4, 3]
def baseStart_239356 : Nat := 118140960795 + 239356 * 2 ^ 59
def prefixEnd_239356 : Nat := 4983230072969 + 3 ^ 40 * 239356 * 2
def baseEnd_239356 : Nat := 109248600477929557554869

theorem tailTrace_239356 : CollatzResearch.WordTrace tailWord_239356 prefixEnd_239356 109248600477929557554869 := by
  unfold tailWord_239356
  simp only [CollatzResearch.WordTrace]
  refine ⟨4365015260430782797692961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5820020347241043730257281 4365015260430782797692961)
  ·
    refine ⟨3273761445323087098269721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4365015260430782797692961 3273761445323087098269721)
    ·
      refine ⟨2455321083992315323702291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3273761445323087098269721 2455321083992315323702291)
      ·
        refine ⟨3682981625988472985553437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2455321083992315323702291 3682981625988472985553437)
        ·
          refine ⟨1381118109745677369582539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3682981625988472985553437 1381118109745677369582539)
          ·
            refine ⟨2071677164618516054373809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1381118109745677369582539 2071677164618516054373809)
            ·
              refine ⟨1553757873463887040780357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2071677164618516054373809 1553757873463887040780357)
              ·
                refine ⟨291329601274478820146317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1553757873463887040780357 291329601274478820146317)
                ·
                  refine ⟨109248600477929557554869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 291329601274478820146317 109248600477929557554869)
                  ·
                    rfl

theorem cell20_239356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4, 3].length) (baseStart_239356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239356 prefixEnd_239356 := by exact prefixLift 239356
  have htrace : WordTrace (prefixWord ++ tailWord_239356) baseStart_239356 baseEnd_239356 := by
    simpa [prefixWord, tailWord_239356, baseEnd_239356] using wordTrace_append hprefix tailTrace_239356
  have hstable : (prefixWord ++ tailWord_239356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239356).length < 2 ^ (prefixWord ++ tailWord_239356).sum := by decide
  have hdescent : baseEnd_239356 < baseStart_239356 := by decide
  rcases family_descends (prefixWord ++ tailWord_239356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239363 : List Nat := [1, 1, 1, 3, 2, 2, 5, 1, 4]
def baseStart_239363 : Nat := 118140960795 + 239363 * 2 ^ 59
def prefixEnd_239363 : Nat := 4983230072969 + 3 ^ 40 * 239363 * 2
def baseEnd_239363 : Nat := 109251795468668644321507

theorem tailTrace_239363 : CollatzResearch.WordTrace tailWord_239363 prefixEnd_239363 109251795468668644321507 := by
  unfold tailWord_239363
  simp only [CollatzResearch.WordTrace]
  refine ⟨8730285831836205790890743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5820190554557470527260495 8730285831836205790890743)
  ·
    refine ⟨13095428747754308686336115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8730285831836205790890743 13095428747754308686336115)
    ·
      refine ⟨19643143121631463029504173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13095428747754308686336115 19643143121631463029504173)
      ·
        refine ⟨7366178670611798636064065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19643143121631463029504173 7366178670611798636064065)
        ·
          refine ⟨5524634002958848977048049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7366178670611798636064065 5524634002958848977048049)
          ·
            refine ⟨4143475502219136732786037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5524634002958848977048049 4143475502219136732786037)
            ·
              refine ⟨388450828333044068698691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4143475502219136732786037 388450828333044068698691)
              ·
                refine ⟨582676242499566103048037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 388450828333044068698691 582676242499566103048037)
                ·
                  refine ⟨109251795468668644321507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 582676242499566103048037 109251795468668644321507)
                  ·
                    rfl

theorem cell20_239363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 4].length) (baseStart_239363 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239363 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239363 prefixEnd_239363 := by exact prefixLift 239363
  have htrace : WordTrace (prefixWord ++ tailWord_239363) baseStart_239363 baseEnd_239363 := by
    simpa [prefixWord, tailWord_239363, baseEnd_239363] using wordTrace_append hprefix tailTrace_239363
  have hstable : (prefixWord ++ tailWord_239363).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239363).length < 2 ^ (prefixWord ++ tailWord_239363).sum := by decide
  have hdescent : baseEnd_239363 < baseStart_239363 := by decide
  rcases family_descends (prefixWord ++ tailWord_239363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239370 : List Nat := [3, 1, 2, 2, 1, 3, 1, 7]
def baseStart_239370 : Nat := 118140960795 + 239370 * 2 ^ 59
def prefixEnd_239370 : Nat := 4983230072969 + 3 ^ 40 * 239370 * 2
def baseEnd_239370 : Nat := 36418330153135910362715

theorem tailTrace_239370 : CollatzResearch.WordTrace tailWord_239370 prefixEnd_239370 36418330153135910362715 := by
  unfold tailWord_239370
  simp only [CollatzResearch.WordTrace]
  refine ⟨2182635285702711496598891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5820360761873897324263709 2182635285702711496598891)
  ·
    refine ⟨3273952928554067244898337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2182635285702711496598891 3273952928554067244898337)
    ·
      refine ⟨2455464696415550433673753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3273952928554067244898337 2455464696415550433673753)
      ·
        refine ⟨1841598522311662825255315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2455464696415550433673753 1841598522311662825255315)
        ·
          refine ⟨2762397783467494237882973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1841598522311662825255315 2762397783467494237882973)
          ·
            refine ⟨1035899168800310339206115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2762397783467494237882973 1035899168800310339206115)
            ·
              refine ⟨1553848753200465508809173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1035899168800310339206115 1553848753200465508809173)
              ·
                refine ⟨36418330153135910362715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1553848753200465508809173 36418330153135910362715)
                ·
                  rfl

theorem cell20_239370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_239370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239370 prefixEnd_239370 := by exact prefixLift 239370
  have htrace : WordTrace (prefixWord ++ tailWord_239370) baseStart_239370 baseEnd_239370 := by
    simpa [prefixWord, tailWord_239370, baseEnd_239370] using wordTrace_append hprefix tailTrace_239370
  have hstable : (prefixWord ++ tailWord_239370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239370).length < 2 ^ (prefixWord ++ tailWord_239370).sum := by decide
  have hdescent : baseEnd_239370 < baseStart_239370 := by decide
  rcases family_descends (prefixWord ++ tailWord_239370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239411 : List Nat := [1, 1, 1, 2, 7, 1, 2, 2, 3]
def baseStart_239411 : Nat := 118140960795 + 239411 * 2 ^ 59
def prefixEnd_239411 : Nat := 4983230072969 + 3 ^ 40 * 239411 * 2
def baseEnd_239411 : Nat := 109273703976593810721311

theorem tailTrace_239411 : CollatzResearch.WordTrace tailWord_239411 prefixEnd_239411 109273703976593810721311 := by
  unfold tailWord_239411
  simp only [CollatzResearch.WordTrace]
  refine ⟨8732036535662309988638087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5821357690441539992425391 8732036535662309988638087)
  ·
    refine ⟨13098054803493464982957131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8732036535662309988638087 13098054803493464982957131)
    ·
      refine ⟨19647082205240197474435697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13098054803493464982957131 19647082205240197474435697)
      ·
        refine ⟨14735311653930148105826773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19647082205240197474435697 14735311653930148105826773)
        ·
          refine ⟨345358866888987846230315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 14735311653930148105826773 345358866888987846230315)
          ·
            refine ⟨518038300333481769345473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345358866888987846230315 518038300333481769345473)
            ·
              refine ⟨388528725250111327009105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 518038300333481769345473 388528725250111327009105)
              ·
                refine ⟨291396543937583495256829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 388528725250111327009105 291396543937583495256829)
                ·
                  refine ⟨109273703976593810721311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 291396543937583495256829 109273703976593810721311)
                  ·
                    rfl

theorem cell20_239411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2, 3].length) (baseStart_239411 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239411 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239411 prefixEnd_239411 := by exact prefixLift 239411
  have htrace : WordTrace (prefixWord ++ tailWord_239411) baseStart_239411 baseEnd_239411 := by
    simpa [prefixWord, tailWord_239411, baseEnd_239411] using wordTrace_append hprefix tailTrace_239411
  have hstable : (prefixWord ++ tailWord_239411).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239411).length < 2 ^ (prefixWord ++ tailWord_239411).sum := by decide
  have hdescent : baseEnd_239411 < baseStart_239411 := by decide
  rcases family_descends (prefixWord ++ tailWord_239411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239414 : List Nat := [5, 1, 2, 2, 1, 2, 1, 4, 2]
def baseStart_239414 : Nat := 118140960795 + 239414 * 2 ^ 59
def prefixEnd_239414 : Nat := 4983230072969 + 3 ^ 40 * 239414 * 2
def baseEnd_239414 : Nat := 109275073258339133621299

theorem tailTrace_239414 : CollatzResearch.WordTrace tailWord_239414 prefixEnd_239414 109275073258339133621299 := by
  unfold tailWord_239414
  simp only [CollatzResearch.WordTrace]
  refine ⟨545759122165715093812331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5821430636434294333998197 545759122165715093812331)
  ·
    refine ⟨818638683248572640718497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 545759122165715093812331 818638683248572640718497)
    ·
      refine ⟨613979012436429480538873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 818638683248572640718497 613979012436429480538873)
      ·
        refine ⟨460484259327322110404155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 613979012436429480538873 460484259327322110404155)
        ·
          refine ⟨690726388990983165606233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460484259327322110404155 690726388990983165606233)
          ·
            refine ⟨518044791743237374204675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 690726388990983165606233 518044791743237374204675)
            ·
              refine ⟨777067187614856061307013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518044791743237374204675 777067187614856061307013)
              ·
                refine ⟨145700097677785511495065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 777067187614856061307013 145700097677785511495065)
                ·
                  refine ⟨109275073258339133621299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145700097677785511495065 109275073258339133621299)
                  ·
                    rfl

theorem cell20_239414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_239414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239414 prefixEnd_239414 := by exact prefixLift 239414
  have htrace : WordTrace (prefixWord ++ tailWord_239414) baseStart_239414 baseEnd_239414 := by
    simpa [prefixWord, tailWord_239414, baseEnd_239414] using wordTrace_append hprefix tailTrace_239414
  have hstable : (prefixWord ++ tailWord_239414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239414).length < 2 ^ (prefixWord ++ tailWord_239414).sum := by decide
  have hdescent : baseEnd_239414 < baseStart_239414 := by decide
  rcases family_descends (prefixWord ++ tailWord_239414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239432 : List Nat := [2, 1, 3, 1, 1, 4, 2, 3, 3]
def baseStart_239432 : Nat := 118140960795 + 239432 * 2 ^ 59
def prefixEnd_239432 : Nat := 4983230072969 + 3 ^ 40 * 239432 * 2
def baseEnd_239432 : Nat := 109283288948811071021225

theorem tailTrace_239432 : CollatzResearch.WordTrace tailWord_239432 prefixEnd_239432 109283288948811071021225 := by
  unfold tailWord_239432
  simp only [CollatzResearch.WordTrace]
  refine ⟨4366401234293115287576275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5821868312390820383435033 4366401234293115287576275)
  ·
    refine ⟨6549601851439672931364413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4366401234293115287576275 6549601851439672931364413)
    ·
      refine ⟨2456100694289877349261655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6549601851439672931364413 2456100694289877349261655)
      ·
        refine ⟨3684151041434816023892483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2456100694289877349261655 3684151041434816023892483)
        ·
          refine ⟨5526226562152224035838725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3684151041434816023892483 5526226562152224035838725)
          ·
            refine ⟨1036167480403542006719761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5526226562152224035838725 1036167480403542006719761)
            ·
              refine ⟨777125610302656505039821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1036167480403542006719761 777125610302656505039821)
              ·
                refine ⟨291422103863496189389933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 777125610302656505039821 291422103863496189389933)
                ·
                  refine ⟨109283288948811071021225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 291422103863496189389933 109283288948811071021225)
                  ·
                    rfl

theorem cell20_239432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3, 3].length) (baseStart_239432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239432 prefixEnd_239432 := by exact prefixLift 239432
  have htrace : WordTrace (prefixWord ++ tailWord_239432) baseStart_239432 baseEnd_239432 := by
    simpa [prefixWord, tailWord_239432, baseEnd_239432] using wordTrace_append hprefix tailTrace_239432
  have hstable : (prefixWord ++ tailWord_239432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239432).length < 2 ^ (prefixWord ++ tailWord_239432).sum := by decide
  have hdescent : baseEnd_239432 < baseStart_239432 := by decide
  rcases family_descends (prefixWord ++ tailWord_239432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239452 : List Nat := [2, 2, 4, 2, 2, 1, 2, 3, 2]
def baseStart_239452 : Nat := 118140960795 + 239452 * 2 ^ 59
def prefixEnd_239452 : Nat := 4983230072969 + 3 ^ 40 * 239452 * 2
def baseEnd_239452 : Nat := 109292417493779890354477

theorem tailTrace_239452 : CollatzResearch.WordTrace tailWord_239452 prefixEnd_239452 109292417493779890354477 := by
  unfold tailWord_239452
  simp only [CollatzResearch.WordTrace]
  refine ⟨4366765964256886995440305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5822354619009182660587073 4366765964256886995440305)
  ·
    refine ⟨3275074473192665246580229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4366765964256886995440305 3275074473192665246580229)
    ·
      refine ⟨614076463723624733733793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3275074473192665246580229 614076463723624733733793)
      ·
        refine ⟨460557347792718550300345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 614076463723624733733793 460557347792718550300345)
        ·
          refine ⟨345418010844538912725259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 460557347792718550300345 345418010844538912725259)
          ·
            refine ⟨518127016266808369087889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345418010844538912725259 518127016266808369087889)
            ·
              refine ⟨388595262200106276815917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 518127016266808369087889 388595262200106276815917)
              ·
                refine ⟨145723223325039853805969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 388595262200106276815917 145723223325039853805969)
                ·
                  refine ⟨109292417493779890354477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145723223325039853805969 109292417493779890354477)
                  ·
                    rfl

theorem cell20_239452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 3, 2].length) (baseStart_239452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239452 prefixEnd_239452 := by exact prefixLift 239452
  have htrace : WordTrace (prefixWord ++ tailWord_239452) baseStart_239452 baseEnd_239452 := by
    simpa [prefixWord, tailWord_239452, baseEnd_239452] using wordTrace_append hprefix tailTrace_239452
  have hstable : (prefixWord ++ tailWord_239452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239452).length < 2 ^ (prefixWord ++ tailWord_239452).sum := by decide
  have hdescent : baseEnd_239452 < baseStart_239452 := by decide
  rcases family_descends (prefixWord ++ tailWord_239452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239456 : List Nat := [2, 1, 1, 3, 3, 2, 1, 5, 2]
def baseStart_239456 : Nat := 118140960795 + 239456 * 2 ^ 59
def prefixEnd_239456 : Nat := 4983230072969 + 3 ^ 40 * 239456 * 2
def baseEnd_239456 : Nat := 109294243202773654221127

theorem tailTrace_239456 : CollatzResearch.WordTrace tailWord_239456 prefixEnd_239456 109294243202773654221127 := by
  unfold tailWord_239456
  simp only [CollatzResearch.WordTrace]
  refine ⟨4366838910249641337013111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5822451880332855116017481 4366838910249641337013111)
  ·
    refine ⟨6550258365374462005519667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4366838910249641337013111 6550258365374462005519667)
    ·
      refine ⟨9825387548061693008279501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6550258365374462005519667 9825387548061693008279501)
      ·
        refine ⟨3684520330523134878104813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9825387548061693008279501 3684520330523134878104813)
        ·
          refine ⟨1381695123946175579289305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3684520330523134878104813 1381695123946175579289305)
          ·
            refine ⟨1036271342959631684466979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1381695123946175579289305 1036271342959631684466979)
            ·
              refine ⟨1554407014439447526700469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1036271342959631684466979 1554407014439447526700469)
              ·
                refine ⟨145725657603698205628169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1554407014439447526700469 145725657603698205628169)
                ·
                  refine ⟨109294243202773654221127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145725657603698205628169 109294243202773654221127)
                  ·
                    rfl

theorem cell20_239456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 5, 2].length) (baseStart_239456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239456 prefixEnd_239456 := by exact prefixLift 239456
  have htrace : WordTrace (prefixWord ++ tailWord_239456) baseStart_239456 baseEnd_239456 := by
    simpa [prefixWord, tailWord_239456, baseEnd_239456] using wordTrace_append hprefix tailTrace_239456
  have hstable : (prefixWord ++ tailWord_239456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239456).length < 2 ^ (prefixWord ++ tailWord_239456).sum := by decide
  have hdescent : baseEnd_239456 < baseStart_239456 := by decide
  rcases family_descends (prefixWord ++ tailWord_239456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239508 : List Nat := [2, 4, 2, 1, 1, 2, 1, 2, 5]
def baseStart_239508 : Nat := 118140960795 + 239508 * 2 ^ 59
def prefixEnd_239508 : Nat := 4983230072969 + 3 ^ 40 * 239508 * 2
def baseEnd_239508 : Nat := 109317977419692584487581

theorem tailTrace_239508 : CollatzResearch.WordTrace tailWord_239508 prefixEnd_239508 109317977419692584487581 := by
  unfold tailWord_239508
  simp only [CollatzResearch.WordTrace]
  refine ⟨4367787208155447777459589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5823716277540597036612785 4367787208155447777459589)
  ·
    refine ⟨818960101529146458273673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4367787208155447777459589 818960101529146458273673)
    ·
      refine ⟨614220076146859843705255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 818960101529146458273673 614220076146859843705255)
      ·
        refine ⟨921330114220289765557883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614220076146859843705255 921330114220289765557883)
        ·
          refine ⟨1381995171330434648336825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 921330114220289765557883 1381995171330434648336825)
          ·
            refine ⟨1036496378497825986252619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1381995171330434648336825 1036496378497825986252619)
            ·
              refine ⟨1554744567746738979378929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1036496378497825986252619 1554744567746738979378929)
              ·
                refine ⟨1166058425810054234534197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1554744567746738979378929 1166058425810054234534197)
                ·
                  refine ⟨109317977419692584487581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1166058425810054234534197 109317977419692584487581)
                  ·
                    rfl

theorem cell20_239508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_239508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239508 prefixEnd_239508 := by exact prefixLift 239508
  have htrace : WordTrace (prefixWord ++ tailWord_239508) baseStart_239508 baseEnd_239508 := by
    simpa [prefixWord, tailWord_239508, baseEnd_239508] using wordTrace_append hprefix tailTrace_239508
  have hstable : (prefixWord ++ tailWord_239508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239508).length < 2 ^ (prefixWord ++ tailWord_239508).sum := by decide
  have hdescent : baseEnd_239508 < baseStart_239508 := by decide
  rcases family_descends (prefixWord ++ tailWord_239508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239511 : List Nat := [1, 1, 3, 3, 1, 5, 1, 3, 2]
def baseStart_239511 : Nat := 118140960795 + 239511 * 2 ^ 59
def prefixEnd_239511 : Nat := 4983230072969 + 3 ^ 40 * 239511 * 2
def baseEnd_239511 : Nat := 109319346701437907387569

theorem tailTrace_239511 : CollatzResearch.WordTrace tailWord_239511 prefixEnd_239511 109319346701437907387569 := by
  unfold tailWord_239511
  simp only [CollatzResearch.WordTrace]
  refine ⟨8735683835300027067278387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5823789223533351378185591 8735683835300027067278387)
  ·
    refine ⟨13103525752950040600917581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8735683835300027067278387 13103525752950040600917581)
    ·
      refine ⟨4913822157356265225344093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13103525752950040600917581 4913822157356265225344093)
      ·
        refine ⟨1842683309008599459504035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4913822157356265225344093 1842683309008599459504035)
        ·
          refine ⟨2764024963512899189256053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1842683309008599459504035 2764024963512899189256053)
          ·
            refine ⟨259127340329334298992755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2764024963512899189256053 259127340329334298992755)
            ·
              refine ⟨388691010494001448489133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259127340329334298992755 388691010494001448489133)
              ·
                refine ⟨145759128935250543183425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 388691010494001448489133 145759128935250543183425)
                ·
                  refine ⟨109319346701437907387569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145759128935250543183425 109319346701437907387569)
                  ·
                    rfl

theorem cell20_239511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 3, 2].length) (baseStart_239511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239511 prefixEnd_239511 := by exact prefixLift 239511
  have htrace : WordTrace (prefixWord ++ tailWord_239511) baseStart_239511 baseEnd_239511 := by
    simpa [prefixWord, tailWord_239511, baseEnd_239511] using wordTrace_append hprefix tailTrace_239511
  have hstable : (prefixWord ++ tailWord_239511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239511).length < 2 ^ (prefixWord ++ tailWord_239511).sum := by decide
  have hdescent : baseEnd_239511 < baseStart_239511 := by decide
  rcases family_descends (prefixWord ++ tailWord_239511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239528 : List Nat := [2, 1, 6, 2, 1, 2, 1, 1, 4]
def baseStart_239528 : Nat := 118140960795 + 239528 * 2 ^ 59
def prefixEnd_239528 : Nat := 4983230072969 + 3 ^ 40 * 239528 * 2
def baseEnd_239528 : Nat := 109327105964661403820833

theorem tailTrace_239528 : CollatzResearch.WordTrace tailWord_239528 prefixEnd_239528 109327105964661403820833 := by
  unfold tailWord_239528
  simp only [CollatzResearch.WordTrace]
  refine ⟨4368151938119219485323619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5824202584158959313764825 4368151938119219485323619)
  ·
    refine ⟨6552227907178829227985429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4368151938119219485323619 6552227907178829227985429)
    ·
      refine ⟨307135683149007620061817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6552227907178829227985429 307135683149007620061817)
      ·
        refine ⟨230351762361755715046363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307135683149007620061817 230351762361755715046363)
        ·
          refine ⟨345527643542633572569545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230351762361755715046363 345527643542633572569545)
          ·
            refine ⟨259145732656975179427159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345527643542633572569545 259145732656975179427159)
            ·
              refine ⟨388718598985462769140739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259145732656975179427159 388718598985462769140739)
              ·
                refine ⟨583077898478194153711109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 388718598985462769140739 583077898478194153711109)
                ·
                  refine ⟨109327105964661403820833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 583077898478194153711109 109327105964661403820833)
                  ·
                    rfl

theorem cell20_239528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 4].length) (baseStart_239528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239528 prefixEnd_239528 := by exact prefixLift 239528
  have htrace : WordTrace (prefixWord ++ tailWord_239528) baseStart_239528 baseEnd_239528 := by
    simpa [prefixWord, tailWord_239528, baseEnd_239528] using wordTrace_append hprefix tailTrace_239528
  have hstable : (prefixWord ++ tailWord_239528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239528).length < 2 ^ (prefixWord ++ tailWord_239528).sum := by decide
  have hdescent : baseEnd_239528 < baseStart_239528 := by decide
  rcases family_descends (prefixWord ++ tailWord_239528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239560 : List Nat := [2, 1, 3, 1, 4, 1, 2, 6]
def baseStart_239560 : Nat := 118140960795 + 239560 * 2 ^ 59
def prefixEnd_239560 : Nat := 4983230072969 + 3 ^ 40 * 239560 * 2
def baseEnd_239560 : Nat := 36447237212203838251345

theorem tailTrace_239560 : CollatzResearch.WordTrace tailWord_239560 prefixEnd_239560 36447237212203838251345 := by
  unfold tailWord_239560
  simp only [CollatzResearch.WordTrace]
  refine ⟨4368735506061254217906067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5824980674748338957208089 4368735506061254217906067)
  ·
    refine ⟨6553103259091881326859101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4368735506061254217906067 6553103259091881326859101)
    ·
      refine ⟨2457413722159455497572163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6553103259091881326859101 2457413722159455497572163)
      ·
        refine ⟨3686120583239183246358245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2457413722159455497572163 3686120583239183246358245)
        ·
          refine ⟨691147609357346858692171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3686120583239183246358245 691147609357346858692171)
          ·
            refine ⟨1036721414036020288038257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 691147609357346858692171 1036721414036020288038257)
            ·
              refine ⟨777541060527015216028693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1036721414036020288038257 777541060527015216028693)
              ·
                refine ⟨36447237212203838251345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 777541060527015216028693 36447237212203838251345)
                ·
                  rfl

theorem cell20_239560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 6].length) (baseStart_239560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239560 prefixEnd_239560 := by exact prefixLift 239560
  have htrace : WordTrace (prefixWord ++ tailWord_239560) baseStart_239560 baseEnd_239560 := by
    simpa [prefixWord, tailWord_239560, baseEnd_239560] using wordTrace_append hprefix tailTrace_239560
  have hstable : (prefixWord ++ tailWord_239560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239560).length < 2 ^ (prefixWord ++ tailWord_239560).sum := by decide
  have hdescent : baseEnd_239560 < baseStart_239560 := by decide
  rcases family_descends (prefixWord ++ tailWord_239560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239587 : List Nat := [1, 1, 1, 6, 1, 2, 4, 2, 2]
def baseStart_239587 : Nat := 118140960795 + 239587 * 2 ^ 59
def prefixEnd_239587 : Nat := 4983230072969 + 3 ^ 40 * 239587 * 2
def baseEnd_239587 : Nat := 109354035172319420853925

theorem tailTrace_239587 : CollatzResearch.WordTrace tailWord_239587 prefixEnd_239587 109354035172319420853925 := by
  unfold tailWord_239587
  simp only [CollatzResearch.WordTrace]
  refine ⟨8738455783024692047045015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5825637188683128031363343 8738455783024692047045015)
  ·
    refine ⟨13107683674537038070567523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8738455783024692047045015 13107683674537038070567523)
    ·
      refine ⟨19661525511805557105851285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13107683674537038070567523 19661525511805557105851285)
      ·
        refine ⟨921634008365885489336779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19661525511805557105851285 921634008365885489336779)
        ·
          refine ⟨1382451012548828234005169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 921634008365885489336779 1382451012548828234005169)
          ·
            refine ⟨1036838259411621175503877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1382451012548828234005169 1036838259411621175503877)
            ·
              refine ⟨194407173639678970406977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1036838259411621175503877 194407173639678970406977)
              ·
                refine ⟨145805380229759227805233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194407173639678970406977 145805380229759227805233)
                ·
                  refine ⟨109354035172319420853925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145805380229759227805233 109354035172319420853925)
                  ·
                    rfl

theorem cell20_239587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 2, 2].length) (baseStart_239587 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239587 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239587 prefixEnd_239587 := by exact prefixLift 239587
  have htrace : WordTrace (prefixWord ++ tailWord_239587) baseStart_239587 baseEnd_239587 := by
    simpa [prefixWord, tailWord_239587, baseEnd_239587] using wordTrace_append hprefix tailTrace_239587
  have hstable : (prefixWord ++ tailWord_239587).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239587).length < 2 ^ (prefixWord ++ tailWord_239587).sum := by decide
  have hdescent : baseEnd_239587 < baseStart_239587 := by decide
  rcases family_descends (prefixWord ++ tailWord_239587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239619 : List Nat := [1, 1, 1, 3, 2, 1, 1, 10]
def baseStart_239619 : Nat := 118140960795 + 239619 * 2 ^ 59
def prefixEnd_239619 : Nat := 4983230072969 + 3 ^ 40 * 239619 * 2
def baseEnd_239619 : Nat := 36456213614756510595709

theorem tailTrace_239619 : CollatzResearch.WordTrace tailWord_239619 prefixEnd_239619 36456213614756510595709 := by
  unfold tailWord_239619
  simp only [CollatzResearch.WordTrace]
  refine ⟨8739622918908761512209911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5826415279272507674806607 8739622918908761512209911)
  ·
    refine ⟨13109434378363142268314867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8739622918908761512209911 13109434378363142268314867)
    ·
      refine ⟨19664151567544713402472301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13109434378363142268314867 19664151567544713402472301)
      ·
        refine ⟨7374056837829267525927113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19664151567544713402472301 7374056837829267525927113)
        ·
          refine ⟨5530542628371950644445335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7374056837829267525927113 5530542628371950644445335)
          ·
            refine ⟨8295813942557925966668003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5530542628371950644445335 8295813942557925966668003)
            ·
              refine ⟨12443720913836888950002005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8295813942557925966668003 12443720913836888950002005)
              ·
                refine ⟨36456213614756510595709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 12443720913836888950002005 36456213614756510595709)
                ·
                  rfl

theorem cell20_239619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 10].length) (baseStart_239619 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239619 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239619 prefixEnd_239619 := by exact prefixLift 239619
  have htrace : WordTrace (prefixWord ++ tailWord_239619) baseStart_239619 baseEnd_239619 := by
    simpa [prefixWord, tailWord_239619, baseEnd_239619] using wordTrace_append hprefix tailTrace_239619
  have hstable : (prefixWord ++ tailWord_239619).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239619).length < 2 ^ (prefixWord ++ tailWord_239619).sum := by decide
  have hdescent : baseEnd_239619 < baseStart_239619 := by decide
  rcases family_descends (prefixWord ++ tailWord_239619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239643 : List Nat := [1, 1, 1, 1, 1, 1, 3, 8, 3]
def baseStart_239643 : Nat := 118140960795 + 239643 * 2 ^ 59
def prefixEnd_239643 : Nat := 4983230072969 + 3 ^ 40 * 239643 * 2
def baseEnd_239643 : Nat := 109379595098232114987029

theorem tailTrace_239643 : CollatzResearch.WordTrace tailWord_239643 prefixEnd_239643 109379595098232114987029 := by
  unfold tailWord_239643
  simp only [CollatzResearch.WordTrace]
  refine ⟨8740498270821813611083583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5826998847214542407389055 8740498270821813611083583)
  ·
    refine ⟨13110747406232720416625375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8740498270821813611083583 13110747406232720416625375)
    ·
      refine ⟨19666121109349080624938063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13110747406232720416625375 19666121109349080624938063)
      ·
        refine ⟨29499181664023620937407095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19666121109349080624938063 29499181664023620937407095)
        ·
          refine ⟨44248772496035431406110643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29499181664023620937407095 44248772496035431406110643)
          ·
            refine ⟨66373158744053147109165965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44248772496035431406110643 66373158744053147109165965)
            ·
              refine ⟨24889934529019930165937237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66373158744053147109165965 24889934529019930165937237)
              ·
                refine ⟨291678920261952306632077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 24889934529019930165937237 291678920261952306632077)
                ·
                  refine ⟨109379595098232114987029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 291678920261952306632077 109379595098232114987029)
                  ·
                    rfl

theorem cell20_239643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8, 3].length) (baseStart_239643 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239643 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239643 prefixEnd_239643 := by exact prefixLift 239643
  have htrace : WordTrace (prefixWord ++ tailWord_239643) baseStart_239643 baseEnd_239643 := by
    simpa [prefixWord, tailWord_239643, baseEnd_239643] using wordTrace_append hprefix tailTrace_239643
  have hstable : (prefixWord ++ tailWord_239643).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239643).length < 2 ^ (prefixWord ++ tailWord_239643).sum := by decide
  have hdescent : baseEnd_239643 < baseStart_239643 := by decide
  rcases family_descends (prefixWord ++ tailWord_239643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239701 : List Nat := [1, 3, 2, 2, 1, 4, 3, 2, 2]
def baseStart_239701 : Nat := 118140960795 + 239701 * 2 ^ 59
def prefixEnd_239701 : Nat := 4983230072969 + 3 ^ 40 * 239701 * 2
def baseEnd_239701 : Nat := 109406067878641691053459

theorem tailTrace_239701 : CollatzResearch.WordTrace tailWord_239701 prefixEnd_239701 109406067878641691053459 := by
  unfold tailWord_239701
  simp only [CollatzResearch.WordTrace]
  refine ⟨8742613704611689516694957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5828409136407793011129971 8742613704611689516694957)
  ·
    refine ⟨3278480139229383568760609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8742613704611689516694957 3278480139229383568760609)
    ·
      refine ⟨2458860104422037676570457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3278480139229383568760609 2458860104422037676570457)
      ·
        refine ⟨1844145078316528257427843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2458860104422037676570457 1844145078316528257427843)
        ·
          refine ⟨2766217617474792386141765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1844145078316528257427843 2766217617474792386141765)
          ·
            refine ⟨518665803276523572401581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2766217617474792386141765 518665803276523572401581)
            ·
              refine ⟨194499676228696339650593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 518665803276523572401581 194499676228696339650593)
              ·
                refine ⟨145874757171522254737945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194499676228696339650593 145874757171522254737945)
                ·
                  refine ⟨109406067878641691053459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145874757171522254737945 109406067878641691053459)
                  ·
                    rfl

theorem cell20_239701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 2, 2].length) (baseStart_239701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239701 prefixEnd_239701 := by exact prefixLift 239701
  have htrace : WordTrace (prefixWord ++ tailWord_239701) baseStart_239701 baseEnd_239701 := by
    simpa [prefixWord, tailWord_239701, baseEnd_239701] using wordTrace_append hprefix tailTrace_239701
  have hstable : (prefixWord ++ tailWord_239701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239701).length < 2 ^ (prefixWord ++ tailWord_239701).sum := by decide
  have hdescent : baseEnd_239701 < baseStart_239701 := by decide
  rcases family_descends (prefixWord ++ tailWord_239701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239712 : List Nat := [2, 1, 1, 3, 2, 4, 2, 5]
def baseStart_239712 : Nat := 118140960795 + 239712 * 2 ^ 59
def prefixEnd_239712 : Nat := 4983230072969 + 3 ^ 40 * 239712 * 2
def baseEnd_239712 : Nat := 36470362859458180562249

theorem tailTrace_239712 : CollatzResearch.WordTrace tailWord_239712 prefixEnd_239712 36470362859458180562249 := by
  unfold tailWord_239712
  simp only [CollatzResearch.WordTrace]
  refine ⟨4371507453785919197672695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5828676605047892263563593 4371507453785919197672695)
  ·
    refine ⟨6557261180678878796509043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4371507453785919197672695 6557261180678878796509043)
    ·
      refine ⟨9835891771018318194763565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6557261180678878796509043 9835891771018318194763565)
      ·
        refine ⟨3688459414131869323036337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9835891771018318194763565 3688459414131869323036337)
        ·
          refine ⟨2766344560598901992277253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3688459414131869323036337 2766344560598901992277253)
          ·
            refine ⟨518689605112294123551985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2766344560598901992277253 518689605112294123551985)
            ·
              refine ⟨389017203834220592663989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 518689605112294123551985 389017203834220592663989)
              ·
                refine ⟨36470362859458180562249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 389017203834220592663989 36470362859458180562249)
                ·
                  rfl

theorem cell20_239712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 5].length) (baseStart_239712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239712 prefixEnd_239712 := by exact prefixLift 239712
  have htrace : WordTrace (prefixWord ++ tailWord_239712) baseStart_239712 baseEnd_239712 := by
    simpa [prefixWord, tailWord_239712, baseEnd_239712] using wordTrace_append hprefix tailTrace_239712
  have hstable : (prefixWord ++ tailWord_239712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239712).length < 2 ^ (prefixWord ++ tailWord_239712).sum := by decide
  have hdescent : baseEnd_239712 < baseStart_239712 := by decide
  rcases family_descends (prefixWord ++ tailWord_239712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239767 : List Nat := [1, 1, 3, 3, 4, 2, 1, 5]
def baseStart_239767 : Nat := 118140960795 + 239767 * 2 ^ 59
def prefixEnd_239767 : Nat := 4983230072969 + 3 ^ 40 * 239767 * 2
def baseEnd_239767 : Nat := 36478730692346264951063

theorem tailTrace_239767 : CollatzResearch.WordTrace tailWord_239767 prefixEnd_239767 36478730692346264951063 := by
  unfold tailWord_239767
  simp only [CollatzResearch.WordTrace]
  refine ⟨8745020922372582788597555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5830013948248388525731703 8745020922372582788597555)
  ·
    refine ⟨13117531383558874182896333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8745020922372582788597555 13117531383558874182896333)
    ·
      refine ⟨4919074268834577818586125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13117531383558874182896333 4919074268834577818586125)
      ·
        refine ⟨1844652850812966681969797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4919074268834577818586125 1844652850812966681969797)
        ·
          refine ⟨345872409527431252869337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1844652850812966681969797 345872409527431252869337)
          ·
            refine ⟨259404307145573439652003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345872409527431252869337 259404307145573439652003)
            ·
              refine ⟨389106460718360159478005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259404307145573439652003 389106460718360159478005)
              ·
                refine ⟨36478730692346264951063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 389106460718360159478005 36478730692346264951063)
                ·
                  rfl

theorem cell20_239767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 5].length) (baseStart_239767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239767 prefixEnd_239767 := by exact prefixLift 239767
  have htrace : WordTrace (prefixWord ++ tailWord_239767) baseStart_239767 baseEnd_239767 := by
    simpa [prefixWord, tailWord_239767, baseEnd_239767] using wordTrace_append hprefix tailTrace_239767
  have hstable : (prefixWord ++ tailWord_239767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239767).length < 2 ^ (prefixWord ++ tailWord_239767).sum := by decide
  have hdescent : baseEnd_239767 < baseStart_239767 := by decide
  rcases family_descends (prefixWord ++ tailWord_239767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239812 : List Nat := [2, 3, 3, 1, 2, 2, 1, 1, 5]
def baseStart_239812 : Nat := 118140960795 + 239812 * 2 ^ 59
def prefixEnd_239812 : Nat := 4983230072969 + 3 ^ 40 * 239812 * 2
def baseEnd_239812 : Nat := 109456731303218638353005

theorem tailTrace_239812 : CollatzResearch.WordTrace tailWord_239812 prefixEnd_239812 109456731303218638353005 := by
  unfold tailWord_239812
  simp only [CollatzResearch.WordTrace]
  refine ⟨4373331103604777736992845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5831108138139703649323793 4373331103604777736992845)
  ·
    refine ⟨1639999163851791651372317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4373331103604777736992845 1639999163851791651372317)
    ·
      refine ⟨614999686444421869264619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1639999163851791651372317 614999686444421869264619)
      ·
        refine ⟨922499529666632803896929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614999686444421869264619 922499529666632803896929)
        ·
          refine ⟨691874647249974602922697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 922499529666632803896929 691874647249974602922697)
          ·
            refine ⟨518905985437480952192023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 691874647249974602922697 518905985437480952192023)
            ·
              refine ⟨778358978156221428288035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518905985437480952192023 778358978156221428288035)
              ·
                refine ⟨1167538467234332142432053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 778358978156221428288035 1167538467234332142432053)
                ·
                  refine ⟨109456731303218638353005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1167538467234332142432053 109456731303218638353005)
                  ·
                    rfl

theorem cell20_239812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_239812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239812 prefixEnd_239812 := by exact prefixLift 239812
  have htrace : WordTrace (prefixWord ++ tailWord_239812) baseStart_239812 baseEnd_239812 := by
    simpa [prefixWord, tailWord_239812, baseEnd_239812] using wordTrace_append hprefix tailTrace_239812
  have hstable : (prefixWord ++ tailWord_239812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239812).length < 2 ^ (prefixWord ++ tailWord_239812).sum := by decide
  have hdescent : baseEnd_239812 < baseStart_239812 := by decide
  rcases family_descends (prefixWord ++ tailWord_239812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239819 : List Nat := [1, 1, 1, 1, 3, 2, 3, 6, 2]
def baseStart_239819 : Nat := 118140960795 + 239819 * 2 ^ 59
def prefixEnd_239819 : Nat := 4983230072969 + 3 ^ 40 * 239819 * 2
def baseEnd_239819 : Nat := 109459926293957725119643

theorem tailTrace_239819 : CollatzResearch.WordTrace tailWord_239819 prefixEnd_239819 109459926293957725119643 := by
  unfold tailWord_239819
  simp only [CollatzResearch.WordTrace]
  refine ⟨8746917518184195669490511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5831278345456130446327007 8746917518184195669490511)
  ·
    refine ⟨13120376277276293504235767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8746917518184195669490511 13120376277276293504235767)
    ·
      refine ⟨19680564415914440256353651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13120376277276293504235767 19680564415914440256353651)
      ·
        refine ⟨29520846623871660384530477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19680564415914440256353651 29520846623871660384530477)
        ·
          refine ⟨11070317483951872644198929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29520846623871660384530477 11070317483951872644198929)
          ·
            refine ⟨8302738112963904483149197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11070317483951872644198929 8302738112963904483149197)
            ·
              refine ⟨3113526792361464181180949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8302738112963904483149197 3113526792361464181180949)
              ·
                refine ⟨145946568391943633492857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3113526792361464181180949 145946568391943633492857)
                ·
                  refine ⟨109459926293957725119643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145946568391943633492857 109459926293957725119643)
                  ·
                    rfl

theorem cell20_239819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 6, 2].length) (baseStart_239819 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239819 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239819 prefixEnd_239819 := by exact prefixLift 239819
  have htrace : WordTrace (prefixWord ++ tailWord_239819) baseStart_239819 baseEnd_239819 := by
    simpa [prefixWord, tailWord_239819, baseEnd_239819] using wordTrace_append hprefix tailTrace_239819
  have hstable : (prefixWord ++ tailWord_239819).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239819).length < 2 ^ (prefixWord ++ tailWord_239819).sum := by decide
  have hdescent : baseEnd_239819 < baseStart_239819 := by decide
  rcases family_descends (prefixWord ++ tailWord_239819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239833 : List Nat := [1, 2, 1, 2, 3, 1, 2, 5, 3]
def baseStart_239833 : Nat := 118140960795 + 239833 * 2 ^ 59
def prefixEnd_239833 : Nat := 4983230072969 + 3 ^ 40 * 239833 * 2
def baseEnd_239833 : Nat := 109466316275435898652919

theorem tailTrace_239833 : CollatzResearch.WordTrace tailWord_239833 prefixEnd_239833 109466316275435898652919 := by
  unfold tailWord_239833
  simp only [CollatzResearch.WordTrace]
  refine ⟨8747428140133476060500153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5831618760088984040333435 8747428140133476060500153)
  ·
    refine ⟨6560571105100107045375115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8747428140133476060500153 6560571105100107045375115)
    ·
      refine ⟨9840856657650160568062673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6560571105100107045375115 9840856657650160568062673)
      ·
        refine ⟨7380642493237620426047005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9840856657650160568062673 7380642493237620426047005)
        ·
          refine ⟨2767740934964107659767627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7380642493237620426047005 2767740934964107659767627)
          ·
            refine ⟨4151611402446161489651441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2767740934964107659767627 4151611402446161489651441)
            ·
              refine ⟨3113708551834621117238581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4151611402446161489651441 3113708551834621117238581)
              ·
                refine ⟨291910176734495729741117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3113708551834621117238581 291910176734495729741117)
                ·
                  refine ⟨109466316275435898652919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 291910176734495729741117 109466316275435898652919)
                  ·
                    rfl

theorem cell20_239833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5, 3].length) (baseStart_239833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239833 prefixEnd_239833 := by exact prefixLift 239833
  have htrace : WordTrace (prefixWord ++ tailWord_239833) baseStart_239833 baseEnd_239833 := by
    simpa [prefixWord, tailWord_239833, baseEnd_239833] using wordTrace_append hprefix tailTrace_239833
  have hstable : (prefixWord ++ tailWord_239833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239833).length < 2 ^ (prefixWord ++ tailWord_239833).sum := by decide
  have hdescent : baseEnd_239833 < baseStart_239833 := by decide
  rcases family_descends (prefixWord ++ tailWord_239833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239840 : List Nat := [2, 1, 1, 3, 1, 3, 1, 4, 4]
def baseStart_239840 : Nat := 118140960795 + 239840 * 2 ^ 59
def prefixEnd_239840 : Nat := 4983230072969 + 3 ^ 40 * 239840 * 2
def baseEnd_239840 : Nat := 109469511266174985419557

theorem tailTrace_239840 : CollatzResearch.WordTrace tailWord_239840 prefixEnd_239840 109469511266174985419557 := by
  unfold tailWord_239840
  simp only [CollatzResearch.WordTrace]
  refine ⟨4373841725554058128002487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5831788967405410837336649 4373841725554058128002487)
  ·
    refine ⟨6560762588331087192003731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4373841725554058128002487 6560762588331087192003731)
    ·
      refine ⟨9841143882496630788005597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6560762588331087192003731 9841143882496630788005597)
      ·
        refine ⟨3690428955936236545502099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9841143882496630788005597 3690428955936236545502099)
        ·
          refine ⟨5535643433904354818253149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3690428955936236545502099 5535643433904354818253149)
          ·
            refine ⟨2075866287714133056844931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5535643433904354818253149 2075866287714133056844931)
            ·
              refine ⟨3113799431571199585267397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2075866287714133056844931 3113799431571199585267397)
              ·
                refine ⟨583837393419599922237637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3113799431571199585267397 583837393419599922237637)
                ·
                  refine ⟨109469511266174985419557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 583837393419599922237637 109469511266174985419557)
                  ·
                    rfl

theorem cell20_239840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 4].length) (baseStart_239840 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239840 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239840 prefixEnd_239840 := by exact prefixLift 239840
  have htrace : WordTrace (prefixWord ++ tailWord_239840) baseStart_239840 baseEnd_239840 := by
    simpa [prefixWord, tailWord_239840, baseEnd_239840] using wordTrace_append hprefix tailTrace_239840
  have hstable : (prefixWord ++ tailWord_239840).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239840).length < 2 ^ (prefixWord ++ tailWord_239840).sum := by decide
  have hdescent : baseEnd_239840 < baseStart_239840 := by decide
  rcases family_descends (prefixWord ++ tailWord_239840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239843 : List Nat := [1, 1, 1, 8, 1, 1, 1, 6]
def baseStart_239843 : Nat := 118140960795 + 239843 * 2 ^ 59
def prefixEnd_239843 : Nat := 4983230072969 + 3 ^ 40 * 239843 * 2
def baseEnd_239843 : Nat := 36490293515973436106515

theorem tailTrace_239843 : CollatzResearch.WordTrace tailWord_239843 prefixEnd_239843 36490293515973436106515 := by
  unfold tailWord_239843
  simp only [CollatzResearch.WordTrace]
  refine ⟨8747792870097247768364183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5831861913398165178909455 8747792870097247768364183)
  ·
    refine ⟨13121689305145871652546275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8747792870097247768364183 13121689305145871652546275)
    ·
      refine ⟨19682533957718807478819413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13121689305145871652546275 19682533957718807478819413)
      ·
        refine ⟨230654694817017275142415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 19682533957718807478819413 230654694817017275142415)
        ·
          refine ⟨345982042225525912713623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230654694817017275142415 345982042225525912713623)
          ·
            refine ⟨518973063338288869070435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345982042225525912713623 518973063338288869070435)
            ·
              refine ⟨778459595007433303605653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518973063338288869070435 778459595007433303605653)
              ·
                refine ⟨36490293515973436106515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 778459595007433303605653 36490293515973436106515)
                ·
                  rfl

theorem cell20_239843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 6].length) (baseStart_239843 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239843 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239843 prefixEnd_239843 := by exact prefixLift 239843
  have htrace : WordTrace (prefixWord ++ tailWord_239843) baseStart_239843 baseEnd_239843 := by
    simpa [prefixWord, tailWord_239843, baseEnd_239843] using wordTrace_append hprefix tailTrace_239843
  have hstable : (prefixWord ++ tailWord_239843).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239843).length < 2 ^ (prefixWord ++ tailWord_239843).sum := by decide
  have hdescent : baseEnd_239843 < baseStart_239843 := by decide
  rcases family_descends (prefixWord ++ tailWord_239843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239871 : List Nat := [1, 1, 2, 2, 1, 4, 2, 4, 3]
def baseStart_239871 : Nat := 118140960795 + 239871 * 2 ^ 59
def prefixEnd_239871 : Nat := 4983230072969 + 3 ^ 40 * 239871 * 2
def baseEnd_239871 : Nat := 109483660510876655386097

theorem tailTrace_239871 : CollatzResearch.WordTrace tailWord_239871 prefixEnd_239871 109483660510876655386097 := by
  unfold tailWord_239871
  simp only [CollatzResearch.WordTrace]
  refine ⟨8748814113995808550383467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5832542742663872366922311 8748814113995808550383467)
  ·
    refine ⟨13123221170993712825575201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8748814113995808550383467 13123221170993712825575201)
    ·
      refine ⟨9842415878245284619181401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13123221170993712825575201 9842415878245284619181401)
      ·
        refine ⟨7381811908683963464386051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9842415878245284619181401 7381811908683963464386051)
        ·
          refine ⟨11072717863025945196579077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7381811908683963464386051 11072717863025945196579077)
          ·
            refine ⟨2076134599317364724358577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11072717863025945196579077 2076134599317364724358577)
            ·
              refine ⟨1557100949488023543268933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2076134599317364724358577 1557100949488023543268933)
              ·
                refine ⟨291956428029004414362925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1557100949488023543268933 291956428029004414362925)
                ·
                  refine ⟨109483660510876655386097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 291956428029004414362925 109483660510876655386097)
                  ·
                    rfl

theorem cell20_239871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4, 3].length) (baseStart_239871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239871 prefixEnd_239871 := by exact prefixLift 239871
  have htrace : WordTrace (prefixWord ++ tailWord_239871) baseStart_239871 baseEnd_239871 := by
    simpa [prefixWord, tailWord_239871, baseEnd_239871] using wordTrace_append hprefix tailTrace_239871
  have hstable : (prefixWord ++ tailWord_239871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239871).length < 2 ^ (prefixWord ++ tailWord_239871).sum := by decide
  have hdescent : baseEnd_239871 < baseStart_239871 := by decide
  rcases family_descends (prefixWord ++ tailWord_239871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239874 : List Nat := [3, 4, 1, 1, 2, 1, 3, 1, 4]
def baseStart_239874 : Nat := 118140960795 + 239874 * 2 ^ 59
def prefixEnd_239874 : Nat := 4983230072969 + 3 ^ 40 * 239874 * 2
def baseEnd_239874 : Nat := 109485029792621978286085

theorem tailTrace_239874 : CollatzResearch.WordTrace tailWord_239874 prefixEnd_239874 109485029792621978286085 := by
  unfold tailWord_239874
  simp only [CollatzResearch.WordTrace]
  refine ⟨2187230883246235015685669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5832615688656626708495117 2187230883246235015685669)
  ·
    refine ⟨410105790608669065441063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2187230883246235015685669 410105790608669065441063)
    ·
      refine ⟨615158685913003598161595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410105790608669065441063 615158685913003598161595)
      ·
        refine ⟨922738028869505397242393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 615158685913003598161595 922738028869505397242393)
        ·
          refine ⟨692053521652129047931795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 922738028869505397242393 692053521652129047931795)
          ·
            refine ⟨1038080282478193571897693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 692053521652129047931795 1038080282478193571897693)
            ·
              refine ⟨389280105929322589461635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1038080282478193571897693 389280105929322589461635)
              ·
                refine ⟨583920158893983884192453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 389280105929322589461635 583920158893983884192453)
                ·
                  refine ⟨109485029792621978286085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 583920158893983884192453 109485029792621978286085)
                  ·
                    rfl

theorem cell20_239874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_239874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239874 prefixEnd_239874 := by exact prefixLift 239874
  have htrace : WordTrace (prefixWord ++ tailWord_239874) baseStart_239874 baseEnd_239874 := by
    simpa [prefixWord, tailWord_239874, baseEnd_239874] using wordTrace_append hprefix tailTrace_239874
  have hstable : (prefixWord ++ tailWord_239874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239874).length < 2 ^ (prefixWord ++ tailWord_239874).sum := by decide
  have hdescent : baseEnd_239874 < baseStart_239874 := by decide
  rcases family_descends (prefixWord ++ tailWord_239874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239929 : List Nat := [1, 2, 1, 6, 1, 1, 4, 2, 2]
def baseStart_239929 : Nat := 118140960795 + 239929 * 2 ^ 59
def prefixEnd_239929 : Nat := 4983230072969 + 3 ^ 40 * 239929 * 2
def baseEnd_239929 : Nat := 109510133291286231452527

theorem tailTrace_239929 : CollatzResearch.WordTrace tailWord_239929 prefixEnd_239929 109510133291286231452527 := by
  unfold tailWord_239929
  simp only [CollatzResearch.WordTrace]
  refine ⟨8750929547785684455994841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5833953031857122970663227 8750929547785684455994841)
  ·
    refine ⟨6563197160839263341996131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8750929547785684455994841 6563197160839263341996131)
    ·
      refine ⟨9844795741258895012994197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6563197160839263341996131 9844795741258895012994197)
      ·
        refine ⟨461474800371510703734103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9844795741258895012994197 461474800371510703734103)
        ·
          refine ⟨692212200557266055601155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461474800371510703734103 692212200557266055601155)
          ·
            refine ⟨1038318300835899083401733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 692212200557266055601155 1038318300835899083401733)
            ·
              refine ⟨194684681406731078137825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1038318300835899083401733 194684681406731078137825)
              ·
                refine ⟨146013511055048308603369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194684681406731078137825 146013511055048308603369)
                ·
                  refine ⟨109510133291286231452527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146013511055048308603369 109510133291286231452527)
                  ·
                    rfl

theorem cell20_239929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 2, 2].length) (baseStart_239929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239929 prefixEnd_239929 := by exact prefixLift 239929
  have htrace : WordTrace (prefixWord ++ tailWord_239929) baseStart_239929 baseEnd_239929 := by
    simpa [prefixWord, tailWord_239929, baseEnd_239929] using wordTrace_append hprefix tailTrace_239929
  have hstable : (prefixWord ++ tailWord_239929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239929).length < 2 ^ (prefixWord ++ tailWord_239929).sum := by decide
  have hdescent : baseEnd_239929 < baseStart_239929 := by decide
  rcases family_descends (prefixWord ++ tailWord_239929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239954 : List Nat := [3, 2, 2, 1, 1, 1, 3, 1, 6]
def baseStart_239954 : Nat := 118140960795 + 239954 * 2 ^ 59
def prefixEnd_239954 : Nat := 4983230072969 + 3 ^ 40 * 239954 * 2
def baseEnd_239954 : Nat := 109521543972497255619091

theorem tailTrace_239954 : CollatzResearch.WordTrace tailWord_239954 prefixEnd_239954 109521543972497255619091 := by
  unfold tailWord_239954
  simp only [CollatzResearch.WordTrace]
  refine ⟨2187960343173778431413729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5834560915130075817103277 2187960343173778431413729)
  ·
    refine ⟨1640970257380333823560297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2187960343173778431413729 1640970257380333823560297)
    ·
      refine ⟨1230727693035250367670223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1640970257380333823560297 1230727693035250367670223)
      ·
        refine ⟨1846091539552875551505335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1230727693035250367670223 1846091539552875551505335)
        ·
          refine ⟨2769137309329313327258003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1846091539552875551505335 2769137309329313327258003)
          ·
            refine ⟨4153705963993969990887005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2769137309329313327258003 4153705963993969990887005)
            ·
              refine ⟨1557639736497738746582627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4153705963993969990887005 1557639736497738746582627)
              ·
                refine ⟨2336459604746608119873941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1557639736497738746582627 2336459604746608119873941)
                ·
                  refine ⟨109521543972497255619091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2336459604746608119873941 109521543972497255619091)
                  ·
                    rfl

theorem cell20_239954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_239954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239954 prefixEnd_239954 := by exact prefixLift 239954
  have htrace : WordTrace (prefixWord ++ tailWord_239954) baseStart_239954 baseEnd_239954 := by
    simpa [prefixWord, tailWord_239954, baseEnd_239954] using wordTrace_append hprefix tailTrace_239954
  have hstable : (prefixWord ++ tailWord_239954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239954).length < 2 ^ (prefixWord ++ tailWord_239954).sum := by decide
  have hdescent : baseEnd_239954 < baseStart_239954 := by decide
  rcases family_descends (prefixWord ++ tailWord_239954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239957 : List Nat := [1, 3, 2, 2, 4, 1, 3, 4]
def baseStart_239957 : Nat := 118140960795 + 239957 * 2 ^ 59
def prefixEnd_239957 : Nat := 4983230072969 + 3 ^ 40 * 239957 * 2
def baseEnd_239957 : Nat := 36507637751414192839693

theorem tailTrace_239957 : CollatzResearch.WordTrace tailWord_239957 prefixEnd_239957 36507637751414192839693 := by
  unfold tailWord_239957
  simp only [CollatzResearch.WordTrace]
  refine ⟨8751950791684245238014125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5834633861122830158676083 8751950791684245238014125)
  ·
    refine ⟨3281981546881591964255297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8751950791684245238014125 3281981546881591964255297)
    ·
      refine ⟨2461486160161193973191473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3281981546881591964255297 2461486160161193973191473)
      ·
        refine ⟨1846114620120895479893605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2461486160161193973191473 1846114620120895479893605)
        ·
          refine ⟨346146491272667902480051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1846114620120895479893605 346146491272667902480051)
          ·
            refine ⟨519219736909001853720077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346146491272667902480051 519219736909001853720077)
            ·
              refine ⟨194707401340875695145029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 519219736909001853720077 194707401340875695145029)
              ·
                refine ⟨36507637751414192839693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 194707401340875695145029 36507637751414192839693)
                ·
                  rfl

theorem cell20_239957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 4].length) (baseStart_239957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239957 prefixEnd_239957 := by exact prefixLift 239957
  have htrace : WordTrace (prefixWord ++ tailWord_239957) baseStart_239957 baseEnd_239957 := by
    simpa [prefixWord, tailWord_239957, baseEnd_239957] using wordTrace_append hprefix tailTrace_239957
  have hstable : (prefixWord ++ tailWord_239957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239957).length < 2 ^ (prefixWord ++ tailWord_239957).sum := by decide
  have hdescent : baseEnd_239957 < baseStart_239957 := by decide
  rcases family_descends (prefixWord ++ tailWord_239957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239978 : List Nat := [3, 1, 3, 3, 1, 2, 7]
def baseStart_239978 : Nat := 118140960795 + 239978 * 2 ^ 59
def prefixEnd_239978 : Nat := 4983230072969 + 3 ^ 40 * 239978 * 2
def baseEnd_239978 : Nat := 12170277580717759868777

theorem tailTrace_239978 : CollatzResearch.WordTrace tailWord_239978 prefixEnd_239978 12170277580717759868777 := by
  unfold tailWord_239978
  simp only [CollatzResearch.WordTrace]
  refine ⟨2188179181152041456132147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5835144483072110549685725 2188179181152041456132147)
  ·
    refine ⟨3282268771728062184198221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2188179181152041456132147 3282268771728062184198221)
    ·
      refine ⟨1230850789398023319074333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3282268771728062184198221 1230850789398023319074333)
      ·
        refine ⟨461569046024258744652875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1230850789398023319074333 461569046024258744652875)
        ·
          refine ⟨692353569036388116979313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461569046024258744652875 692353569036388116979313)
          ·
            refine ⟨519265176777291087734485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 692353569036388116979313 519265176777291087734485)
            ·
              refine ⟨12170277580717759868777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 519265176777291087734485 12170277580717759868777)
              ·
                rfl

theorem cell20_239978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 7].length) (baseStart_239978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_239978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_239978 prefixEnd_239978 := by exact prefixLift 239978
  have htrace : WordTrace (prefixWord ++ tailWord_239978) baseStart_239978 baseEnd_239978 := by
    simpa [prefixWord, tailWord_239978, baseEnd_239978] using wordTrace_append hprefix tailTrace_239978
  have hstable : (prefixWord ++ tailWord_239978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239978).length < 2 ^ (prefixWord ++ tailWord_239978).sum := by decide
  have hdescent : baseEnd_239978 < baseStart_239978 := by decide
  rcases family_descends (prefixWord ++ tailWord_239978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240026 : List Nat := [3, 1, 1, 4, 1, 2, 3, 3, 2]
def baseStart_240026 : Nat := 118140960795 + 240026 * 2 ^ 59
def prefixEnd_240026 : Nat := 4983230072969 + 3 ^ 40 * 240026 * 2
def baseEnd_240026 : Nat := 109554406734385005218797

theorem tailTrace_240026 : CollatzResearch.WordTrace tailWord_240026 prefixEnd_240026 109554406734385005218797 := by
  unfold tailWord_240026
  simp only [CollatzResearch.WordTrace]
  refine ⟨2188616857108567505568983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5836311618956180014850621 2188616857108567505568983)
  ·
    refine ⟨3282925285662851258353475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2188616857108567505568983 3282925285662851258353475)
    ·
      refine ⟨4924387928494276887530213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3282925285662851258353475 4924387928494276887530213)
      ·
        refine ⟨923322736592676916411915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4924387928494276887530213 923322736592676916411915)
        ·
          refine ⟨1384984104889015374617873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 923322736592676916411915 1384984104889015374617873)
          ·
            refine ⟨1038738078666761530963405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1384984104889015374617873 1038738078666761530963405)
            ·
              refine ⟨389526779500035574111277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1038738078666761530963405 389526779500035574111277)
              ·
                refine ⟨146072542312513340291729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 389526779500035574111277 146072542312513340291729)
                ·
                  refine ⟨109554406734385005218797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146072542312513340291729 109554406734385005218797)
                  ·
                    rfl

theorem cell20_240026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 3, 2].length) (baseStart_240026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240026 prefixEnd_240026 := by exact prefixLift 240026
  have htrace : WordTrace (prefixWord ++ tailWord_240026) baseStart_240026 baseEnd_240026 := by
    simpa [prefixWord, tailWord_240026, baseEnd_240026] using wordTrace_append hprefix tailTrace_240026
  have hstable : (prefixWord ++ tailWord_240026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240026).length < 2 ^ (prefixWord ++ tailWord_240026).sum := by decide
  have hdescent : baseEnd_240026 < baseStart_240026 := by decide
  rcases family_descends (prefixWord ++ tailWord_240026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240033 : List Nat := [1, 2, 3, 5, 1, 2, 6]
def baseStart_240033 : Nat := 118140960795 + 240033 * 2 ^ 59
def prefixEnd_240033 : Nat := 4983230072969 + 3 ^ 40 * 240033 * 2
def baseEnd_240033 : Nat := 12173066858347121331715

theorem tailTrace_240033 : CollatzResearch.WordTrace tailWord_240033 prefixEnd_240033 12173066858347121331715 := by
  unfold tailWord_240033
  simp only [CollatzResearch.WordTrace]
  refine ⟨8754722739408910217780753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5836481826272606811853835 8754722739408910217780753)
  ·
    refine ⟨6566042054556682663335565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8754722739408910217780753 6566042054556682663335565)
    ·
      refine ⟨2462265770458755998750837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6566042054556682663335565 2462265770458755998750837)
      ·
        refine ⟨230837415980508374882891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2462265770458755998750837 230837415980508374882891)
        ·
          refine ⟨346256123970762562324337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230837415980508374882891 346256123970762562324337)
          ·
            refine ⟨259692092978071921743253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346256123970762562324337 259692092978071921743253)
            ·
              refine ⟨12173066858347121331715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 259692092978071921743253 12173066858347121331715)
              ·
                rfl

theorem cell20_240033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 6].length) (baseStart_240033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240033 prefixEnd_240033 := by exact prefixLift 240033
  have htrace : WordTrace (prefixWord ++ tailWord_240033) baseStart_240033 baseEnd_240033 := by
    simpa [prefixWord, tailWord_240033, baseEnd_240033] using wordTrace_append hprefix tailTrace_240033
  have hstable : (prefixWord ++ tailWord_240033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240033).length < 2 ^ (prefixWord ++ tailWord_240033).sum := by decide
  have hdescent : baseEnd_240033 < baseStart_240033 := by decide
  rcases family_descends (prefixWord ++ tailWord_240033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240040 : List Nat := [2, 1, 6, 1, 1, 1, 2, 1, 5]
def baseStart_240040 : Nat := 118140960795 + 240040 * 2 ^ 59
def prefixEnd_240040 : Nat := 4983230072969 + 3 ^ 40 * 240040 * 2
def baseEnd_240040 : Nat := 109560796715863178752073

theorem tailTrace_240040 : CollatzResearch.WordTrace tailWord_240040 prefixEnd_240040 109560796715863178752073 := by
  unfold tailWord_240040
  simp only [CollatzResearch.WordTrace]
  refine ⟨4377489025191775206642787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5836652033589033608857049 4377489025191775206642787)
  ·
    refine ⟨6566233537787662809964181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4377489025191775206642787 6566233537787662809964181)
    ·
      refine ⟨307792197083796694217071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6566233537787662809964181 307792197083796694217071)
      ·
        refine ⟨461688295625695041325607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307792197083796694217071 461688295625695041325607)
        ·
          refine ⟨692532443438542561988411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461688295625695041325607 692532443438542561988411)
          ·
            refine ⟨1038798665157813842982617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 692532443438542561988411 1038798665157813842982617)
            ·
              refine ⟨779098998868360382236963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1038798665157813842982617 779098998868360382236963)
              ·
                refine ⟨1168648498302540573355445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 779098998868360382236963 1168648498302540573355445)
                ·
                  refine ⟨109560796715863178752073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1168648498302540573355445 109560796715863178752073)
                  ·
                    rfl

theorem cell20_240040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 5].length) (baseStart_240040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240040 prefixEnd_240040 := by exact prefixLift 240040
  have htrace : WordTrace (prefixWord ++ tailWord_240040) baseStart_240040 baseEnd_240040 := by
    simpa [prefixWord, tailWord_240040, baseEnd_240040] using wordTrace_append hprefix tailTrace_240040
  have hstable : (prefixWord ++ tailWord_240040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240040).length < 2 ^ (prefixWord ++ tailWord_240040).sum := by decide
  have hdescent : baseEnd_240040 < baseStart_240040 := by decide
  rcases family_descends (prefixWord ++ tailWord_240040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240057 : List Nat := [1, 2, 1, 4, 3, 3, 2, 1, 3]
def baseStart_240057 : Nat := 118140960795 + 240057 * 2 ^ 59
def prefixEnd_240057 : Nat := 4983230072969 + 3 ^ 40 * 240057 * 2
def baseEnd_240057 : Nat := 109568555979086675185337

theorem tailTrace_240057 : CollatzResearch.WordTrace tailWord_240057 prefixEnd_240057 109568555979086675185337 := by
  unfold tailWord_240057
  simp only [CollatzResearch.WordTrace]
  refine ⟨8755598091321962316654425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5837065394214641544436283 8755598091321962316654425)
  ·
    refine ⟨6566698568491471737490819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8755598091321962316654425 6566698568491471737490819)
    ·
      refine ⟨9850047852737207606236229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6566698568491471737490819 9850047852737207606236229)
      ·
        refine ⟨1846883972388226426169293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9850047852737207606236229 1846883972388226426169293)
        ·
          refine ⟨692581489645584909813485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1846883972388226426169293 692581489645584909813485)
          ·
            refine ⟨259718058617094341180057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 692581489645584909813485 259718058617094341180057)
            ·
              refine ⟨194788543962820755885043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259718058617094341180057 194788543962820755885043)
              ·
                refine ⟨292182815944231133827565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194788543962820755885043 292182815944231133827565)
                ·
                  refine ⟨109568555979086675185337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 292182815944231133827565 109568555979086675185337)
                  ·
                    rfl

theorem cell20_240057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 1, 3].length) (baseStart_240057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240057 prefixEnd_240057 := by exact prefixLift 240057
  have htrace : WordTrace (prefixWord ++ tailWord_240057) baseStart_240057 baseEnd_240057 := by
    simpa [prefixWord, tailWord_240057, baseEnd_240057] using wordTrace_append hprefix tailTrace_240057
  have hstable : (prefixWord ++ tailWord_240057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240057).length < 2 ^ (prefixWord ++ tailWord_240057).sum := by decide
  have hdescent : baseEnd_240057 < baseStart_240057 := by decide
  rcases family_descends (prefixWord ++ tailWord_240057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240098 : List Nat := [3, 3, 3, 2, 1, 1, 1, 4, 2]
def baseStart_240098 : Nat := 118140960795 + 240098 * 2 ^ 59
def prefixEnd_240098 : Nat := 4983230072969 + 3 ^ 40 * 240098 * 2
def baseEnd_240098 : Nat := 109587269496272754818503

theorem tailTrace_240098 : CollatzResearch.WordTrace tailWord_240098 prefixEnd_240098 109587269496272754818503 := by
  unfold tailWord_240098
  simp only [CollatzResearch.WordTrace]
  refine ⟨2189273371043356579724237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5838062322782284212597965 2189273371043356579724237)
  ·
    refine ⟨820977514141258717396589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2189273371043356579724237 820977514141258717396589)
    ·
      refine ⟨307866567802972019023721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 820977514141258717396589 307866567802972019023721)
      ·
        refine ⟨230899925852229014267791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307866567802972019023721 230899925852229014267791)
        ·
          refine ⟨346349888778343521401687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230899925852229014267791 346349888778343521401687)
          ·
            refine ⟨519524833167515282102531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346349888778343521401687 519524833167515282102531)
            ·
              refine ⟨779287249751272923153797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519524833167515282102531 779287249751272923153797)
              ·
                refine ⟨146116359328363673091337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 779287249751272923153797 146116359328363673091337)
                ·
                  refine ⟨109587269496272754818503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146116359328363673091337 109587269496272754818503)
                  ·
                    rfl

theorem cell20_240098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_240098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240098 prefixEnd_240098 := by exact prefixLift 240098
  have htrace : WordTrace (prefixWord ++ tailWord_240098) baseStart_240098 baseEnd_240098 := by
    simpa [prefixWord, tailWord_240098, baseEnd_240098] using wordTrace_append hprefix tailTrace_240098
  have hstable : (prefixWord ++ tailWord_240098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240098).length < 2 ^ (prefixWord ++ tailWord_240098).sum := by decide
  have hdescent : baseEnd_240098 < baseStart_240098 := by decide
  rcases family_descends (prefixWord ++ tailWord_240098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240109 : List Nat := [1, 5, 1, 3, 1, 3, 1, 5]
def baseStart_240109 : Nat := 118140960795 + 240109 * 2 ^ 59
def prefixEnd_240109 : Nat := 4983230072969 + 3 ^ 40 * 240109 * 2
def baseEnd_240109 : Nat := 36530763398668535150597

theorem tailTrace_240109 : CollatzResearch.WordTrace tailWord_240109 prefixEnd_240109 36530763398668535150597 := by
  unfold tailWord_240109
  simp only [CollatzResearch.WordTrace]
  refine ⟨8757494687133575197547381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5838329791422383465031587 8757494687133575197547381)
  ·
    refine ⟨821015126918772674770067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8757494687133575197547381 821015126918772674770067)
    ·
      refine ⟨1231522690378159012155101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 821015126918772674770067 1231522690378159012155101)
      ·
        refine ⟨461821008891809629558163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1231522690378159012155101 461821008891809629558163)
        ·
          refine ⟨692731513337714444337245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461821008891809629558163 692731513337714444337245)
          ·
            refine ⟨259774317501642916626467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 692731513337714444337245 259774317501642916626467)
            ·
              refine ⟨389661476252464374939701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259774317501642916626467 389661476252464374939701)
              ·
                refine ⟨36530763398668535150597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 389661476252464374939701 36530763398668535150597)
                ·
                  rfl

theorem cell20_240109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 5].length) (baseStart_240109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240109 prefixEnd_240109 := by exact prefixLift 240109
  have htrace : WordTrace (prefixWord ++ tailWord_240109) baseStart_240109 baseEnd_240109 := by
    simpa [prefixWord, tailWord_240109, baseEnd_240109] using wordTrace_append hprefix tailTrace_240109
  have hstable : (prefixWord ++ tailWord_240109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240109).length < 2 ^ (prefixWord ++ tailWord_240109).sum := by decide
  have hdescent : baseEnd_240109 < baseStart_240109 := by decide
  rcases family_descends (prefixWord ++ tailWord_240109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240140 : List Nat := [2, 2, 1, 2, 4, 2, 2, 3, 2]
def baseStart_240140 : Nat := 118140960795 + 240140 * 2 ^ 59
def prefixEnd_240140 : Nat := 4983230072969 + 3 ^ 40 * 240140 * 2
def baseEnd_240140 : Nat := 109606439440707275418331

theorem tailTrace_240140 : CollatzResearch.WordTrace tailWord_240140 prefixEnd_240140 109606439440707275418331 := by
  unfold tailWord_240140
  simp only [CollatzResearch.WordTrace]
  refine ⟨4379312675010633745962937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5839083566680844994617249 4379312675010633745962937)
  ·
    refine ⟨3284484506257975309472203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4379312675010633745962937 3284484506257975309472203)
    ·
      refine ⟨4926726759386962964208305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3284484506257975309472203 4926726759386962964208305)
      ·
        refine ⟨3695045069540222223156229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4926726759386962964208305 3695045069540222223156229)
        ·
          refine ⟨692820950538791666841793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3695045069540222223156229 692820950538791666841793)
          ·
            refine ⟨519615712904093750131345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 692820950538791666841793 519615712904093750131345)
            ·
              refine ⟨389711784678070312598509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 519615712904093750131345 389711784678070312598509)
              ·
                refine ⟨146141919254276367224441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 389711784678070312598509 146141919254276367224441)
                ·
                  refine ⟨109606439440707275418331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146141919254276367224441 109606439440707275418331)
                  ·
                    rfl

theorem cell20_240140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 3, 2].length) (baseStart_240140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240140 prefixEnd_240140 := by exact prefixLift 240140
  have htrace : WordTrace (prefixWord ++ tailWord_240140) baseStart_240140 baseEnd_240140 := by
    simpa [prefixWord, tailWord_240140, baseEnd_240140] using wordTrace_append hprefix tailTrace_240140
  have hstable : (prefixWord ++ tailWord_240140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240140).length < 2 ^ (prefixWord ++ tailWord_240140).sum := by decide
  have hdescent : baseEnd_240140 < baseStart_240140 := by decide
  rcases family_descends (prefixWord ++ tailWord_240140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240161 : List Nat := [1, 2, 3, 2, 2, 1, 1, 6, 2]
def baseStart_240161 : Nat := 118140960795 + 240161 * 2 ^ 59
def prefixEnd_240161 : Nat := 4983230072969 + 3 ^ 40 * 240161 * 2
def baseEnd_240161 : Nat := 109616024412924535718245

theorem tailTrace_240161 : CollatzResearch.WordTrace tailWord_240161 prefixEnd_240161 109616024412924535718245 := by
  unfold tailWord_240161
  simp only [CollatzResearch.WordTrace]
  refine ⟨8759391282945188078440337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5839594188630125385626891 8759391282945188078440337)
  ·
    refine ⟨6569543462208891058830253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8759391282945188078440337 6569543462208891058830253)
    ·
      refine ⟨2463578798328334147061345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6569543462208891058830253 2463578798328334147061345)
      ·
        refine ⟨1847684098746250610296009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2463578798328334147061345 1847684098746250610296009)
        ·
          refine ⟨1385763074059687957722007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1847684098746250610296009 1385763074059687957722007)
          ·
            refine ⟨2078644611089531936583011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1385763074059687957722007 2078644611089531936583011)
            ·
              refine ⟨3117966916634297904874517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2078644611089531936583011 3117966916634297904874517)
              ·
                refine ⟨146154699217232714290993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3117966916634297904874517 146154699217232714290993)
                ·
                  refine ⟨109616024412924535718245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146154699217232714290993 109616024412924535718245)
                  ·
                    rfl

theorem cell20_240161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 6, 2].length) (baseStart_240161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240161 prefixEnd_240161 := by exact prefixLift 240161
  have htrace : WordTrace (prefixWord ++ tailWord_240161) baseStart_240161 baseEnd_240161 := by
    simpa [prefixWord, tailWord_240161, baseEnd_240161] using wordTrace_append hprefix tailTrace_240161
  have hstable : (prefixWord ++ tailWord_240161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240161).length < 2 ^ (prefixWord ++ tailWord_240161).sum := by decide
  have hdescent : baseEnd_240161 < baseStart_240161 := by decide
  rcases family_descends (prefixWord ++ tailWord_240161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240203 : List Nat := [1, 1, 1, 1, 3, 1, 4, 2, 6]
def baseStart_240203 : Nat := 118140960795 + 240203 * 2 ^ 59
def prefixEnd_240203 : Nat := 4983230072969 + 3 ^ 40 * 240203 * 2
def baseEnd_240203 : Nat := 109635194357359056318073

theorem tailTrace_240203 : CollatzResearch.WordTrace tailWord_240203 prefixEnd_240203 109635194357359056318073 := by
  unfold tailWord_240203
  simp only [CollatzResearch.WordTrace]
  refine ⟨8760923148793029251469263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5840615432528686167646175 8760923148793029251469263)
  ·
    refine ⟨13141384723189543877203895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8760923148793029251469263 13141384723189543877203895)
    ·
      refine ⟨19712077084784315815805843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13141384723189543877203895 19712077084784315815805843)
      ·
        refine ⟨29568115627176473723708765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19712077084784315815805843 29568115627176473723708765)
        ·
          refine ⟨11088043360191177646390787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29568115627176473723708765 11088043360191177646390787)
          ·
            refine ⟨16632065040286766469586181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11088043360191177646390787 16632065040286766469586181)
            ·
              refine ⟨3118512195053768713047409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16632065040286766469586181 3118512195053768713047409)
              ·
                refine ⟨2338884146290326534785557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3118512195053768713047409 2338884146290326534785557)
                ·
                  refine ⟨109635194357359056318073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2338884146290326534785557 109635194357359056318073)
                  ·
                    rfl

theorem cell20_240203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 6].length) (baseStart_240203 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240203 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240203 prefixEnd_240203 := by exact prefixLift 240203
  have htrace : WordTrace (prefixWord ++ tailWord_240203) baseStart_240203 baseEnd_240203 := by
    simpa [prefixWord, tailWord_240203, baseEnd_240203] using wordTrace_append hprefix tailTrace_240203
  have hstable : (prefixWord ++ tailWord_240203).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240203).length < 2 ^ (prefixWord ++ tailWord_240203).sum := by decide
  have hdescent : baseEnd_240203 < baseStart_240203 := by decide
  rcases family_descends (prefixWord ++ tailWord_240203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240222 : List Nat := [4, 4, 1, 2, 1, 2, 2, 1, 3]
def baseStart_240222 : Nat := 118140960795 + 240222 * 2 ^ 59
def prefixEnd_240222 : Nat := 4983230072969 + 3 ^ 40 * 240222 * 2
def baseEnd_240222 : Nat := 109643866475079434684663

theorem tailTrace_240222 : CollatzResearch.WordTrace tailWord_240222 prefixEnd_240222 109643866475079434684663 := by
  unfold tailWord_240222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1095202016965524437051365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5841077423816130330940613 1095202016965524437051365)
  ·
    refine ⟨205350378181035831947131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1095202016965524437051365 205350378181035831947131)
    ·
      refine ⟨308025567271553747920697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205350378181035831947131 308025567271553747920697)
      ·
        refine ⟨231019175453665310940523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308025567271553747920697 231019175453665310940523)
        ·
          refine ⟨346528763180497966410785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231019175453665310940523 346528763180497966410785)
          ·
            refine ⟨259896572385373474808089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346528763180497966410785 259896572385373474808089)
            ·
              refine ⟨194922429289030106106067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259896572385373474808089 194922429289030106106067)
              ·
                refine ⟨292383643933545159159101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194922429289030106106067 292383643933545159159101)
                ·
                  refine ⟨109643866475079434684663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 292383643933545159159101 109643866475079434684663)
                  ·
                    rfl

theorem cell20_240222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_240222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240222 prefixEnd_240222 := by exact prefixLift 240222
  have htrace : WordTrace (prefixWord ++ tailWord_240222) baseStart_240222 baseEnd_240222 := by
    simpa [prefixWord, tailWord_240222, baseEnd_240222] using wordTrace_append hprefix tailTrace_240222
  have hstable : (prefixWord ++ tailWord_240222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240222).length < 2 ^ (prefixWord ++ tailWord_240222).sum := by decide
  have hdescent : baseEnd_240222 < baseStart_240222 := by decide
  rcases family_descends (prefixWord ++ tailWord_240222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240227 : List Nat := [1, 1, 1, 5, 1, 2, 4, 5]
def baseStart_240227 : Nat := 118140960795 + 240227 * 2 ^ 59
def prefixEnd_240227 : Nat := 4983230072969 + 3 ^ 40 * 240227 * 2
def baseEnd_240227 : Nat := 36548716203773879839325

theorem tailTrace_240227 : CollatzResearch.WordTrace tailWord_240227 prefixEnd_240227 36548716203773879839325 := by
  unfold tailWord_240227
  simp only [CollatzResearch.WordTrace]
  refine ⟨8761798500706081350342935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5841199000470720900228623 8761798500706081350342935)
  ·
    refine ⟨13142697751059122025514403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8761798500706081350342935 13142697751059122025514403)
    ·
      refine ⟨19714046626588683038271605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13142697751059122025514403 19714046626588683038271605)
      ·
        refine ⟨1848191871242689034837963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19714046626588683038271605 1848191871242689034837963)
        ·
          refine ⟨2772287806864033552256945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1848191871242689034837963 2772287806864033552256945)
          ·
            refine ⟨2079215855148025164192709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2772287806864033552256945 2079215855148025164192709)
            ·
              refine ⟨389852972840254718286133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2079215855148025164192709 389852972840254718286133)
              ·
                refine ⟨36548716203773879839325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 389852972840254718286133 36548716203773879839325)
                ·
                  rfl

theorem cell20_240227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 5].length) (baseStart_240227 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240227 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240227 prefixEnd_240227 := by exact prefixLift 240227
  have htrace : WordTrace (prefixWord ++ tailWord_240227) baseStart_240227 baseEnd_240227 := by
    simpa [prefixWord, tailWord_240227, baseEnd_240227] using wordTrace_append hprefix tailTrace_240227
  have hstable : (prefixWord ++ tailWord_240227).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240227).length < 2 ^ (prefixWord ++ tailWord_240227).sum := by decide
  have hdescent : baseEnd_240227 < baseStart_240227 := by decide
  rcases family_descends (prefixWord ++ tailWord_240227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240334 : List Nat := [4, 1, 1, 1, 3, 2, 1, 3, 4]
def baseStart_240334 : Nat := 118140960795 + 240334 * 2 ^ 59
def prefixEnd_240334 : Nat := 4983230072969 + 3 ^ 40 * 240334 * 2
def baseEnd_240334 : Nat := 109694986326904822950871

theorem tailTrace_240334 : CollatzResearch.WordTrace tailWord_240334 prefixEnd_240334 109694986326904822950871 := by
  unfold tailWord_240334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1095712638914804828061007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5843800740878959082992037 1095712638914804828061007)
  ·
    refine ⟨1643568958372207242091511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1095712638914804828061007 1643568958372207242091511)
    ·
      refine ⟨2465353437558310863137267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1643568958372207242091511 2465353437558310863137267)
      ·
        refine ⟨3698030156337466294705901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2465353437558310863137267 3698030156337466294705901)
        ·
          refine ⟨1386761308626549860514713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3698030156337466294705901 1386761308626549860514713)
          ·
            refine ⟨1040070981469912395386035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1386761308626549860514713 1040070981469912395386035)
            ·
              refine ⟨1560106472204868593079053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1040070981469912395386035 1560106472204868593079053)
              ·
                refine ⟨585039927076825722404645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1560106472204868593079053 585039927076825722404645)
                ·
                  refine ⟨109694986326904822950871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 585039927076825722404645 109694986326904822950871)
                  ·
                    rfl

theorem cell20_240334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_240334 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240334 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240334 prefixEnd_240334 := by exact prefixLift 240334
  have htrace : WordTrace (prefixWord ++ tailWord_240334) baseStart_240334 baseEnd_240334 := by
    simpa [prefixWord, tailWord_240334, baseEnd_240334] using wordTrace_append hprefix tailTrace_240334
  have hstable : (prefixWord ++ tailWord_240334).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240334).length < 2 ^ (prefixWord ++ tailWord_240334).sum := by decide
  have hdescent : baseEnd_240334 < baseStart_240334 := by decide
  rcases family_descends (prefixWord ++ tailWord_240334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240344 : List Nat := [2, 1, 2, 2, 3, 3, 3, 1, 3]
def baseStart_240344 : Nat := 118140960795 + 240344 * 2 ^ 59
def prefixEnd_240344 : Nat := 4983230072969 + 3 ^ 40 * 240344 * 2
def baseEnd_240344 : Nat := 109699550599389232617497

theorem tailTrace_240344 : CollatzResearch.WordTrace tailWord_240344 prefixEnd_240344 109699550599389232617497 := by
  unfold tailWord_240344
  simp only [CollatzResearch.WordTrace]
  refine ⟨4383032920641105166176043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5844043894188140221568057 4383032920641105166176043)
  ·
    refine ⟨6574549380961657749264065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4383032920641105166176043 6574549380961657749264065)
    ·
      refine ⟨4930912035721243311948049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6574549380961657749264065 4930912035721243311948049)
      ·
        refine ⟨3698184026790932483961037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4930912035721243311948049 3698184026790932483961037)
        ·
          refine ⟨1386819010046599681485389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3698184026790932483961037 1386819010046599681485389)
          ·
            refine ⟨520057128767474880557021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1386819010046599681485389 520057128767474880557021)
            ·
              refine ⟨195021423287803080208883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 520057128767474880557021 195021423287803080208883)
              ·
                refine ⟨292532134931704620313325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195021423287803080208883 292532134931704620313325)
                ·
                  refine ⟨109699550599389232617497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 292532134931704620313325 109699550599389232617497)
                  ·
                    rfl

theorem cell20_240344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 1, 3].length) (baseStart_240344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240344 prefixEnd_240344 := by exact prefixLift 240344
  have htrace : WordTrace (prefixWord ++ tailWord_240344) baseStart_240344 baseEnd_240344 := by
    simpa [prefixWord, tailWord_240344, baseEnd_240344] using wordTrace_append hprefix tailTrace_240344
  have hstable : (prefixWord ++ tailWord_240344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240344).length < 2 ^ (prefixWord ++ tailWord_240344).sum := by decide
  have hdescent : baseEnd_240344 < baseStart_240344 := by decide
  rcases family_descends (prefixWord ++ tailWord_240344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240507 : List Nat := [1, 1, 1, 1, 1, 5, 3, 3, 4]
def baseStart_240507 : Nat := 118140960795 + 240507 * 2 ^ 59
def prefixEnd_240507 : Nat := 4983230072969 + 3 ^ 40 * 240507 * 2
def baseEnd_240507 : Nat := 109773948240885110183497

theorem tailTrace_240507 : CollatzResearch.WordTrace tailWord_240507 prefixEnd_240507 109773948240885110183497 := by
  unfold tailWord_240507
  simp only [CollatzResearch.WordTrace]
  refine ⟨8772010939691689170535775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5848007293127792780357183 8772010939691689170535775)
  ·
    refine ⟨13158016409537533755803663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8772010939691689170535775 13158016409537533755803663)
    ·
      refine ⟨19737024614306300633705495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13158016409537533755803663 19737024614306300633705495)
      ·
        refine ⟨29605536921459450950558243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19737024614306300633705495 29605536921459450950558243)
        ·
          refine ⟨44408305382189176425837365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29605536921459450950558243 44408305382189176425837365)
          ·
            refine ⟨4163278629580235289922253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44408305382189176425837365 4163278629580235289922253)
            ·
              refine ⟨1561229486092588233720845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4163278629580235289922253 1561229486092588233720845)
              ·
                refine ⟨585461057284720587645317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1561229486092588233720845 585461057284720587645317)
                ·
                  refine ⟨109773948240885110183497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 585461057284720587645317 109773948240885110183497)
                  ·
                    rfl

theorem cell20_240507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 4].length) (baseStart_240507 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240507 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240507 prefixEnd_240507 := by exact prefixLift 240507
  have htrace : WordTrace (prefixWord ++ tailWord_240507) baseStart_240507 baseEnd_240507 := by
    simpa [prefixWord, tailWord_240507, baseEnd_240507] using wordTrace_append hprefix tailTrace_240507
  have hstable : (prefixWord ++ tailWord_240507).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240507).length < 2 ^ (prefixWord ++ tailWord_240507).sum := by decide
  have hdescent : baseEnd_240507 < baseStart_240507 := by decide
  rcases family_descends (prefixWord ++ tailWord_240507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240569 : List Nat := [1, 2, 1, 4, 2, 3, 2, 5]
def baseStart_240569 : Nat := 118140960795 + 240569 * 2 ^ 59
def prefixEnd_240569 : Nat := 4983230072969 + 3 ^ 40 * 240569 * 2
def baseEnd_240569 : Nat := 36600748910096150038859

theorem tailTrace_240569 : CollatzResearch.WordTrace tailWord_240569 prefixEnd_240569 36600748910096150038859 := by
  unfold tailWord_240569
  simp only [CollatzResearch.WordTrace]
  refine ⟨8774272265467073759292761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5849514843644715839528507 8774272265467073759292761)
  ·
    refine ⟨6580704199100305319469571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8774272265467073759292761 6580704199100305319469571)
    ·
      refine ⟨9871056298650457979204357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6580704199100305319469571 9871056298650457979204357)
      ·
        refine ⟨1850823055996960871100817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9871056298650457979204357 1850823055996960871100817)
        ·
          refine ⟨1388117291997720653325613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1850823055996960871100817 1388117291997720653325613)
          ·
            refine ⟨520543984499145244997105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1388117291997720653325613 520543984499145244997105)
            ·
              refine ⟨390407988374358933747829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 520543984499145244997105 390407988374358933747829)
              ·
                refine ⟨36600748910096150038859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 390407988374358933747829 36600748910096150038859)
                ·
                  rfl

theorem cell20_240569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 5].length) (baseStart_240569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240569 prefixEnd_240569 := by exact prefixLift 240569
  have htrace : WordTrace (prefixWord ++ tailWord_240569) baseStart_240569 baseEnd_240569 := by
    simpa [prefixWord, tailWord_240569, baseEnd_240569] using wordTrace_append hprefix tailTrace_240569
  have hstable : (prefixWord ++ tailWord_240569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240569).length < 2 ^ (prefixWord ++ tailWord_240569).sum := by decide
  have hdescent : baseEnd_240569 < baseStart_240569 := by decide
  rcases family_descends (prefixWord ++ tailWord_240569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240583 : List Nat := [1, 1, 4, 1, 1, 2, 2, 4, 4]
def baseStart_240583 : Nat := 118140960795 + 240583 * 2 ^ 59
def prefixEnd_240583 : Nat := 4983230072969 + 3 ^ 40 * 240583 * 2
def baseEnd_240583 : Nat := 109808636711766623649853

theorem tailTrace_240583 : CollatzResearch.WordTrace tailWord_240583 prefixEnd_240583 109808636711766623649853 := by
  unfold tailWord_240583
  simp only [CollatzResearch.WordTrace]
  refine ⟨8774782887416354150302403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5849855258277569433534935 8774782887416354150302403)
  ·
    refine ⟨13162174331124531225453605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8774782887416354150302403 13162174331124531225453605)
    ·
      refine ⟨2467907687085849604772551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13162174331124531225453605 2467907687085849604772551)
      ·
        refine ⟨3701861530628774407158827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2467907687085849604772551 3701861530628774407158827)
        ·
          refine ⟨5552792295943161610738241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3701861530628774407158827 5552792295943161610738241)
          ·
            refine ⟨4164594221957371208053681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5552792295943161610738241 4164594221957371208053681)
            ·
              refine ⟨3123445666468028406040261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4164594221957371208053681 3123445666468028406040261)
              ·
                refine ⟨585646062462755326132549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3123445666468028406040261 585646062462755326132549)
                ·
                  refine ⟨109808636711766623649853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 585646062462755326132549 109808636711766623649853)
                  ·
                    rfl

theorem cell20_240583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 4].length) (baseStart_240583 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240583 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240583 prefixEnd_240583 := by exact prefixLift 240583
  have htrace : WordTrace (prefixWord ++ tailWord_240583) baseStart_240583 baseEnd_240583 := by
    simpa [prefixWord, tailWord_240583, baseEnd_240583] using wordTrace_append hprefix tailTrace_240583
  have hstable : (prefixWord ++ tailWord_240583).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240583).length < 2 ^ (prefixWord ++ tailWord_240583).sum := by decide
  have hdescent : baseEnd_240583 < baseStart_240583 := by decide
  rcases family_descends (prefixWord ++ tailWord_240583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240607 : List Nat := [1, 1, 2, 3, 6, 7]
def baseStart_240607 : Nat := 118140960795 + 240607 * 2 ^ 59
def prefixEnd_240607 : Nat := 4983230072969 + 3 ^ 40 * 240607 * 2
def baseEnd_240607 : Nat := 4067392257989970624065

theorem tailTrace_240607 : CollatzResearch.WordTrace tailWord_240607 prefixEnd_240607 4067392257989970624065 := by
  unfold tailWord_240607
  simp only [CollatzResearch.WordTrace]
  refine ⟨8775658239329406249176075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5850438826219604166117383 8775658239329406249176075)
  ·
    refine ⟨13163487358994109373764113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8775658239329406249176075 13163487358994109373764113)
    ·
      refine ⟨9872615519245582030323085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13163487358994109373764113 9872615519245582030323085)
      ·
        refine ⟨3702230819717093261371157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9872615519245582030323085 3702230819717093261371157)
        ·
          refine ⟨173542069674238746626773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3702230819717093261371157 173542069674238746626773)
          ·
            refine ⟨4067392257989970624065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 173542069674238746626773 4067392257989970624065)
            ·
              rfl

theorem cell20_240607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 7].length) (baseStart_240607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240607 prefixEnd_240607 := by exact prefixLift 240607
  have htrace : WordTrace (prefixWord ++ tailWord_240607) baseStart_240607 baseEnd_240607 := by
    simpa [prefixWord, tailWord_240607, baseEnd_240607] using wordTrace_append hprefix tailTrace_240607
  have hstable : (prefixWord ++ tailWord_240607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240607).length < 2 ^ (prefixWord ++ tailWord_240607).sum := by decide
  have hdescent : baseEnd_240607 < baseStart_240607 := by decide
  rcases family_descends (prefixWord ++ tailWord_240607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240610 : List Nat := [3, 3, 3, 1, 1, 1, 1, 4, 3]
def baseStart_240610 : Nat := 118140960795 + 240610 * 2 ^ 59
def prefixEnd_240610 : Nat := 4983230072969 + 3 ^ 40 * 240610 * 2
def baseEnd_240610 : Nat := 109820960247474529749743

theorem tailTrace_240610 : CollatzResearch.WordTrace tailWord_240610 prefixEnd_240610 109820960247474529749743 := by
  unfold tailWord_240610
  simp only [CollatzResearch.WordTrace]
  refine ⟨2193941914579634440383821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5850511772212358507690189 2193941914579634440383821)
  ·
    refine ⟨822728217967362915143933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2193941914579634440383821 822728217967362915143933)
    ·
      refine ⟨308523081737761093178975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 822728217967362915143933 308523081737761093178975)
      ·
        refine ⟨462784622606641639768463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308523081737761093178975 462784622606641639768463)
        ·
          refine ⟨694176933909962459652695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462784622606641639768463 694176933909962459652695)
          ·
            refine ⟨1041265400864943689479043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 694176933909962459652695 1041265400864943689479043)
            ·
              refine ⟨1561898101297415534218565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1041265400864943689479043 1561898101297415534218565)
              ·
                refine ⟨292855893993265412665981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1561898101297415534218565 292855893993265412665981)
                ·
                  refine ⟨109820960247474529749743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 292855893993265412665981 109820960247474529749743)
                  ·
                    rfl

theorem cell20_240610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_240610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240610 prefixEnd_240610 := by exact prefixLift 240610
  have htrace : WordTrace (prefixWord ++ tailWord_240610) baseStart_240610 baseEnd_240610 := by
    simpa [prefixWord, tailWord_240610, baseEnd_240610] using wordTrace_append hprefix tailTrace_240610
  have hstable : (prefixWord ++ tailWord_240610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240610).length < 2 ^ (prefixWord ++ tailWord_240610).sum := by decide
  have hdescent : baseEnd_240610 < baseStart_240610 := by decide
  rcases family_descends (prefixWord ++ tailWord_240610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240635 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 7]
def baseStart_240635 : Nat := 118140960795 + 240635 * 2 ^ 59
def prefixEnd_240635 : Nat := 4983230072969 + 3 ^ 40 * 240635 * 2
def baseEnd_240635 : Nat := 109832370928685553916307

theorem tailTrace_240635 : CollatzResearch.WordTrace tailWord_240635 prefixEnd_240635 109832370928685553916307 := by
  unfold tailWord_240635
  simp only [CollatzResearch.WordTrace]
  refine ⟨8776679483227967031195359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5851119655485311354130239 8776679483227967031195359)
  ·
    refine ⟨13165019224841950546793039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8776679483227967031195359 13165019224841950546793039)
    ·
      refine ⟨19747528837262925820189559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13165019224841950546793039 19747528837262925820189559)
      ·
        refine ⟨29621293255894388730284339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19747528837262925820189559 29621293255894388730284339)
        ·
          refine ⟨44431939883841583095426509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29621293255894388730284339 44431939883841583095426509)
          ·
            refine ⟨16661977456440593660784941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44431939883841583095426509 16661977456440593660784941)
            ·
              refine ⟨6248241546165222622794353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16661977456440593660784941 6248241546165222622794353)
              ·
                refine ⟨4686181159623916967095765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6248241546165222622794353 4686181159623916967095765)
                ·
                  refine ⟨109832370928685553916307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4686181159623916967095765 109832370928685553916307)
                  ·
                    rfl

theorem cell20_240635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 7].length) (baseStart_240635 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240635 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240635 prefixEnd_240635 := by exact prefixLift 240635
  have htrace : WordTrace (prefixWord ++ tailWord_240635) baseStart_240635 baseEnd_240635 := by
    simpa [prefixWord, tailWord_240635, baseEnd_240635] using wordTrace_append hprefix tailTrace_240635
  have hstable : (prefixWord ++ tailWord_240635).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240635).length < 2 ^ (prefixWord ++ tailWord_240635).sum := by decide
  have hdescent : baseEnd_240635 < baseStart_240635 := by decide
  rcases family_descends (prefixWord ++ tailWord_240635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240645 : List Nat := [1, 3, 1, 1, 2, 3, 5, 4]
def baseStart_240645 : Nat := 118140960795 + 240645 * 2 ^ 59
def prefixEnd_240645 : Nat := 4983230072969 + 3 ^ 40 * 240645 * 2
def baseEnd_240645 : Nat := 36612311733723321194311

theorem tailTrace_240645 : CollatzResearch.WordTrace tailWord_240645 prefixEnd_240645 36612311733723321194311 := by
  unfold tailWord_240645
  simp only [CollatzResearch.WordTrace]
  refine ⟨8777044213191738739059389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5851362808794492492706259 8777044213191738739059389)
  ·
    refine ⟨3291391579946902027147271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8777044213191738739059389 3291391579946902027147271)
    ·
      refine ⟨4937087369920353040720907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3291391579946902027147271 4937087369920353040720907)
      ·
        refine ⟨7405631054880529561081361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4937087369920353040720907 7405631054880529561081361)
        ·
          refine ⟨5554223291160397170811021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7405631054880529561081361 5554223291160397170811021)
          ·
            refine ⟨2082833734185148939054133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5554223291160397170811021 2082833734185148939054133)
            ·
              refine ⟨195265662579857713036325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2082833734185148939054133 195265662579857713036325)
              ·
                refine ⟨36612311733723321194311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195265662579857713036325 36612311733723321194311)
                ·
                  rfl

theorem cell20_240645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 4].length) (baseStart_240645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240645 prefixEnd_240645 := by exact prefixLift 240645
  have htrace : WordTrace (prefixWord ++ tailWord_240645) baseStart_240645 baseEnd_240645 := by
    simpa [prefixWord, tailWord_240645, baseEnd_240645] using wordTrace_append hprefix tailTrace_240645
  have hstable : (prefixWord ++ tailWord_240645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240645).length < 2 ^ (prefixWord ++ tailWord_240645).sum := by decide
  have hdescent : baseEnd_240645 < baseStart_240645 := by decide
  rcases family_descends (prefixWord ++ tailWord_240645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240666 : List Nat := [3, 1, 1, 3, 1, 2, 9]
def baseStart_240666 : Nat := 118140960795 + 240666 * 2 ^ 59
def prefixEnd_240666 : Nat := 4983230072969 + 3 ^ 40 * 240666 * 2
def baseEnd_240666 : Nat := 12205168908154135986983

theorem tailTrace_240666 : CollatzResearch.WordTrace tailWord_240666 prefixEnd_240666 12205168908154135986983 := by
  unfold tailWord_240666
  simp only [CollatzResearch.WordTrace]
  refine ⟨2194452536528914831393463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5851873430743772883715901 2194452536528914831393463)
  ·
    refine ⟨3291678804793372247090195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2194452536528914831393463 3291678804793372247090195)
    ·
      refine ⟨4937518207190058370635293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3291678804793372247090195 4937518207190058370635293)
      ·
        refine ⟨1851569327696271888988235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4937518207190058370635293 1851569327696271888988235)
        ·
          refine ⟨2777353991544407833482353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1851569327696271888988235 2777353991544407833482353)
          ·
            refine ⟨2083015493658305875111765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2777353991544407833482353 2083015493658305875111765)
            ·
              refine ⟨12205168908154135986983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2083015493658305875111765 12205168908154135986983)
              ·
                rfl

theorem cell20_240666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 9].length) (baseStart_240666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240666 prefixEnd_240666 := by exact prefixLift 240666
  have htrace : WordTrace (prefixWord ++ tailWord_240666) baseStart_240666 baseEnd_240666 := by
    simpa [prefixWord, tailWord_240666, baseEnd_240666] using wordTrace_append hprefix tailTrace_240666
  have hstable : (prefixWord ++ tailWord_240666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240666).length < 2 ^ (prefixWord ++ tailWord_240666).sum := by decide
  have hdescent : baseEnd_240666 < baseStart_240666 := by decide
  rcases family_descends (prefixWord ++ tailWord_240666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240669 : List Nat := [1, 4, 2, 2, 3, 1, 1, 1, 5]
def baseStart_240669 : Nat := 118140960795 + 240669 * 2 ^ 59
def prefixEnd_240669 : Nat := 4983230072969 + 3 ^ 40 * 240669 * 2
def baseEnd_240669 : Nat := 109847889455132546782835

theorem tailTrace_240669 : CollatzResearch.WordTrace tailWord_240669 prefixEnd_240669 109847889455132546782835 := by
  unfold tailWord_240669
  simp only [CollatzResearch.WordTrace]
  refine ⟨8777919565104790837933061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5851946376736527225288707 8777919565104790837933061)
  ·
    refine ⟨1645859918457148282112449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8777919565104790837933061 1645859918457148282112449)
    ·
      refine ⟨1234394938842861211584337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1645859918457148282112449 1234394938842861211584337)
      ·
        refine ⟨925796204132145908688253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1234394938842861211584337 925796204132145908688253)
        ·
          refine ⟨347173576549554715758095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 925796204132145908688253 347173576549554715758095)
          ·
            refine ⟨520760364824332073637143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347173576549554715758095 520760364824332073637143)
            ·
              refine ⟨781140547236498110455715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 520760364824332073637143 781140547236498110455715)
              ·
                refine ⟨1171710820854747165683573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 781140547236498110455715 1171710820854747165683573)
                ·
                  refine ⟨109847889455132546782835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1171710820854747165683573 109847889455132546782835)
                  ·
                    rfl

theorem cell20_240669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_240669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240669 prefixEnd_240669 := by exact prefixLift 240669
  have htrace : WordTrace (prefixWord ++ tailWord_240669) baseStart_240669 baseEnd_240669 := by
    simpa [prefixWord, tailWord_240669, baseEnd_240669] using wordTrace_append hprefix tailTrace_240669
  have hstable : (prefixWord ++ tailWord_240669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240669).length < 2 ^ (prefixWord ++ tailWord_240669).sum := by decide
  have hdescent : baseEnd_240669 < baseStart_240669 := by decide
  rcases family_descends (prefixWord ++ tailWord_240669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240676 : List Nat := [2, 3, 1, 4, 1, 1, 1, 3, 4]
def baseStart_240676 : Nat := 118140960795 + 240676 * 2 ^ 59
def prefixEnd_240676 : Nat := 4983230072969 + 3 ^ 40 * 240676 * 2
def baseEnd_240676 : Nat := 109851084445871633549473

theorem tailTrace_240676 : CollatzResearch.WordTrace tailWord_240676 prefixEnd_240676 109851084445871633549473 := by
  unfold tailWord_240676
  simp only [CollatzResearch.WordTrace]
  refine ⟨4389087438039715516718941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5852116584052954022291921 4389087438039715516718941)
  ·
    refine ⟨1645907789264893318769603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4389087438039715516718941 1645907789264893318769603)
    ·
      refine ⟨2468861683897339978154405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1645907789264893318769603 2468861683897339978154405)
      ·
        refine ⟨462911565730751245903951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2468861683897339978154405 462911565730751245903951)
        ·
          refine ⟨694367348596126868855927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462911565730751245903951 694367348596126868855927)
          ·
            refine ⟨1041551022894190303283891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 694367348596126868855927 1041551022894190303283891)
            ·
              refine ⟨1562326534341285454925837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1041551022894190303283891 1562326534341285454925837)
              ·
                refine ⟨585872450377982045597189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1562326534341285454925837 585872450377982045597189)
                ·
                  refine ⟨109851084445871633549473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 585872450377982045597189 109851084445871633549473)
                  ·
                    rfl

theorem cell20_240676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_240676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240676 prefixEnd_240676 := by exact prefixLift 240676
  have htrace : WordTrace (prefixWord ++ tailWord_240676) baseStart_240676 baseEnd_240676 := by
    simpa [prefixWord, tailWord_240676, baseEnd_240676] using wordTrace_append hprefix tailTrace_240676
  have hstable : (prefixWord ++ tailWord_240676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240676).length < 2 ^ (prefixWord ++ tailWord_240676).sum := by decide
  have hdescent : baseEnd_240676 < baseStart_240676 := by decide
  rcases family_descends (prefixWord ++ tailWord_240676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240686 : List Nat := [4, 1, 3, 1, 1, 1, 5, 1, 3]
def baseStart_240686 : Nat := 118140960795 + 240686 * 2 ^ 59
def prefixEnd_240686 : Nat := 4983230072969 + 3 ^ 40 * 240686 * 2
def baseEnd_240686 : Nat := 109855648718356043216099

theorem tailTrace_240686 : CollatzResearch.WordTrace tailWord_240686 prefixEnd_240686 109855648718356043216099 := by
  unfold tailWord_240686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1097317450755400342662739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5852359737362135160867941 1097317450755400342662739)
  ·
    refine ⟨1645976176133100513994109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1097317450755400342662739 1645976176133100513994109)
    ·
      refine ⟨617241066049912692747791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1645976176133100513994109 617241066049912692747791)
      ·
        refine ⟨925861599074869039121687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617241066049912692747791 925861599074869039121687)
        ·
          refine ⟨1388792398612303558682531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 925861599074869039121687 1388792398612303558682531)
          ·
            refine ⟨2083188597918455338023797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1388792398612303558682531 2083188597918455338023797)
            ·
              refine ⟨195298931054855187939731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2083188597918455338023797 195298931054855187939731)
              ·
                refine ⟨292948396582282781909597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195298931054855187939731 292948396582282781909597)
                ·
                  refine ⟨109855648718356043216099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 292948396582282781909597 109855648718356043216099)
                  ·
                    rfl

theorem cell20_240686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_240686 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240686 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240686 prefixEnd_240686 := by exact prefixLift 240686
  have htrace : WordTrace (prefixWord ++ tailWord_240686) baseStart_240686 baseEnd_240686 := by
    simpa [prefixWord, tailWord_240686, baseEnd_240686] using wordTrace_append hprefix tailTrace_240686
  have hstable : (prefixWord ++ tailWord_240686).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240686).length < 2 ^ (prefixWord ++ tailWord_240686).sum := by decide
  have hdescent : baseEnd_240686 < baseStart_240686 := by decide
  rcases family_descends (prefixWord ++ tailWord_240686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240700 : List Nat := [2, 2, 2, 2, 2, 4, 2, 4]
def baseStart_240700 : Nat := 118140960795 + 240700 * 2 ^ 59
def prefixEnd_240700 : Nat := 4983230072969 + 3 ^ 40 * 240700 * 2
def baseEnd_240700 : Nat := 36620679566611405583125

theorem tailTrace_240700 : CollatzResearch.WordTrace tailWord_240700 prefixEnd_240700 36620679566611405583125 := by
  unfold tailWord_240700
  simp only [CollatzResearch.WordTrace]
  refine ⟨4389525113996241566155777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5852700151994988754874369 4389525113996241566155777)
  ·
    refine ⟨3292143835497181174616833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4389525113996241566155777 3292143835497181174616833)
    ·
      refine ⟨2469107876622885880962625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3292143835497181174616833 2469107876622885880962625)
      ·
        refine ⟨1851830907467164410721969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2469107876622885880962625 1851830907467164410721969)
        ·
          refine ⟨1388873180600373308041477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1851830907467164410721969 1388873180600373308041477)
          ·
            refine ⟨260413721362569995257777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1388873180600373308041477 260413721362569995257777)
            ·
              refine ⟨195310291021927496443333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260413721362569995257777 195310291021927496443333)
              ·
                refine ⟨36620679566611405583125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195310291021927496443333 36620679566611405583125)
                ·
                  rfl

theorem cell20_240700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 4].length) (baseStart_240700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240700 prefixEnd_240700 := by exact prefixLift 240700
  have htrace : WordTrace (prefixWord ++ tailWord_240700) baseStart_240700 baseEnd_240700 := by
    simpa [prefixWord, tailWord_240700, baseEnd_240700] using wordTrace_append hprefix tailTrace_240700
  have hstable : (prefixWord ++ tailWord_240700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240700).length < 2 ^ (prefixWord ++ tailWord_240700).sum := by decide
  have hdescent : baseEnd_240700 < baseStart_240700 := by decide
  rcases family_descends (prefixWord ++ tailWord_240700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240704 : List Nat := [2, 1, 1, 2, 2, 3, 3, 6]
def baseStart_240704 : Nat := 118140960795 + 240704 * 2 ^ 59
def prefixEnd_240704 : Nat := 4983230072969 + 3 ^ 40 * 240704 * 2
def baseEnd_240704 : Nat := 36621288136275993538675

theorem tailTrace_240704 : CollatzResearch.WordTrace tailWord_240704 prefixEnd_240704 36621288136275993538675 := by
  unfold tailWord_240704
  simp only [CollatzResearch.WordTrace]
  refine ⟨4389598059988995907728583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5852797413318661210304777 4389598059988995907728583)
  ·
    refine ⟨6584397089983493861592875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4389598059988995907728583 6584397089983493861592875)
    ·
      refine ⟨9876595634975240792389313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6584397089983493861592875 9876595634975240792389313)
      ·
        refine ⟨7407446726231430594291985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9876595634975240792389313 7407446726231430594291985)
        ·
          refine ⟨5555585044673572945718989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7407446726231430594291985 5555585044673572945718989)
          ·
            refine ⟨2083344391752589854644621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5555585044673572945718989 2083344391752589854644621)
            ·
              refine ⟨781254146907221195491733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2083344391752589854644621 781254146907221195491733)
              ·
                refine ⟨36621288136275993538675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 781254146907221195491733 36621288136275993538675)
                ·
                  rfl

theorem cell20_240704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 6].length) (baseStart_240704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240704 prefixEnd_240704 := by exact prefixLift 240704
  have htrace : WordTrace (prefixWord ++ tailWord_240704) baseStart_240704 baseEnd_240704 := by
    simpa [prefixWord, tailWord_240704, baseEnd_240704] using wordTrace_append hprefix tailTrace_240704
  have hstable : (prefixWord ++ tailWord_240704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240704).length < 2 ^ (prefixWord ++ tailWord_240704).sum := by decide
  have hdescent : baseEnd_240704 < baseStart_240704 := by decide
  rcases family_descends (prefixWord ++ tailWord_240704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240728 : List Nat := [2, 1, 2, 2, 1, 3, 2, 4, 3]
def baseStart_240728 : Nat := 118140960795 + 240728 * 2 ^ 59
def prefixEnd_240728 : Nat := 4983230072969 + 3 ^ 40 * 240728 * 2
def baseEnd_240728 : Nat := 109874818662790563815927

theorem tailTrace_240728 : CollatzResearch.WordTrace tailWord_240728 prefixEnd_240728 109874818662790563815927 := by
  unfold tailWord_240728
  simp only [CollatzResearch.WordTrace]
  refine ⟨4390035735945521957165419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5853380981260695942887225 4390035735945521957165419)
  ·
    refine ⟨6585053603918282935748129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4390035735945521957165419 6585053603918282935748129)
    ·
      refine ⟨4938790202938712201811097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6585053603918282935748129 4938790202938712201811097)
      ·
        refine ⟨3704092652204034151358323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4938790202938712201811097 3704092652204034151358323)
        ·
          refine ⟨5556138978306051227037485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3704092652204034151358323 5556138978306051227037485)
          ·
            refine ⟨2083552116864769210139057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5556138978306051227037485 2083552116864769210139057)
            ·
              refine ⟨1562664087648576907604293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2083552116864769210139057 1562664087648576907604293)
              ·
                refine ⟨292999516434108170175805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1562664087648576907604293 292999516434108170175805)
                ·
                  refine ⟨109874818662790563815927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 292999516434108170175805 109874818662790563815927)
                  ·
                    rfl

theorem cell20_240728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4, 3].length) (baseStart_240728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240728 prefixEnd_240728 := by exact prefixLift 240728
  have htrace : WordTrace (prefixWord ++ tailWord_240728) baseStart_240728 baseEnd_240728 := by
    simpa [prefixWord, tailWord_240728, baseEnd_240728] using wordTrace_append hprefix tailTrace_240728
  have hstable : (prefixWord ++ tailWord_240728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240728).length < 2 ^ (prefixWord ++ tailWord_240728).sum := by decide
  have hdescent : baseEnd_240728 < baseStart_240728 := by decide
  rcases family_descends (prefixWord ++ tailWord_240728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240738 : List Nat := [3, 3, 2, 2, 1, 2, 2, 5]
def baseStart_240738 : Nat := 118140960795 + 240738 * 2 ^ 59
def prefixEnd_240738 : Nat := 4983230072969 + 3 ^ 40 * 240738 * 2
def baseEnd_240738 : Nat := 36626460978424991160851

theorem tailTrace_240738 : CollatzResearch.WordTrace tailWord_240738 prefixEnd_240738 36626460978424991160851 := by
  unfold tailWord_240738
  simp only [CollatzResearch.WordTrace]
  refine ⟨2195109050463703905548717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5853624134569877081463245 2195109050463703905548717)
  ·
    refine ⟨823165893923888964580769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2195109050463703905548717 823165893923888964580769)
    ·
      refine ⟨617374420442916723435577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 823165893923888964580769 617374420442916723435577)
      ·
        refine ⟨463030815332187542576683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 617374420442916723435577 463030815332187542576683)
        ·
          refine ⟨694546222998281313865025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463030815332187542576683 694546222998281313865025)
          ·
            refine ⟨520909667248710985398769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 694546222998281313865025 520909667248710985398769)
            ·
              refine ⟨390682250436533239049077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 520909667248710985398769 390682250436533239049077)
              ·
                refine ⟨36626460978424991160851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 390682250436533239049077 36626460978424991160851)
                ·
                  rfl

theorem cell20_240738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_240738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240738 prefixEnd_240738 := by exact prefixLift 240738
  have htrace : WordTrace (prefixWord ++ tailWord_240738) baseStart_240738 baseEnd_240738 := by
    simpa [prefixWord, tailWord_240738, baseEnd_240738] using wordTrace_append hprefix tailTrace_240738
  have hstable : (prefixWord ++ tailWord_240738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240738).length < 2 ^ (prefixWord ++ tailWord_240738).sum := by decide
  have hdescent : baseEnd_240738 < baseStart_240738 := by decide
  rcases family_descends (prefixWord ++ tailWord_240738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240745 : List Nat := [1, 2, 1, 1, 1, 6, 4, 1, 3]
def baseStart_240745 : Nat := 118140960795 + 240745 * 2 ^ 59
def prefixEnd_240745 : Nat := 4983230072969 + 3 ^ 40 * 240745 * 2
def baseEnd_240745 : Nat := 109882577926014060249191

theorem tailTrace_240745 : CollatzResearch.WordTrace tailWord_240745 prefixEnd_240745 109882577926014060249191 := by
  unfold tailWord_240745
  simp only [CollatzResearch.WordTrace]
  refine ⟨8780691512829455817699689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5853794341886303878466459 8780691512829455817699689)
  ·
    refine ⟨6585518634622091863274767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8780691512829455817699689 6585518634622091863274767)
    ·
      refine ⟨9878277951933137794912151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6585518634622091863274767 9878277951933137794912151)
      ·
        refine ⟨14817416927899706692368227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9878277951933137794912151 14817416927899706692368227)
        ·
          refine ⟨22226125391849560038552341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14817416927899706692368227 22226125391849560038552341)
          ·
            refine ⟨1041849627742948126807141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22226125391849560038552341 1041849627742948126807141)
            ·
              refine ⟨195346805201802773776339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1041849627742948126807141 195346805201802773776339)
              ·
                refine ⟨293020207802704160664509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195346805201802773776339 293020207802704160664509)
                ·
                  refine ⟨109882577926014060249191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 293020207802704160664509 109882577926014060249191)
                  ·
                    rfl

theorem cell20_240745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 1, 3].length) (baseStart_240745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240745 prefixEnd_240745 := by exact prefixLift 240745
  have htrace : WordTrace (prefixWord ++ tailWord_240745) baseStart_240745 baseEnd_240745 := by
    simpa [prefixWord, tailWord_240745, baseEnd_240745] using wordTrace_append hprefix tailTrace_240745
  have hstable : (prefixWord ++ tailWord_240745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240745).length < 2 ^ (prefixWord ++ tailWord_240745).sum := by decide
  have hdescent : baseEnd_240745 < baseStart_240745 := by decide
  rcases family_descends (prefixWord ++ tailWord_240745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240786 : List Nat := [3, 2, 3, 1, 1, 2, 4, 2, 2]
def baseStart_240786 : Nat := 118140960795 + 240786 * 2 ^ 59
def prefixEnd_240786 : Nat := 4983230072969 + 3 ^ 40 * 240786 * 2
def baseEnd_240786 : Nat := 109901291443200139882357

theorem tailTrace_240786 : CollatzResearch.WordTrace tailWord_240786 prefixEnd_240786 109901291443200139882357 := by
  unfold tailWord_240786
  simp only [CollatzResearch.WordTrace]
  refine ⟨2195546726420229954985553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5854791270453946546628141 2195546726420229954985553)
  ·
    refine ⟨1646660044815172466239165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2195546726420229954985553 1646660044815172466239165)
    ·
      refine ⟨617497516805689674839687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1646660044815172466239165 617497516805689674839687)
      ·
        refine ⟨926246275208534512259531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617497516805689674839687 926246275208534512259531)
        ·
          refine ⟨1389369412812801768389297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 926246275208534512259531 1389369412812801768389297)
          ·
            refine ⟨1042027059609601326291973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1389369412812801768389297 1042027059609601326291973)
            ·
              refine ⟨195380073676800248679745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1042027059609601326291973 195380073676800248679745)
              ·
                refine ⟨146535055257600186509809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195380073676800248679745 146535055257600186509809)
                ·
                  refine ⟨109901291443200139882357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146535055257600186509809 109901291443200139882357)
                  ·
                    rfl

theorem cell20_240786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 2, 2].length) (baseStart_240786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240786 prefixEnd_240786 := by exact prefixLift 240786
  have htrace : WordTrace (prefixWord ++ tailWord_240786) baseStart_240786 baseEnd_240786 := by
    simpa [prefixWord, tailWord_240786, baseEnd_240786] using wordTrace_append hprefix tailTrace_240786
  have hstable : (prefixWord ++ tailWord_240786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240786).length < 2 ^ (prefixWord ++ tailWord_240786).sum := by decide
  have hdescent : baseEnd_240786 < baseStart_240786 := by decide
  rcases family_descends (prefixWord ++ tailWord_240786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240787 : List Nat := [1, 1, 1, 2, 1, 2, 4, 3, 5]
def baseStart_240787 : Nat := 118140960795 + 240787 * 2 ^ 59
def prefixEnd_240787 : Nat := 4983230072969 + 3 ^ 40 * 240787 * 2
def baseEnd_240787 : Nat := 109901747870448580849019

theorem tailTrace_240787 : CollatzResearch.WordTrace tailWord_240787 prefixEnd_240787 109901747870448580849019 := by
  unfold tailWord_240787
  simp only [CollatzResearch.WordTrace]
  refine ⟨8782223378677296990728615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5854815585784864660485743 8782223378677296990728615)
  ·
    refine ⟨13173335068015945486092923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8782223378677296990728615 13173335068015945486092923)
    ·
      refine ⟨19760002602023918229139385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13173335068015945486092923 19760002602023918229139385)
      ·
        refine ⟨14820001951517938671854539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19760002602023918229139385 14820001951517938671854539)
        ·
          refine ⟨22230002927276908007781809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14820001951517938671854539 22230002927276908007781809)
          ·
            refine ⟨16672502195457681005836357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22230002927276908007781809 16672502195457681005836357)
            ·
              refine ⟨3126094161648315188594317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16672502195457681005836357 3126094161648315188594317)
              ·
                refine ⟨1172285310618118195722869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3126094161648315188594317 1172285310618118195722869)
                ·
                  refine ⟨109901747870448580849019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1172285310618118195722869 109901747870448580849019)
                  ·
                    rfl

theorem cell20_240787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 5].length) (baseStart_240787 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240787 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240787 prefixEnd_240787 := by exact prefixLift 240787
  have htrace : WordTrace (prefixWord ++ tailWord_240787) baseStart_240787 baseEnd_240787 := by
    simpa [prefixWord, tailWord_240787, baseEnd_240787] using wordTrace_append hprefix tailTrace_240787
  have hstable : (prefixWord ++ tailWord_240787).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240787).length < 2 ^ (prefixWord ++ tailWord_240787).sum := by decide
  have hdescent : baseEnd_240787 < baseStart_240787 := by decide
  rcases family_descends (prefixWord ++ tailWord_240787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240834 : List Nat := [3, 5, 1, 1, 2, 2, 1, 2, 3]
def baseStart_240834 : Nat := 118140960795 + 240834 * 2 ^ 59
def prefixEnd_240834 : Nat := 4983230072969 + 3 ^ 40 * 240834 * 2
def baseEnd_240834 : Nat := 109923199951125306282161

theorem tailTrace_240834 : CollatzResearch.WordTrace tailWord_240834 prefixEnd_240834 109923199951125306282161 := by
  unfold tailWord_240834
  simp only [CollatzResearch.WordTrace]
  refine ⟨2195984402376756004422389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5855958406338016011793037 2195984402376756004422389)
  ·
    refine ⟨205873537722820875414599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2195984402376756004422389 205873537722820875414599)
    ·
      refine ⟨308810306584231313121899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205873537722820875414599 308810306584231313121899)
      ·
        refine ⟨463215459876346969682849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308810306584231313121899 463215459876346969682849)
        ·
          refine ⟨347411594907260227262137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 463215459876346969682849 347411594907260227262137)
          ·
            refine ⟨260558696180445170446603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347411594907260227262137 260558696180445170446603)
            ·
              refine ⟨390838044270667755669905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260558696180445170446603 390838044270667755669905)
              ·
                refine ⟨293128533203000816752429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 390838044270667755669905 293128533203000816752429)
                ·
                  refine ⟨109923199951125306282161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 293128533203000816752429 109923199951125306282161)
                  ·
                    rfl

theorem cell20_240834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_240834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240834 prefixEnd_240834 := by exact prefixLift 240834
  have htrace : WordTrace (prefixWord ++ tailWord_240834) baseStart_240834 baseEnd_240834 := by
    simpa [prefixWord, tailWord_240834, baseEnd_240834] using wordTrace_append hprefix tailTrace_240834
  have hstable : (prefixWord ++ tailWord_240834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240834).length < 2 ^ (prefixWord ++ tailWord_240834).sum := by decide
  have hdescent : baseEnd_240834 < baseStart_240834 := by decide
  rcases family_descends (prefixWord ++ tailWord_240834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240842 : List Nat := [3, 1, 2, 1, 3, 3, 1, 1, 5]
def baseStart_240842 : Nat := 118140960795 + 240842 * 2 ^ 59
def prefixEnd_240842 : Nat := 4983230072969 + 3 ^ 40 * 240842 * 2
def baseEnd_240842 : Nat := 109926851369112834015461

theorem tailTrace_240842 : CollatzResearch.WordTrace tailWord_240842 prefixEnd_240842 109926851369112834015461 := by
  unfold tailWord_240842
  simp only [CollatzResearch.WordTrace]
  refine ⟨2196057348369510345995195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5856152928985360922653853 2196057348369510345995195)
  ·
    refine ⟨3294086022554265518992793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2196057348369510345995195 3294086022554265518992793)
    ·
      refine ⟨2470564516915699139244595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3294086022554265518992793 2470564516915699139244595)
      ·
        refine ⟨3705846775373548708866893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2470564516915699139244595 3705846775373548708866893)
        ·
          refine ⟨1389692540765080765825085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3705846775373548708866893 1389692540765080765825085)
          ·
            refine ⟨521134702786905287184407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1389692540765080765825085 521134702786905287184407)
            ·
              refine ⟨781702054180357930776611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 521134702786905287184407 781702054180357930776611)
              ·
                refine ⟨1172553081270536896164917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 781702054180357930776611 1172553081270536896164917)
                ·
                  refine ⟨109926851369112834015461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1172553081270536896164917 109926851369112834015461)
                  ·
                    rfl

theorem cell20_240842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_240842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240842 prefixEnd_240842 := by exact prefixLift 240842
  have htrace : WordTrace (prefixWord ++ tailWord_240842) baseStart_240842 baseEnd_240842 := by
    simpa [prefixWord, tailWord_240842, baseEnd_240842] using wordTrace_append hprefix tailTrace_240842
  have hstable : (prefixWord ++ tailWord_240842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240842).length < 2 ^ (prefixWord ++ tailWord_240842).sum := by decide
  have hdescent : baseEnd_240842 < baseStart_240842 := by decide
  rcases family_descends (prefixWord ++ tailWord_240842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240869 : List Nat := [1, 3, 1, 4, 4, 1, 2, 4]
def baseStart_240869 : Nat := 118140960795 + 240869 * 2 ^ 59
def prefixEnd_240869 : Nat := 4983230072969 + 3 ^ 40 * 240869 * 2
def baseEnd_240869 : Nat := 36646391634940246705117

theorem tailTrace_240869 : CollatzResearch.WordTrace tailWord_240869 prefixEnd_240869 36646391634940246705117 := by
  unfold tailWord_240869
  simp only [CollatzResearch.WordTrace]
  refine ⟨8785214164380224995213661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5856809442920149996809107 8785214164380224995213661)
  ·
    refine ⟨3294455311642584373205123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8785214164380224995213661 3294455311642584373205123)
    ·
      refine ⟨4941682967463876559807685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3294455311642584373205123 4941682967463876559807685)
      ·
        refine ⟨926565556399476854963941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4941682967463876559807685 926565556399476854963941)
        ·
          refine ⟨173731041824901910305739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 926565556399476854963941 173731041824901910305739)
          ·
            refine ⟨260596562737352865458609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173731041824901910305739 260596562737352865458609)
            ·
              refine ⟨195447422053014649093957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260596562737352865458609 195447422053014649093957)
              ·
                refine ⟨36646391634940246705117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195447422053014649093957 36646391634940246705117)
                ·
                  rfl

theorem cell20_240869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 4].length) (baseStart_240869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240869 prefixEnd_240869 := by exact prefixLift 240869
  have htrace : WordTrace (prefixWord ++ tailWord_240869) baseStart_240869 baseEnd_240869 := by
    simpa [prefixWord, tailWord_240869, baseEnd_240869] using wordTrace_append hprefix tailTrace_240869
  have hstable : (prefixWord ++ tailWord_240869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240869).length < 2 ^ (prefixWord ++ tailWord_240869).sum := by decide
  have hdescent : baseEnd_240869 < baseStart_240869 := by decide
  rcases family_descends (prefixWord ++ tailWord_240869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240883 : List Nat := [1, 1, 1, 2, 2, 7, 1, 3, 2]
def baseStart_240883 : Nat := 118140960795 + 240883 * 2 ^ 59
def prefixEnd_240883 : Nat := 4983230072969 + 3 ^ 40 * 240883 * 2
def baseEnd_240883 : Nat := 109945564886298913648627

theorem tailTrace_240883 : CollatzResearch.WordTrace tailWord_240883 prefixEnd_240883 109945564886298913648627 := by
  unfold tailWord_240883
  simp only [CollatzResearch.WordTrace]
  refine ⟨8785724786329505386223303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5857149857553003590815535 8785724786329505386223303)
  ·
    refine ⟨13178587179494258079334955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8785724786329505386223303 13178587179494258079334955)
    ·
      refine ⟨19767880769241387119002433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13178587179494258079334955 19767880769241387119002433)
      ·
        refine ⟨14825910576931040339251825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19767880769241387119002433 14825910576931040339251825)
        ·
          refine ⟨11119432932698280254438869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14825910576931040339251825 11119432932698280254438869)
          ·
            refine ⟨260611709360115943463411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 11119432932698280254438869 260611709360115943463411)
            ·
              refine ⟨390917564040173915195117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260611709360115943463411 390917564040173915195117)
              ·
                refine ⟨146594086515065218198169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 390917564040173915195117 146594086515065218198169)
                ·
                  refine ⟨109945564886298913648627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146594086515065218198169 109945564886298913648627)
                  ·
                    rfl

theorem cell20_240883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 3, 2].length) (baseStart_240883 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240883 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240883 prefixEnd_240883 := by exact prefixLift 240883
  have htrace : WordTrace (prefixWord ++ tailWord_240883) baseStart_240883 baseEnd_240883 := by
    simpa [prefixWord, tailWord_240883, baseEnd_240883] using wordTrace_append hprefix tailTrace_240883
  have hstable : (prefixWord ++ tailWord_240883).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240883).length < 2 ^ (prefixWord ++ tailWord_240883).sum := by decide
  have hdescent : baseEnd_240883 < baseStart_240883 := by decide
  rcases family_descends (prefixWord ++ tailWord_240883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240900 : List Nat := [2, 3, 2, 2, 2, 2, 3, 2, 2]
def baseStart_240900 : Nat := 118140960795 + 240900 * 2 ^ 59
def prefixEnd_240900 : Nat := 4983230072969 + 3 ^ 40 * 240900 * 2
def baseEnd_240900 : Nat := 109953324149522410081891

theorem tailTrace_240900 : CollatzResearch.WordTrace tailWord_240900 prefixEnd_240900 109953324149522410081891 := by
  unfold tailWord_240900
  simp only [CollatzResearch.WordTrace]
  refine ⟨4393172413633958644796077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5857563218178611526394769 4393172413633958644796077)
  ·
    refine ⟨1647439655112734491798529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4393172413633958644796077 1647439655112734491798529)
    ·
      refine ⟨1235579741334550868848897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1647439655112734491798529 1235579741334550868848897)
      ·
        refine ⟨926684806000913151636673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1235579741334550868848897 926684806000913151636673)
        ·
          refine ⟨695013604500684863727505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 926684806000913151636673 695013604500684863727505)
          ·
            refine ⟨521260203375513647795629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 695013604500684863727505 521260203375513647795629)
            ·
              refine ⟨195472576265817617923361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 521260203375513647795629 195472576265817617923361)
              ·
                refine ⟨146604432199363213442521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195472576265817617923361 146604432199363213442521)
                ·
                  refine ⟨109953324149522410081891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146604432199363213442521 109953324149522410081891)
                  ·
                    rfl

theorem cell20_240900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 2, 2].length) (baseStart_240900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240900 prefixEnd_240900 := by exact prefixLift 240900
  have htrace : WordTrace (prefixWord ++ tailWord_240900) baseStart_240900 baseEnd_240900 := by
    simpa [prefixWord, tailWord_240900, baseEnd_240900] using wordTrace_append hprefix tailTrace_240900
  have hstable : (prefixWord ++ tailWord_240900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240900).length < 2 ^ (prefixWord ++ tailWord_240900).sum := by decide
  have hdescent : baseEnd_240900 < baseStart_240900 := by decide
  rcases family_descends (prefixWord ++ tailWord_240900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240901 : List Nat := [1, 3, 1, 1, 2, 1, 3, 3, 5]
def baseStart_240901 : Nat := 118140960795 + 240901 * 2 ^ 59
def prefixEnd_240901 : Nat := 4983230072969 + 3 ^ 40 * 240901 * 2
def baseEnd_240901 : Nat := 109953780576770851048553

theorem tailTrace_240901 : CollatzResearch.WordTrace tailWord_240901 prefixEnd_240901 109953780576770851048553 := by
  unfold tailWord_240901
  simp only [CollatzResearch.WordTrace]
  refine ⟨8786381300264294460378557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5857587533509529640252371 8786381300264294460378557)
  ·
    refine ⟨3294892987599110422641959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8786381300264294460378557 3294892987599110422641959)
    ·
      refine ⟨4942339481398665633962939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3294892987599110422641959 4942339481398665633962939)
      ·
        refine ⟨7413509222097998450944409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4942339481398665633962939 7413509222097998450944409)
        ·
          refine ⟨5560131916573498838208307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7413509222097998450944409 5560131916573498838208307)
          ·
            refine ⟨8340197874860248257312461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5560131916573498838208307 8340197874860248257312461)
            ·
              refine ⟨3127574203072593096492173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8340197874860248257312461 3127574203072593096492173)
              ·
                refine ⟨1172840326152222411184565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3127574203072593096492173 1172840326152222411184565)
                ·
                  refine ⟨109953780576770851048553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1172840326152222411184565 109953780576770851048553)
                  ·
                    rfl

theorem cell20_240901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_240901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240901 prefixEnd_240901 := by exact prefixLift 240901
  have htrace : WordTrace (prefixWord ++ tailWord_240901) baseStart_240901 baseEnd_240901 := by
    simpa [prefixWord, tailWord_240901, baseEnd_240901] using wordTrace_append hprefix tailTrace_240901
  have hstable : (prefixWord ++ tailWord_240901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240901).length < 2 ^ (prefixWord ++ tailWord_240901).sum := by decide
  have hdescent : baseEnd_240901 < baseStart_240901 := by decide
  rcases family_descends (prefixWord ++ tailWord_240901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240932 : List Nat := [2, 3, 1, 3, 1, 1, 1, 8]
def baseStart_240932 : Nat := 118140960795 + 240932 * 2 ^ 59
def prefixEnd_240932 : Nat := 4983230072969 + 3 ^ 40 * 240932 * 2
def baseEnd_240932 : Nat := 36655976607157507005031

theorem tailTrace_240932 : CollatzResearch.WordTrace tailWord_240932 prefixEnd_240932 36655976607157507005031 := by
  unfold tailWord_240932
  simp only [CollatzResearch.WordTrace]
  refine ⟨4393755981575993377378525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5858341308767991169838033 4393755981575993377378525)
  ·
    refine ⟨1647658493090997516516947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4393755981575993377378525 1647658493090997516516947)
    ·
      refine ⟨2471487739636496274775421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1647658493090997516516947 2471487739636496274775421)
      ·
        refine ⟨926807902363686103040783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2471487739636496274775421 926807902363686103040783)
        ·
          refine ⟨1390211853545529154561175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 926807902363686103040783 1390211853545529154561175)
          ·
            refine ⟨2085317780318293731841763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1390211853545529154561175 2085317780318293731841763)
            ·
              refine ⟨3127976670477440597762645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2085317780318293731841763 3127976670477440597762645)
              ·
                refine ⟨36655976607157507005031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3127976670477440597762645 36655976607157507005031)
                ·
                  rfl

theorem cell20_240932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 8].length) (baseStart_240932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240932 prefixEnd_240932 := by exact prefixLift 240932
  have htrace : WordTrace (prefixWord ++ tailWord_240932) baseStart_240932 baseEnd_240932 := by
    simpa [prefixWord, tailWord_240932, baseEnd_240932] using wordTrace_append hprefix tailTrace_240932
  have hstable : (prefixWord ++ tailWord_240932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240932).length < 2 ^ (prefixWord ++ tailWord_240932).sum := by decide
  have hdescent : baseEnd_240932 < baseStart_240932 := by decide
  rcases family_descends (prefixWord ++ tailWord_240932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240956 : List Nat := [2, 2, 2, 2, 1, 3, 1, 4, 3]
def baseStart_240956 : Nat := 118140960795 + 240956 * 2 ^ 59
def prefixEnd_240956 : Nat := 4983230072969 + 3 ^ 40 * 240956 * 2
def baseEnd_240956 : Nat := 109978884075435104214995

theorem tailTrace_240956 : CollatzResearch.WordTrace tailWord_240956 prefixEnd_240956 109978884075435104214995 := by
  unfold tailWord_240956
  simp only [CollatzResearch.WordTrace]
  refine ⟨4394193657532519426815361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5858924876710025902420481 4394193657532519426815361)
  ·
    refine ⟨3295645243149389570111521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4394193657532519426815361 3295645243149389570111521)
    ·
      refine ⟨2471733932362042177583641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3295645243149389570111521 2471733932362042177583641)
      ·
        refine ⟨1853800449271531633187731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2471733932362042177583641 1853800449271531633187731)
        ·
          refine ⟨2780700673907297449781597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1853800449271531633187731 2780700673907297449781597)
          ·
            refine ⟨1042762752715236543668099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2780700673907297449781597 1042762752715236543668099)
            ·
              refine ⟨1564144129072854815502149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1042762752715236543668099 1564144129072854815502149)
              ·
                refine ⟨293277024201160277906653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1564144129072854815502149 293277024201160277906653)
                ·
                  refine ⟨109978884075435104214995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 293277024201160277906653 109978884075435104214995)
                  ·
                    rfl

theorem cell20_240956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4, 3].length) (baseStart_240956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240956 prefixEnd_240956 := by exact prefixLift 240956
  have htrace : WordTrace (prefixWord ++ tailWord_240956) baseStart_240956 baseEnd_240956 := by
    simpa [prefixWord, tailWord_240956, baseEnd_240956] using wordTrace_append hprefix tailTrace_240956
  have hstable : (prefixWord ++ tailWord_240956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240956).length < 2 ^ (prefixWord ++ tailWord_240956).sum := by decide
  have hdescent : baseEnd_240956 < baseStart_240956 := by decide
  rcases family_descends (prefixWord ++ tailWord_240956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240959 : List Nat := [1, 1, 2, 2, 4, 2, 4, 2, 2]
def baseStart_240959 : Nat := 118140960795 + 240959 * 2 ^ 59
def prefixEnd_240959 : Nat := 4983230072969 + 3 ^ 40 * 240959 * 2
def baseEnd_240959 : Nat := 109980253357180427114983

theorem tailTrace_240959 : CollatzResearch.WordTrace tailWord_240959 prefixEnd_240959 109980253357180427114983 := by
  unfold tailWord_240959
  simp only [CollatzResearch.WordTrace]
  refine ⟨8788496734054170365989931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5858997822702780243993287 8788496734054170365989931)
  ·
    refine ⟨13182745101081255548984897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8788496734054170365989931 13182745101081255548984897)
    ·
      refine ⟨9887058825810941661738673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13182745101081255548984897 9887058825810941661738673)
      ·
        refine ⟨7415294119358206246304005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9887058825810941661738673 7415294119358206246304005)
        ·
          refine ⟨1390367647379663671182001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7415294119358206246304005 1390367647379663671182001)
          ·
            refine ⟨1042775735534747753386501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1390367647379663671182001 1042775735534747753386501)
            ·
              refine ⟨195520450412765203759969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1042775735534747753386501 195520450412765203759969)
              ·
                refine ⟨146640337809573902819977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195520450412765203759969 146640337809573902819977)
                ·
                  refine ⟨109980253357180427114983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146640337809573902819977 109980253357180427114983)
                  ·
                    rfl

theorem cell20_240959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 2, 2].length) (baseStart_240959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240959 prefixEnd_240959 := by exact prefixLift 240959
  have htrace : WordTrace (prefixWord ++ tailWord_240959) baseStart_240959 baseEnd_240959 := by
    simpa [prefixWord, tailWord_240959, baseEnd_240959] using wordTrace_append hprefix tailTrace_240959
  have hstable : (prefixWord ++ tailWord_240959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240959).length < 2 ^ (prefixWord ++ tailWord_240959).sum := by decide
  have hdescent : baseEnd_240959 < baseStart_240959 := by decide
  rcases family_descends (prefixWord ++ tailWord_240959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240994 : List Nat := [3, 3, 2, 1, 1, 1, 2, 2, 5]
def baseStart_240994 : Nat := 118140960795 + 240994 * 2 ^ 59
def prefixEnd_240994 : Nat := 4983230072969 + 3 ^ 40 * 240994 * 2
def baseEnd_240994 : Nat := 109996228310875860948173

theorem tailTrace_240994 : CollatzResearch.WordTrace tailWord_240994 prefixEnd_240994 109996228310875860948173 := by
  unfold tailWord_240994
  simp only [CollatzResearch.WordTrace]
  refine ⟨2197443322231842835878509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5859848859284914229009357 2197443322231842835878509)
  ·
    refine ⟨824041245836941063454441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2197443322231842835878509 824041245836941063454441)
    ·
      refine ⟨618030934377705797590831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 824041245836941063454441 618030934377705797590831)
      ·
        refine ⟨927046401566558696386247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 618030934377705797590831 927046401566558696386247)
        ·
          refine ⟨1390569602349838044579371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 927046401566558696386247 1390569602349838044579371)
          ·
            refine ⟨2085854403524757066869057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1390569602349838044579371 2085854403524757066869057)
            ·
              refine ⟨1564390802643567800151793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2085854403524757066869057 1564390802643567800151793)
              ·
                refine ⟨1173293101982675850113845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1564390802643567800151793 1173293101982675850113845)
                ·
                  refine ⟨109996228310875860948173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1173293101982675850113845 109996228310875860948173)
                  ·
                    rfl

theorem cell20_240994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_240994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_240994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_240994 prefixEnd_240994 := by exact prefixLift 240994
  have htrace : WordTrace (prefixWord ++ tailWord_240994) baseStart_240994 baseEnd_240994 := by
    simpa [prefixWord, tailWord_240994, baseEnd_240994] using wordTrace_append hprefix tailTrace_240994
  have hstable : (prefixWord ++ tailWord_240994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240994).length < 2 ^ (prefixWord ++ tailWord_240994).sum := by decide
  have hdescent : baseEnd_240994 < baseStart_240994 := by decide
  rcases family_descends (prefixWord ++ tailWord_240994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241015 : List Nat := [1, 1, 3, 1, 1, 2, 5, 1, 5]
def baseStart_241015 : Nat := 118140960795 + 241015 * 2 ^ 59
def prefixEnd_241015 : Nat := 4983230072969 + 3 ^ 40 * 241015 * 2
def baseEnd_241015 : Nat := 110005813283093121248087

theorem tailTrace_241015 : CollatzResearch.WordTrace tailWord_241015 prefixEnd_241015 110005813283093121248087 := by
  unfold tailWord_241015
  simp only [CollatzResearch.WordTrace]
  refine ⟨8790539221851291930028499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5860359481234194620018999 8790539221851291930028499)
  ·
    refine ⟨13185808832776937895042749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8790539221851291930028499 13185808832776937895042749)
    ·
      refine ⟨4944678312291351710641031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13185808832776937895042749 4944678312291351710641031)
      ·
        refine ⟨7417017468437027565961547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4944678312291351710641031 7417017468437027565961547)
        ·
          refine ⟨11125526202655541348942321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7417017468437027565961547 11125526202655541348942321)
          ·
            refine ⟨8344144651991656011706741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11125526202655541348942321 8344144651991656011706741)
            ·
              refine ⟨782263561124217751097507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8344144651991656011706741 782263561124217751097507)
              ·
                refine ⟨1173395341686326626646261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 782263561124217751097507 1173395341686326626646261)
                ·
                  refine ⟨110005813283093121248087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1173395341686326626646261 110005813283093121248087)
                  ·
                    rfl

theorem cell20_241015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 5].length) (baseStart_241015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241015 prefixEnd_241015 := by exact prefixLift 241015
  have htrace : WordTrace (prefixWord ++ tailWord_241015) baseStart_241015 baseEnd_241015 := by
    simpa [prefixWord, tailWord_241015, baseEnd_241015] using wordTrace_append hprefix tailTrace_241015
  have hstable : (prefixWord ++ tailWord_241015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241015).length < 2 ^ (prefixWord ++ tailWord_241015).sum := by decide
  have hdescent : baseEnd_241015 < baseStart_241015 := by decide
  rcases family_descends (prefixWord ++ tailWord_241015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241042 : List Nat := [3, 2, 3, 3, 1, 1, 1, 6]
def baseStart_241042 : Nat := 118140960795 + 241042 * 2 ^ 59
def prefixEnd_241042 : Nat := 4983230072969 + 3 ^ 40 * 241042 * 2
def baseEnd_241042 : Nat := 36672712272933675782659

theorem tailTrace_241042 : CollatzResearch.WordTrace tailWord_241042 prefixEnd_241042 36672712272933675782659 := by
  unfold tailWord_241042
  simp only [CollatzResearch.WordTrace]
  refine ⟨2197880998188368885315345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5861015995168983694174253 2197880998188368885315345)
  ·
    refine ⟨1648410748641276663986509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2197880998188368885315345 1648410748641276663986509)
    ·
      refine ⟨618154030740478748994941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1648410748641276663986509 618154030740478748994941)
      ·
        refine ⟨231807761527679530873103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 618154030740478748994941 231807761527679530873103)
        ·
          refine ⟨347711642291519296309655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231807761527679530873103 347711642291519296309655)
          ·
            refine ⟨521567463437278944464483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347711642291519296309655 521567463437278944464483)
            ·
              refine ⟨782351195155918416696725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 521567463437278944464483 782351195155918416696725)
              ·
                refine ⟨36672712272933675782659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 782351195155918416696725 36672712272933675782659)
                ·
                  rfl

theorem cell20_241042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 6].length) (baseStart_241042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241042 prefixEnd_241042 := by exact prefixLift 241042
  have htrace : WordTrace (prefixWord ++ tailWord_241042) baseStart_241042 baseEnd_241042 := by
    simpa [prefixWord, tailWord_241042, baseEnd_241042] using wordTrace_append hprefix tailTrace_241042
  have hstable : (prefixWord ++ tailWord_241042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241042).length < 2 ^ (prefixWord ++ tailWord_241042).sum := by decide
  have hdescent : baseEnd_241042 < baseStart_241042 := by decide
  rcases family_descends (prefixWord ++ tailWord_241042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241073 : List Nat := [1, 2, 2, 4, 1, 1, 5, 2, 2]
def baseStart_241073 : Nat := 118140960795 + 241073 * 2 ^ 59
def prefixEnd_241073 : Nat := 4983230072969 + 3 ^ 40 * 241073 * 2
def baseEnd_241073 : Nat := 110032286063502697314517

theorem tailTrace_241073 : CollatzResearch.WordTrace tailWord_241073 prefixEnd_241073 110032286063502697314517 := by
  unfold tailWord_241073
  simp only [CollatzResearch.WordTrace]
  refine ⟨8792654655641167835639873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5861769770427445223759915 8792654655641167835639873)
  ·
    refine ⟨6594490991730875876729905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8792654655641167835639873 6594490991730875876729905)
    ·
      refine ⟨4945868243798156907547429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6594490991730875876729905 4945868243798156907547429)
      ·
        refine ⟨927350295712154420165143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4945868243798156907547429 927350295712154420165143)
        ·
          refine ⟨1391025443568231630247715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 927350295712154420165143 1391025443568231630247715)
          ·
            refine ⟨2086538165352347445371573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1391025443568231630247715 2086538165352347445371573)
            ·
              refine ⟨195612953001782573003585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2086538165352347445371573 195612953001782573003585)
              ·
                refine ⟨146709714751336929752689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195612953001782573003585 146709714751336929752689)
                ·
                  refine ⟨110032286063502697314517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146709714751336929752689 110032286063502697314517)
                  ·
                    rfl

theorem cell20_241073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 2, 2].length) (baseStart_241073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241073 prefixEnd_241073 := by exact prefixLift 241073
  have htrace : WordTrace (prefixWord ++ tailWord_241073) baseStart_241073 baseEnd_241073 := by
    simpa [prefixWord, tailWord_241073, baseEnd_241073] using wordTrace_append hprefix tailTrace_241073
  have hstable : (prefixWord ++ tailWord_241073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241073).length < 2 ^ (prefixWord ++ tailWord_241073).sum := by decide
  have hdescent : baseEnd_241073 < baseStart_241073 := by decide
  rcases family_descends (prefixWord ++ tailWord_241073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241122 : List Nat := [3, 3, 3, 11]
def baseStart_241122 : Nat := 118140960795 + 241122 * 2 ^ 59
def prefixEnd_241122 : Nat := 4983230072969 + 3 ^ 40 * 241122 * 2
def baseEnd_241122 : Nat := 452899798348462159181

theorem tailTrace_241122 : CollatzResearch.WordTrace tailWord_241122 prefixEnd_241122 452899798348462159181 := by
  unfold tailWord_241122
  simp only [CollatzResearch.WordTrace]
  refine ⟨2198610458115912301043405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5862961221642432802782413 2198610458115912301043405)
  ·
    refine ⟨824478921793467112891277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2198610458115912301043405 824478921793467112891277)
    ·
      refine ⟨309179595672550167334229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 824478921793467112891277 309179595672550167334229)
      ·
        refine ⟨452899798348462159181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 309179595672550167334229 452899798348462159181)
        ·
          rfl

theorem cell20_241122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 11].length) (baseStart_241122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241122 prefixEnd_241122 := by exact prefixLift 241122
  have htrace : WordTrace (prefixWord ++ tailWord_241122) baseStart_241122 baseEnd_241122 := by
    simpa [prefixWord, tailWord_241122, baseEnd_241122] using wordTrace_append hprefix tailTrace_241122
  have hstable : (prefixWord ++ tailWord_241122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241122).length < 2 ^ (prefixWord ++ tailWord_241122).sum := by decide
  have hdescent : baseEnd_241122 < baseStart_241122 := by decide
  rcases family_descends (prefixWord ++ tailWord_241122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241125 : List Nat := [1, 3, 1, 5, 1, 2, 2, 2, 3]
def baseStart_241125 : Nat := 118140960795 + 241125 * 2 ^ 59
def prefixEnd_241125 : Nat := 4983230072969 + 3 ^ 40 * 241125 * 2
def baseEnd_241125 : Nat := 110056020280421627580971

theorem tailTrace_241125 : CollatzResearch.WordTrace tailWord_241125 prefixEnd_241125 110056020280421627580971 := by
  unfold tailWord_241125
  simp only [CollatzResearch.WordTrace]
  refine ⟨8794551251452780716532829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5863034167635187144355219 8794551251452780716532829)
  ·
    refine ⟨3297956719294792768699811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8794551251452780716532829 3297956719294792768699811)
    ·
      refine ⟨4946935078942189153049717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3297956719294792768699811 4946935078942189153049717)
      ·
        refine ⟨463775163650830233098411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4946935078942189153049717 463775163650830233098411)
        ·
          refine ⟨695662745476245349647617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463775163650830233098411 695662745476245349647617)
          ·
            refine ⟨521747059107184012235713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 695662745476245349647617 521747059107184012235713)
            ·
              refine ⟨391310294330388009176785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 521747059107184012235713 391310294330388009176785)
              ·
                refine ⟨293482720747791006882589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 391310294330388009176785 293482720747791006882589)
                ·
                  refine ⟨110056020280421627580971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 293482720747791006882589 110056020280421627580971)
                  ·
                    rfl

theorem cell20_241125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2, 3].length) (baseStart_241125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241125 prefixEnd_241125 := by exact prefixLift 241125
  have htrace : WordTrace (prefixWord ++ tailWord_241125) baseStart_241125 baseEnd_241125 := by
    simpa [prefixWord, tailWord_241125, baseEnd_241125] using wordTrace_append hprefix tailTrace_241125
  have hstable : (prefixWord ++ tailWord_241125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241125).length < 2 ^ (prefixWord ++ tailWord_241125).sum := by decide
  have hdescent : baseEnd_241125 < baseStart_241125 := by decide
  rcases family_descends (prefixWord ++ tailWord_241125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241143 : List Nat := [1, 1, 3, 1, 1, 1, 1, 11]
def baseStart_241143 : Nat := 118140960795 + 241143 * 2 ^ 59
def prefixEnd_241143 : Nat := 4983230072969 + 3 ^ 40 * 241143 * 2
def baseEnd_241143 : Nat := 36688078656964521660299

theorem tailTrace_241143 : CollatzResearch.WordTrace tailWord_241143 prefixEnd_241143 36688078656964521660299 := by
  unfold tailWord_241143
  simp only [CollatzResearch.WordTrace]
  refine ⟨8795207765387569790688083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5863471843591713193792055 8795207765387569790688083)
  ·
    refine ⟨13192811648081354686032125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8795207765387569790688083 13192811648081354686032125)
    ·
      refine ⟨4947304368030508007262047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13192811648081354686032125 4947304368030508007262047)
      ·
        refine ⟨7420956552045762010893071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4947304368030508007262047 7420956552045762010893071)
        ·
          refine ⟨11131434828068643016339607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7420956552045762010893071 11131434828068643016339607)
          ·
            refine ⟨16697152242102964524509411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11131434828068643016339607 16697152242102964524509411)
            ·
              refine ⟨25045728363154446786764117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16697152242102964524509411 25045728363154446786764117)
              ·
                refine ⟨36688078656964521660299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 25045728363154446786764117 36688078656964521660299)
                ·
                  rfl

theorem cell20_241143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 11].length) (baseStart_241143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241143 prefixEnd_241143 := by exact prefixLift 241143
  have htrace : WordTrace (prefixWord ++ tailWord_241143) baseStart_241143 baseEnd_241143 := by
    simpa [prefixWord, tailWord_241143, baseEnd_241143] using wordTrace_append hprefix tailTrace_241143
  have hstable : (prefixWord ++ tailWord_241143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241143).length < 2 ^ (prefixWord ++ tailWord_241143).sum := by decide
  have hdescent : baseEnd_241143 < baseStart_241143 := by decide
  rcases family_descends (prefixWord ++ tailWord_241143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241156 : List Nat := [2, 3, 2, 3, 2, 1, 3, 4]
def baseStart_241156 : Nat := 118140960795 + 241156 * 2 ^ 59
def prefixEnd_241156 : Nat := 4983230072969 + 3 ^ 40 * 241156 * 2
def baseEnd_241156 : Nat := 36690056508374432515837

theorem tailTrace_241156 : CollatzResearch.WordTrace tailWord_241156 prefixEnd_241156 36690056508374432515837 := by
  unfold tailWord_241156
  simp only [CollatzResearch.WordTrace]
  refine ⟨4397840957170236505455661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5863787942893648673940881 4397840957170236505455661)
  ·
    refine ⟨1649190358938838689545873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4397840957170236505455661 1649190358938838689545873)
    ·
      refine ⟨1236892769204129017159405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1649190358938838689545873 1236892769204129017159405)
      ·
        refine ⟨463834788451548381434777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1236892769204129017159405 463834788451548381434777)
        ·
          refine ⟨347876091338661286076083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 463834788451548381434777 347876091338661286076083)
          ·
            refine ⟨521814137007991929114125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347876091338661286076083 521814137007991929114125)
            ·
              refine ⟨195680301377996973417797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 521814137007991929114125 195680301377996973417797)
              ·
                refine ⟨36690056508374432515837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195680301377996973417797 36690056508374432515837)
                ·
                  rfl

theorem cell20_241156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 4].length) (baseStart_241156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241156 prefixEnd_241156 := by exact prefixLift 241156
  have htrace : WordTrace (prefixWord ++ tailWord_241156) baseStart_241156 baseEnd_241156 := by
    simpa [prefixWord, tailWord_241156, baseEnd_241156] using wordTrace_append hprefix tailTrace_241156
  have hstable : (prefixWord ++ tailWord_241156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241156).length < 2 ^ (prefixWord ++ tailWord_241156).sum := by decide
  have hdescent : baseEnd_241156 < baseStart_241156 := by decide
  rcases family_descends (prefixWord ++ tailWord_241156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241184 : List Nat := [2, 1, 1, 6, 1, 2, 1, 1, 5]
def baseStart_241184 : Nat := 118140960795 + 241184 * 2 ^ 59
def prefixEnd_241184 : Nat := 4983230072969 + 3 ^ 40 * 241184 * 2
def baseEnd_241184 : Nat := 110082949488079644614063

theorem tailTrace_241184 : CollatzResearch.WordTrace tailWord_241184 prefixEnd_241184 110082949488079644614063 := by
  unfold tailWord_241184
  simp only [CollatzResearch.WordTrace]
  refine ⟨4398351579119516896465303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5864468772159355861953737 4398351579119516896465303)
  ·
    refine ⟨6597527368679275344697955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4398351579119516896465303 6597527368679275344697955)
    ·
      refine ⟨9896291053018913017046933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6597527368679275344697955 9896291053018913017046933)
      ·
        refine ⟨463888643110261547674075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9896291053018913017046933 463888643110261547674075)
        ·
          refine ⟨695832964665392321511113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463888643110261547674075 695832964665392321511113)
          ·
            refine ⟨521874723499044241133335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 695832964665392321511113 521874723499044241133335)
            ·
              refine ⟨782812085248566361700003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 521874723499044241133335 782812085248566361700003)
              ·
                refine ⟨1174218127872849542550005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 782812085248566361700003 1174218127872849542550005)
                ·
                  refine ⟨110082949488079644614063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1174218127872849542550005 110082949488079644614063)
                  ·
                    rfl

theorem cell20_241184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 5].length) (baseStart_241184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241184 prefixEnd_241184 := by exact prefixLift 241184
  have htrace : WordTrace (prefixWord ++ tailWord_241184) baseStart_241184 baseEnd_241184 := by
    simpa [prefixWord, tailWord_241184, baseEnd_241184] using wordTrace_append hprefix tailTrace_241184
  have hstable : (prefixWord ++ tailWord_241184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241184).length < 2 ^ (prefixWord ++ tailWord_241184).sum := by decide
  have hdescent : baseEnd_241184 < baseStart_241184 := by decide
  rcases family_descends (prefixWord ++ tailWord_241184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241215 : List Nat := [1, 1, 2, 2, 3, 5, 2, 4]
def baseStart_241215 : Nat := 118140960795 + 241215 * 2 ^ 59
def prefixEnd_241215 : Nat := 4983230072969 + 3 ^ 40 * 241215 * 2
def baseEnd_241215 : Nat := 36699032910927104860201

theorem tailTrace_241215 : CollatzResearch.WordTrace tailWord_241215 prefixEnd_241215 36699032910927104860201 := by
  unfold tailWord_241215
  simp only [CollatzResearch.WordTrace]
  refine ⟨8797833821126726087309099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5865222547417817391539399 8797833821126726087309099)
  ·
    refine ⟨13196750731690089130963649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8797833821126726087309099 13196750731690089130963649)
    ·
      refine ⟨9897563048767566848222737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13196750731690089130963649 9897563048767566848222737)
      ·
        refine ⟨7423172286575675136167053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9897563048767566848222737 7423172286575675136167053)
        ·
          refine ⟨2783689607465878176062645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7423172286575675136167053 2783689607465878176062645)
          ·
            refine ⟨260970900699926079005873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2783689607465878176062645 260970900699926079005873)
            ·
              refine ⟨195728175524944559254405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260970900699926079005873 195728175524944559254405)
              ·
                refine ⟨36699032910927104860201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195728175524944559254405 36699032910927104860201)
                ·
                  rfl

theorem cell20_241215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 4].length) (baseStart_241215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241215 prefixEnd_241215 := by exact prefixLift 241215
  have htrace : WordTrace (prefixWord ++ tailWord_241215) baseStart_241215 baseEnd_241215 := by
    simpa [prefixWord, tailWord_241215, baseEnd_241215] using wordTrace_append hprefix tailTrace_241215
  have hstable : (prefixWord ++ tailWord_241215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241215).length < 2 ^ (prefixWord ++ tailWord_241215).sum := by decide
  have hdescent : baseEnd_241215 < baseStart_241215 := by decide
  rcases family_descends (prefixWord ++ tailWord_241215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241238 : List Nat := [5, 2, 2, 2, 1, 1, 3, 2, 2]
def baseStart_241238 : Nat := 118140960795 + 241238 * 2 ^ 59
def prefixEnd_241238 : Nat := 4983230072969 + 3 ^ 40 * 241238 * 2
def baseEnd_241238 : Nat := 110107596559495456813843

theorem tailTrace_241238 : CollatzResearch.WordTrace tailWord_241238 prefixEnd_241238 110107596559495456813843 := by
  unfold tailWord_241238
  simp only [CollatzResearch.WordTrace]
  refine ⟨549917043752712563462273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5865781800028934010264245 549917043752712563462273)
  ·
    refine ⟨412437782814534422596705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 549917043752712563462273 412437782814534422596705)
    ·
      refine ⟨309328337110900816947529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412437782814534422596705 309328337110900816947529)
      ·
        refine ⟨231996252833175612710647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309328337110900816947529 231996252833175612710647)
        ·
          refine ⟨347994379249763419065971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231996252833175612710647 347994379249763419065971)
          ·
            refine ⟨521991568874645128598957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347994379249763419065971 521991568874645128598957)
            ·
              refine ⟨195746838327991923224609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 521991568874645128598957 195746838327991923224609)
              ·
                refine ⟨146810128745993942418457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195746838327991923224609 146810128745993942418457)
                ·
                  refine ⟨110107596559495456813843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146810128745993942418457 110107596559495456813843)
                  ·
                    rfl

theorem cell20_241238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_241238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241238 prefixEnd_241238 := by exact prefixLift 241238
  have htrace : WordTrace (prefixWord ++ tailWord_241238) baseStart_241238 baseEnd_241238 := by
    simpa [prefixWord, tailWord_241238, baseEnd_241238] using wordTrace_append hprefix tailTrace_241238
  have hstable : (prefixWord ++ tailWord_241238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241238).length < 2 ^ (prefixWord ++ tailWord_241238).sum := by decide
  have hdescent : baseEnd_241238 < baseStart_241238 := by decide
  rcases family_descends (prefixWord ++ tailWord_241238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241256 : List Nat := [2, 1, 4, 3, 1, 3, 2, 1, 3]
def baseStart_241256 : Nat := 118140960795 + 241256 * 2 ^ 59
def prefixEnd_241256 : Nat := 4983230072969 + 3 ^ 40 * 241256 * 2
def baseEnd_241256 : Nat := 110115812249967394213769

theorem tailTrace_241256 : CollatzResearch.WordTrace tailWord_241256 prefixEnd_241256 110115812249967394213769 := by
  unfold tailWord_241256
  simp only [CollatzResearch.WordTrace]
  refine ⟨4399664606989095044775811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5866219475985460059701081 4399664606989095044775811)
  ·
    refine ⟨6599496910483642567163717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4399664606989095044775811 6599496910483642567163717)
    ·
      refine ⟨1237405670715682981343197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6599496910483642567163717 1237405670715682981343197)
      ·
        refine ⟨464027126518381118003699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1237405670715682981343197 464027126518381118003699)
        ·
          refine ⟨696040689777571677005549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464027126518381118003699 696040689777571677005549)
          ·
            refine ⟨261015258666589378877081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 696040689777571677005549 261015258666589378877081)
            ·
              refine ⟨195761443999942034157811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261015258666589378877081 195761443999942034157811)
              ·
                refine ⟨293642165999913051236717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195761443999942034157811 293642165999913051236717)
                ·
                  refine ⟨110115812249967394213769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 293642165999913051236717 110115812249967394213769)
                  ·
                    rfl

theorem cell20_241256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 1, 3].length) (baseStart_241256 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241256 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241256 prefixEnd_241256 := by exact prefixLift 241256
  have htrace : WordTrace (prefixWord ++ tailWord_241256) baseStart_241256 baseEnd_241256 := by
    simpa [prefixWord, tailWord_241256, baseEnd_241256] using wordTrace_append hprefix tailTrace_241256
  have hstable : (prefixWord ++ tailWord_241256).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241256).length < 2 ^ (prefixWord ++ tailWord_241256).sum := by decide
  have hdescent : baseEnd_241256 < baseStart_241256 := by decide
  rcases family_descends (prefixWord ++ tailWord_241256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241257 : List Nat := [1, 2, 1, 1, 1, 4, 3, 7]
def baseStart_241257 : Nat := 118140960795 + 241257 * 2 ^ 59
def prefixEnd_241257 : Nat := 4983230072969 + 3 ^ 40 * 241257 * 2
def baseEnd_241257 : Nat := 36705422892405278393477

theorem tailTrace_241257 : CollatzResearch.WordTrace tailWord_241257 prefixEnd_241257 36705422892405278393477 := by
  unfold tailWord_241257
  simp only [CollatzResearch.WordTrace]
  refine ⟨8799365686974567260338025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5866243791316378173558683 8799365686974567260338025)
  ·
    refine ⟨6599524265230925445253519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8799365686974567260338025 6599524265230925445253519)
    ·
      refine ⟨9899286397846388167880279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6599524265230925445253519 9899286397846388167880279)
      ·
        refine ⟨14848929596769582251820419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9899286397846388167880279 14848929596769582251820419)
        ·
          refine ⟨22273394395154373377730629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14848929596769582251820419 22273394395154373377730629)
          ·
            refine ⟨4176261449091445008324493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22273394395154373377730629 4176261449091445008324493)
            ·
              refine ⟨1566098043409291878121685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4176261449091445008324493 1566098043409291878121685)
              ·
                refine ⟨36705422892405278393477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1566098043409291878121685 36705422892405278393477)
                ·
                  rfl

theorem cell20_241257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 7].length) (baseStart_241257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241257 prefixEnd_241257 := by exact prefixLift 241257
  have htrace : WordTrace (prefixWord ++ tailWord_241257) baseStart_241257 baseEnd_241257 := by
    simpa [prefixWord, tailWord_241257, baseEnd_241257] using wordTrace_append hprefix tailTrace_241257
  have hstable : (prefixWord ++ tailWord_241257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241257).length < 2 ^ (prefixWord ++ tailWord_241257).sum := by decide
  have hdescent : baseEnd_241257 < baseStart_241257 := by decide
  rcases family_descends (prefixWord ++ tailWord_241257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241308 : List Nat := [2, 2, 3, 2, 4, 1, 1, 5]
def baseStart_241308 : Nat := 118140960795 + 241308 * 2 ^ 59
def prefixEnd_241308 : Nat := 4983230072969 + 3 ^ 40 * 241308 * 2
def baseEnd_241308 : Nat := 36713182155628774826741

theorem tailTrace_241308 : CollatzResearch.WordTrace tailWord_241308 prefixEnd_241308 36713182155628774826741 := by
  unfold tailWord_241308
  simp only [CollatzResearch.WordTrace]
  refine ⟨4400612904894901485222289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5867483873193201980296385 4400612904894901485222289)
  ·
    refine ⟨3300459678671176113916717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4400612904894901485222289 3300459678671176113916717)
    ·
      refine ⟨1237672379501691042718769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3300459678671176113916717 1237672379501691042718769)
      ·
        refine ⟨928254284626268282039077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1237672379501691042718769 928254284626268282039077)
        ·
          refine ⟨174047678367425302882327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 928254284626268282039077 174047678367425302882327)
          ·
            refine ⟨261071517551137954323491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174047678367425302882327 261071517551137954323491)
            ·
              refine ⟨391607276326706931485237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261071517551137954323491 391607276326706931485237)
              ·
                refine ⟨36713182155628774826741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 391607276326706931485237 36713182155628774826741)
                ·
                  rfl

theorem cell20_241308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 5].length) (baseStart_241308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241308 prefixEnd_241308 := by exact prefixLift 241308
  have htrace : WordTrace (prefixWord ++ tailWord_241308) baseStart_241308 baseEnd_241308 := by
    simpa [prefixWord, tailWord_241308, baseEnd_241308] using wordTrace_append hprefix tailTrace_241308
  have hstable : (prefixWord ++ tailWord_241308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241308).length < 2 ^ (prefixWord ++ tailWord_241308).sum := by decide
  have hdescent : baseEnd_241308 < baseStart_241308 := by decide
  rcases family_descends (prefixWord ++ tailWord_241308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241312 : List Nat := [2, 1, 1, 4, 3, 1, 3, 5]
def baseStart_241312 : Nat := 118140960795 + 241312 * 2 ^ 59
def prefixEnd_241312 : Nat := 4983230072969 + 3 ^ 40 * 241312 * 2
def baseEnd_241312 : Nat := 36713790725293362782291

theorem tailTrace_241312 : CollatzResearch.WordTrace tailWord_241312 prefixEnd_241312 36713790725293362782291 := by
  unfold tailWord_241312
  simp only [CollatzResearch.WordTrace]
  refine ⟨4400685850887655826795095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5867581134516874435726793 4400685850887655826795095)
  ·
    refine ⟨6601028776331483740192643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4400685850887655826795095 6601028776331483740192643)
    ·
      refine ⟨9901543164497225610288965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6601028776331483740192643 9901543164497225610288965)
      ·
        refine ⟨1856539343343229801929181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9901543164497225610288965 1856539343343229801929181)
        ·
          refine ⟨696202253753711175723443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1856539343343229801929181 696202253753711175723443)
          ·
            refine ⟨1044303380630566763585165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 696202253753711175723443 1044303380630566763585165)
            ·
              refine ⟨391613767736462536344437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1044303380630566763585165 391613767736462536344437)
              ·
                refine ⟨36713790725293362782291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 391613767736462536344437 36713790725293362782291)
                ·
                  rfl

theorem cell20_241312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 5].length) (baseStart_241312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241312 prefixEnd_241312 := by exact prefixLift 241312
  have htrace : WordTrace (prefixWord ++ tailWord_241312) baseStart_241312 baseEnd_241312 := by
    simpa [prefixWord, tailWord_241312, baseEnd_241312] using wordTrace_append hprefix tailTrace_241312
  have hstable : (prefixWord ++ tailWord_241312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241312).length < 2 ^ (prefixWord ++ tailWord_241312).sum := by decide
  have hdescent : baseEnd_241312 < baseStart_241312 := by decide
  rcases family_descends (prefixWord ++ tailWord_241312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241388 : List Nat := [2, 2, 1, 1, 2, 2, 6, 4]
def baseStart_241388 : Nat := 118140960795 + 241388 * 2 ^ 59
def prefixEnd_241388 : Nat := 4983230072969 + 3 ^ 40 * 241388 * 2
def baseEnd_241388 : Nat := 36725353548920533937743

theorem tailTrace_241388 : CollatzResearch.WordTrace tailWord_241388 prefixEnd_241388 36725353548920533937743 := by
  unfold tailWord_241388
  simp only [CollatzResearch.WordTrace]
  refine ⟨4402071824749988316678409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5869429099666651088904545 4402071824749988316678409)
  ·
    refine ⟨3301553868562491237508807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4402071824749988316678409 3301553868562491237508807)
    ·
      refine ⟨4952330802843736856263211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3301553868562491237508807 4952330802843736856263211)
      ·
        refine ⟨7428496204265605284394817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4952330802843736856263211 7428496204265605284394817)
        ·
          refine ⟨5571372153199203963296113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7428496204265605284394817 5571372153199203963296113)
          ·
            refine ⟨4178529114899402972472085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5571372153199203963296113 4178529114899402972472085)
            ·
              refine ⟨195868552260909514334629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4178529114899402972472085 195868552260909514334629)
              ·
                refine ⟨36725353548920533937743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195868552260909514334629 36725353548920533937743)
                ·
                  rfl

theorem cell20_241388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 4].length) (baseStart_241388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241388 prefixEnd_241388 := by exact prefixLift 241388
  have htrace : WordTrace (prefixWord ++ tailWord_241388) baseStart_241388 baseEnd_241388 := by
    simpa [prefixWord, tailWord_241388, baseEnd_241388] using wordTrace_append hprefix tailTrace_241388
  have hstable : (prefixWord ++ tailWord_241388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241388).length < 2 ^ (prefixWord ++ tailWord_241388).sum := by decide
  have hdescent : baseEnd_241388 < baseStart_241388 := by decide
  rcases family_descends (prefixWord ++ tailWord_241388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241409 : List Nat := [1, 2, 4, 1, 1, 1, 10]
def baseStart_241409 : Nat := 118140960795 + 241409 * 2 ^ 59
def prefixEnd_241409 : Nat := 4983230072969 + 3 ^ 40 * 241409 * 2
def baseEnd_241409 : Nat := 12242849513219873568127

theorem tailTrace_241409 : CollatzResearch.WordTrace tailWord_241409 prefixEnd_241409 12242849513219873568127 := by
  unfold tailWord_241409
  simp only [CollatzResearch.WordTrace]
  refine ⟨8804909582423897219871281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5869939721615931479914187 8804909582423897219871281)
  ·
    refine ⟨6603682186817922914903461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8804909582423897219871281 6603682186817922914903461)
    ·
      refine ⟨1238190410028360546544399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6603682186817922914903461 1238190410028360546544399)
      ·
        refine ⟨1857285615042540819816599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1238190410028360546544399 1857285615042540819816599)
        ·
          refine ⟨2785928422563811229724899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1857285615042540819816599 2785928422563811229724899)
          ·
            refine ⟨4178892633845716844587349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2785928422563811229724899 4178892633845716844587349)
            ·
              refine ⟨12242849513219873568127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4178892633845716844587349 12242849513219873568127)
              ·
                rfl

theorem cell20_241409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 10].length) (baseStart_241409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241409 prefixEnd_241409 := by exact prefixLift 241409
  have htrace : WordTrace (prefixWord ++ tailWord_241409) baseStart_241409 baseEnd_241409 := by
    simpa [prefixWord, tailWord_241409, baseEnd_241409] using wordTrace_append hprefix tailTrace_241409
  have hstable : (prefixWord ++ tailWord_241409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241409).length < 2 ^ (prefixWord ++ tailWord_241409).sum := by decide
  have hdescent : baseEnd_241409 < baseStart_241409 := by decide
  rcases family_descends (prefixWord ++ tailWord_241409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241415 : List Nat := [1, 1, 4, 4, 3, 1, 1, 1, 4]
def baseStart_241415 : Nat := 118140960795 + 241415 * 2 ^ 59
def prefixEnd_241415 : Nat := 4983230072969 + 3 ^ 40 * 241415 * 2
def baseEnd_241415 : Nat := 110188384182469507913119

theorem tailTrace_241415 : CollatzResearch.WordTrace tailWord_241415 prefixEnd_241415 110188384182469507913119 := by
  unfold tailWord_241415
  simp only [CollatzResearch.WordTrace]
  refine ⟨8805128420402160244589699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5870085613601440163059799 8805128420402160244589699)
  ·
    refine ⟨13207692630603240366884549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8805128420402160244589699 13207692630603240366884549)
    ·
      refine ⟨2476442368238107568790853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13207692630603240366884549 2476442368238107568790853)
      ·
        refine ⟨464332944044645169148285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2476442368238107568790853 464332944044645169148285)
        ·
          refine ⟨174124854016741938430607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 464332944044645169148285 174124854016741938430607)
          ·
            refine ⟨261187281025112907645911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174124854016741938430607 261187281025112907645911)
            ·
              refine ⟨391780921537669361468867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261187281025112907645911 391780921537669361468867)
              ·
                refine ⟨587671382306504042203301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 391780921537669361468867 587671382306504042203301)
                ·
                  refine ⟨110188384182469507913119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 587671382306504042203301 110188384182469507913119)
                  ·
                    rfl

theorem cell20_241415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 4].length) (baseStart_241415 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241415 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241415 prefixEnd_241415 := by exact prefixLift 241415
  have htrace : WordTrace (prefixWord ++ tailWord_241415) baseStart_241415 baseEnd_241415 := by
    simpa [prefixWord, tailWord_241415, baseEnd_241415] using wordTrace_append hprefix tailTrace_241415
  have hstable : (prefixWord ++ tailWord_241415).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241415).length < 2 ^ (prefixWord ++ tailWord_241415).sum := by decide
  have hdescent : baseEnd_241415 < baseStart_241415 := by decide
  rcases family_descends (prefixWord ++ tailWord_241415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241419 : List Nat := [1, 1, 1, 1, 5, 1, 2, 6, 2]
def baseStart_241419 : Nat := 118140960795 + 241419 * 2 ^ 59
def prefixEnd_241419 : Nat := 4983230072969 + 3 ^ 40 * 241419 * 2
def baseEnd_241419 : Nat := 110190209891463271779769

theorem tailTrace_241419 : CollatzResearch.WordTrace tailWord_241419 prefixEnd_241419 110190209891463271779769 := by
  unfold tailWord_241419
  simp only [CollatzResearch.WordTrace]
  refine ⟨8805274312387668927735311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5870182874925112618490207 8805274312387668927735311)
  ·
    refine ⟨13207911468581503391602967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8805274312387668927735311 13207911468581503391602967)
    ·
      refine ⟨19811867202872255087404451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13207911468581503391602967 19811867202872255087404451)
      ·
        refine ⟨29717800804308382631106677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19811867202872255087404451 29717800804308382631106677)
        ·
          refine ⟨2786043825403910871666251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29717800804308382631106677 2786043825403910871666251)
          ·
            refine ⟨4179065738105866307499377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2786043825403910871666251 4179065738105866307499377)
            ·
              refine ⟨3134299303579399730624533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4179065738105866307499377 3134299303579399730624533)
              ·
                refine ⟨146920279855284362373025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3134299303579399730624533 146920279855284362373025)
                ·
                  refine ⟨110190209891463271779769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146920279855284362373025 110190209891463271779769)
                  ·
                    rfl

theorem cell20_241419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 6, 2].length) (baseStart_241419 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241419 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241419 prefixEnd_241419 := by exact prefixLift 241419
  have htrace : WordTrace (prefixWord ++ tailWord_241419) baseStart_241419 baseEnd_241419 := by
    simpa [prefixWord, tailWord_241419, baseEnd_241419] using wordTrace_append hprefix tailTrace_241419
  have hstable : (prefixWord ++ tailWord_241419).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241419).length < 2 ^ (prefixWord ++ tailWord_241419).sum := by decide
  have hdescent : baseEnd_241419 < baseStart_241419 := by decide
  rcases family_descends (prefixWord ++ tailWord_241419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241421 : List Nat := [1, 7, 2, 1, 1, 2, 2, 1, 3]
def baseStart_241421 : Nat := 118140960795 + 241421 * 2 ^ 59
def prefixEnd_241421 : Nat := 4983230072969 + 3 ^ 40 * 241421 * 2
def baseEnd_241421 : Nat := 110191122745960153713095

theorem tailTrace_241421 : CollatzResearch.WordTrace tailWord_241421 prefixEnd_241421 110191122745960153713095 := by
  unfold tailWord_241421
  simp only [CollatzResearch.WordTrace]
  refine ⟨8805347258380423269308117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5870231505586948846205411 8805347258380423269308117)
  ·
    refine ⟨206375326368291170374409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 8805347258380423269308117 206375326368291170374409)
    ·
      refine ⟨154781494776218377780807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206375326368291170374409 154781494776218377780807)
      ·
        refine ⟨232172242164327566671211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154781494776218377780807 232172242164327566671211)
        ·
          refine ⟨348258363246491350006817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232172242164327566671211 348258363246491350006817)
          ·
            refine ⟨261193772434868512505113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348258363246491350006817 261193772434868512505113)
            ·
              refine ⟨195895329326151384378835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261193772434868512505113 195895329326151384378835)
              ·
                refine ⟨293842993989227076568253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195895329326151384378835 293842993989227076568253)
                ·
                  refine ⟨110191122745960153713095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 293842993989227076568253 110191122745960153713095)
                  ·
                    rfl

theorem cell20_241421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_241421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241421 prefixEnd_241421 := by exact prefixLift 241421
  have htrace : WordTrace (prefixWord ++ tailWord_241421) baseStart_241421 baseEnd_241421 := by
    simpa [prefixWord, tailWord_241421, baseEnd_241421] using wordTrace_append hprefix tailTrace_241421
  have hstable : (prefixWord ++ tailWord_241421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241421).length < 2 ^ (prefixWord ++ tailWord_241421).sum := by decide
  have hdescent : baseEnd_241421 < baseStart_241421 := by decide
  rcases family_descends (prefixWord ++ tailWord_241421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241429 : List Nat := [1, 3, 2, 1, 2, 5, 2, 1, 3]
def baseStart_241429 : Nat := 118140960795 + 241429 * 2 ^ 59
def prefixEnd_241429 : Nat := 4983230072969 + 3 ^ 40 * 241429 * 2
def baseEnd_241429 : Nat := 110194774163947681446395

theorem tailTrace_241429 : CollatzResearch.WordTrace tailWord_241429 prefixEnd_241429 110194774163947681446395 := by
  unfold tailWord_241429
  simp only [CollatzResearch.WordTrace]
  refine ⟨8805639042351440635599341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5870426028234293757066227 8805639042351440635599341)
  ·
    refine ⟨3302114640881790238349753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8805639042351440635599341 3302114640881790238349753)
    ·
      refine ⟨2476585980661342678762315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3302114640881790238349753 2476585980661342678762315)
      ·
        refine ⟨3714878970992014018143473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2476585980661342678762315 3714878970992014018143473)
        ·
          refine ⟨2786159228244010513607605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3714878970992014018143473 2786159228244010513607605)
          ·
            refine ⟨261202427647875985650713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2786159228244010513607605 261202427647875985650713)
            ·
              refine ⟨195901820735906989238035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261202427647875985650713 195901820735906989238035)
              ·
                refine ⟨293852731103860483857053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195901820735906989238035 293852731103860483857053)
                ·
                  refine ⟨110194774163947681446395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 293852731103860483857053 110194774163947681446395)
                  ·
                    rfl

theorem cell20_241429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 1, 3].length) (baseStart_241429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241429 prefixEnd_241429 := by exact prefixLift 241429
  have htrace : WordTrace (prefixWord ++ tailWord_241429) baseStart_241429 baseEnd_241429 := by
    simpa [prefixWord, tailWord_241429, baseEnd_241429] using wordTrace_append hprefix tailTrace_241429
  have hstable : (prefixWord ++ tailWord_241429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241429).length < 2 ^ (prefixWord ++ tailWord_241429).sum := by decide
  have hdescent : baseEnd_241429 < baseStart_241429 := by decide
  rcases family_descends (prefixWord ++ tailWord_241429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241440 : List Nat := [2, 1, 1, 5, 1, 1, 2, 1, 6]
def baseStart_241440 : Nat := 118140960795 + 241440 * 2 ^ 59
def prefixEnd_241440 : Nat := 4983230072969 + 3 ^ 40 * 241440 * 2
def baseEnd_241440 : Nat := 110199794863680532079683

theorem tailTrace_241440 : CollatzResearch.WordTrace tailWord_241440 prefixEnd_241440 110199794863680532079683 := by
  unfold tailWord_241440
  simp only [CollatzResearch.WordTrace]
  refine ⟨4403020122655794757124887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5870693496874393009499849 4403020122655794757124887)
  ·
    refine ⟨6604530183983692135687331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4403020122655794757124887 6604530183983692135687331)
    ·
      refine ⟨9906795275975538203530997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6604530183983692135687331 9906795275975538203530997)
      ·
        refine ⟨928762057122706706581031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9906795275975538203530997 928762057122706706581031)
        ·
          refine ⟨1393143085684060059871547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 928762057122706706581031 1393143085684060059871547)
          ·
            refine ⟨2089714628526090089807321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1393143085684060059871547 2089714628526090089807321)
            ·
              refine ⟨1567285971394567567355491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2089714628526090089807321 1567285971394567567355491)
              ·
                refine ⟨2350928957091851351033237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1567285971394567567355491 2350928957091851351033237)
                ·
                  refine ⟨110199794863680532079683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2350928957091851351033237 110199794863680532079683)
                  ·
                    rfl

theorem cell20_241440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 6].length) (baseStart_241440 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241440 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241440 prefixEnd_241440 := by exact prefixLift 241440
  have htrace : WordTrace (prefixWord ++ tailWord_241440) baseStart_241440 baseEnd_241440 := by
    simpa [prefixWord, tailWord_241440, baseEnd_241440] using wordTrace_append hprefix tailTrace_241440
  have hstable : (prefixWord ++ tailWord_241440).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241440).length < 2 ^ (prefixWord ++ tailWord_241440).sum := by decide
  have hdescent : baseEnd_241440 < baseStart_241440 := by decide
  rcases family_descends (prefixWord ++ tailWord_241440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241470 : List Nat := [4, 2, 1, 2, 2, 3, 2, 2, 2]
def baseStart_241470 : Nat := 118140960795 + 241470 * 2 ^ 59
def prefixEnd_241470 : Nat := 4983230072969 + 3 ^ 40 * 241470 * 2
def baseEnd_241470 : Nat := 110213487681133761079561

theorem tailTrace_241470 : CollatzResearch.WordTrace tailWord_241470 prefixEnd_241470 110213487681133761079561 := by
  unfold tailWord_241470
  simp only [CollatzResearch.WordTrace]
  refine ⟨1100891804400363079730233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5871422956801936425227909 1100891804400363079730233)
  ·
    refine ⟨825668853300272309797675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1100891804400363079730233 825668853300272309797675)
    ·
      refine ⟨1238503279950408464696513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 825668853300272309797675 1238503279950408464696513)
      ·
        refine ⟨928877459962806348522385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1238503279950408464696513 928877459962806348522385)
        ·
          refine ⟨696658094972104761391789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 928877459962806348522385 696658094972104761391789)
          ·
            refine ⟨261246785614539285521921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 696658094972104761391789 261246785614539285521921)
            ·
              refine ⟨195935089210904464141441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261246785614539285521921 195935089210904464141441)
              ·
                refine ⟨146951316908178348106081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195935089210904464141441 146951316908178348106081)
                ·
                  refine ⟨110213487681133761079561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146951316908178348106081 110213487681133761079561)
                  ·
                    rfl

theorem cell20_241470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_241470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241470 prefixEnd_241470 := by exact prefixLift 241470
  have htrace : WordTrace (prefixWord ++ tailWord_241470) baseStart_241470 baseEnd_241470 := by
    simpa [prefixWord, tailWord_241470, baseEnd_241470] using wordTrace_append hprefix tailTrace_241470
  have hstable : (prefixWord ++ tailWord_241470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241470).length < 2 ^ (prefixWord ++ tailWord_241470).sum := by decide
  have hdescent : baseEnd_241470 < baseStart_241470 := by decide
  rcases family_descends (prefixWord ++ tailWord_241470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241495 : List Nat := [1, 1, 3, 2, 5, 1, 1, 2, 4]
def baseStart_241495 : Nat := 118140960795 + 241495 * 2 ^ 59
def prefixEnd_241495 : Nat := 4983230072969 + 3 ^ 40 * 241495 * 2
def baseEnd_241495 : Nat := 110224898362344785246125

theorem tailTrace_241495 : CollatzResearch.WordTrace tailWord_241495 prefixEnd_241495 110224898362344785246125 := by
  unfold tailWord_241495
  simp only [CollatzResearch.WordTrace]
  refine ⟨8808046260112333907501939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5872030840074889271667959 8808046260112333907501939)
  ·
    refine ⟨13212069390168500861252909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8808046260112333907501939 13212069390168500861252909)
    ·
      refine ⟨4954526021313187822969841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13212069390168500861252909 4954526021313187822969841)
      ·
        refine ⟨3715894515984890867227381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4954526021313187822969841 3715894515984890867227381)
        ·
          refine ⟨348365110873583518802567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3715894515984890867227381 348365110873583518802567)
          ·
            refine ⟨522547666310375278203851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348365110873583518802567 522547666310375278203851)
            ·
              refine ⟨783821499465562917305777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 522547666310375278203851 783821499465562917305777)
              ·
                refine ⟨587866124599172187979333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 783821499465562917305777 587866124599172187979333)
                ·
                  refine ⟨110224898362344785246125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 587866124599172187979333 110224898362344785246125)
                  ·
                    rfl

theorem cell20_241495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 4].length) (baseStart_241495 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241495 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241495 prefixEnd_241495 := by exact prefixLift 241495
  have htrace : WordTrace (prefixWord ++ tailWord_241495) baseStart_241495 baseEnd_241495 := by
    simpa [prefixWord, tailWord_241495, baseEnd_241495] using wordTrace_append hprefix tailTrace_241495
  have hstable : (prefixWord ++ tailWord_241495).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241495).length < 2 ^ (prefixWord ++ tailWord_241495).sum := by decide
  have hdescent : baseEnd_241495 < baseStart_241495 := by decide
  rcases family_descends (prefixWord ++ tailWord_241495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241512 : List Nat := [2, 1, 4, 2, 1, 1, 4, 3, 2]
def baseStart_241512 : Nat := 118140960795 + 241512 * 2 ^ 59
def prefixEnd_241512 : Nat := 4983230072969 + 3 ^ 40 * 241512 * 2
def baseEnd_241512 : Nat := 110232657625568281679389

theorem tailTrace_241512 : CollatzResearch.WordTrace tailWord_241512 prefixEnd_241512 110232657625568281679389 := by
  unfold tailWord_241512
  simp only [CollatzResearch.WordTrace]
  refine ⟨4404333150525372905435395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5872444200700497207247193 4404333150525372905435395)
  ·
    refine ⟨6606499725788059358153093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4404333150525372905435395 6606499725788059358153093)
    ·
      refine ⟨1238718698585261129653705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6606499725788059358153093 1238718698585261129653705)
      ·
        refine ⟨929039023938945847240279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1238718698585261129653705 929039023938945847240279)
        ·
          refine ⟨1393558535908418770860419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 929039023938945847240279 1393558535908418770860419)
          ·
            refine ⟨2090337803862628156290629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1393558535908418770860419 2090337803862628156290629)
            ·
              refine ⟨391938338224242779304493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2090337803862628156290629 391938338224242779304493)
              ·
                refine ⟨146976876834091042239185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 391938338224242779304493 146976876834091042239185)
                ·
                  refine ⟨110232657625568281679389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146976876834091042239185 110232657625568281679389)
                  ·
                    rfl

theorem cell20_241512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 3, 2].length) (baseStart_241512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241512 prefixEnd_241512 := by exact prefixLift 241512
  have htrace : WordTrace (prefixWord ++ tailWord_241512) baseStart_241512 baseEnd_241512 := by
    simpa [prefixWord, tailWord_241512, baseEnd_241512] using wordTrace_append hprefix tailTrace_241512
  have hstable : (prefixWord ++ tailWord_241512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241512).length < 2 ^ (prefixWord ++ tailWord_241512).sum := by decide
  have hdescent : baseEnd_241512 < baseStart_241512 := by decide
  rcases family_descends (prefixWord ++ tailWord_241512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241543 : List Nat := [1, 1, 4, 2, 4, 1, 3, 1, 3]
def baseStart_241543 : Nat := 118140960795 + 241543 * 2 ^ 59
def prefixEnd_241543 : Nat := 4983230072969 + 3 ^ 40 * 241543 * 2
def baseEnd_241543 : Nat := 110246806870269951645929

theorem tailTrace_241543 : CollatzResearch.WordTrace tailWord_241543 prefixEnd_241543 110246806870269951645929 := by
  unfold tailWord_241543
  simp only [CollatzResearch.WordTrace]
  refine ⟨8809796963938438105249283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5873197975958958736832855 8809796963938438105249283)
  ·
    refine ⟨13214695445907657157873925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8809796963938438105249283 13214695445907657157873925)
    ·
      refine ⟨2477755396107685717101361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13214695445907657157873925 2477755396107685717101361)
      ·
        refine ⟨1858316547080764287826021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2477755396107685717101361 1858316547080764287826021)
        ·
          refine ⟨348434352577643303967379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1858316547080764287826021 348434352577643303967379)
          ·
            refine ⟨522651528866464955951069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348434352577643303967379 522651528866464955951069)
            ·
              refine ⟨195994323324924358481651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 522651528866464955951069 195994323324924358481651)
              ·
                refine ⟨293991484987386537722477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195994323324924358481651 293991484987386537722477)
                ·
                  refine ⟨110246806870269951645929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 293991484987386537722477 110246806870269951645929)
                  ·
                    rfl

theorem cell20_241543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 1, 3].length) (baseStart_241543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241543 prefixEnd_241543 := by exact prefixLift 241543
  have htrace : WordTrace (prefixWord ++ tailWord_241543) baseStart_241543 baseEnd_241543 := by
    simpa [prefixWord, tailWord_241543, baseEnd_241543] using wordTrace_append hprefix tailTrace_241543
  have hstable : (prefixWord ++ tailWord_241543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241543).length < 2 ^ (prefixWord ++ tailWord_241543).sum := by decide
  have hdescent : baseEnd_241543 < baseStart_241543 := by decide
  rcases family_descends (prefixWord ++ tailWord_241543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241567 : List Nat := [1, 1, 2, 5, 3, 2, 1, 3, 2]
def baseStart_241567 : Nat := 118140960795 + 241567 * 2 ^ 59
def prefixEnd_241567 : Nat := 4983230072969 + 3 ^ 40 * 241567 * 2
def baseEnd_241567 : Nat := 110257761124232534845831

theorem tailTrace_241567 : CollatzResearch.WordTrace tailWord_241567 prefixEnd_241567 110257761124232534845831 := by
  unfold tailWord_241567
  simp only [CollatzResearch.WordTrace]
  refine ⟨8810672315851490204122955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5873781543900993469415303 8810672315851490204122955)
  ·
    refine ⟨13216008473777235306184433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8810672315851490204122955 13216008473777235306184433)
    ·
      refine ⟨9912006355332926479638325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13216008473777235306184433 9912006355332926479638325)
      ·
        refine ⟨929250595812461857466093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9912006355332926479638325 929250595812461857466093)
        ·
          refine ⟨348468973429673196549785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 929250595812461857466093 348468973429673196549785)
          ·
            refine ⟨261351730072254897412339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348468973429673196549785 261351730072254897412339)
            ·
              refine ⟨392027595108382346118509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261351730072254897412339 392027595108382346118509)
              ·
                refine ⟨147010348165643379794441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 392027595108382346118509 147010348165643379794441)
                ·
                  refine ⟨110257761124232534845831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147010348165643379794441 110257761124232534845831)
                  ·
                    rfl

theorem cell20_241567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 3, 2].length) (baseStart_241567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241567 prefixEnd_241567 := by exact prefixLift 241567
  have htrace : WordTrace (prefixWord ++ tailWord_241567) baseStart_241567 baseEnd_241567 := by
    simpa [prefixWord, tailWord_241567, baseEnd_241567] using wordTrace_append hprefix tailTrace_241567
  have hstable : (prefixWord ++ tailWord_241567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241567).length < 2 ^ (prefixWord ++ tailWord_241567).sum := by decide
  have hdescent : baseEnd_241567 < baseStart_241567 := by decide
  rcases family_descends (prefixWord ++ tailWord_241567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241585 : List Nat := [1, 2, 2, 4, 2, 1, 2, 1, 5]
def baseStart_241585 : Nat := 118140960795 + 241585 * 2 ^ 59
def prefixEnd_241585 : Nat := 4983230072969 + 3 ^ 40 * 241585 * 2
def baseEnd_241585 : Nat := 110265976814704472245757

theorem tailTrace_241585 : CollatzResearch.WordTrace tailWord_241585 prefixEnd_241585 110265976814704472245757 := by
  unfold tailWord_241585
  simp only [CollatzResearch.WordTrace]
  refine ⟨8811328829786279278278209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5874219219857519518852139 8811328829786279278278209)
  ·
    refine ⟨6608496622339709458708657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8811328829786279278278209 6608496622339709458708657)
    ·
      refine ⟨4956372466754782094031493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6608496622339709458708657 4956372466754782094031493)
      ·
        refine ⟨929319837516521642630905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4956372466754782094031493 929319837516521642630905)
        ·
          refine ⟨696989878137391231973179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 929319837516521642630905 696989878137391231973179)
          ·
            refine ⟨1045484817206086847959769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 696989878137391231973179 1045484817206086847959769)
            ·
              refine ⟨784113612904565135969827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1045484817206086847959769 784113612904565135969827)
              ·
                refine ⟨1176170419356847703954741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 784113612904565135969827 1176170419356847703954741)
                ·
                  refine ⟨110265976814704472245757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1176170419356847703954741 110265976814704472245757)
                  ·
                    rfl

theorem cell20_241585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 5].length) (baseStart_241585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241585 prefixEnd_241585 := by exact prefixLift 241585
  have htrace : WordTrace (prefixWord ++ tailWord_241585) baseStart_241585 baseEnd_241585 := by
    simpa [prefixWord, tailWord_241585, baseEnd_241585] using wordTrace_append hprefix tailTrace_241585
  have hstable : (prefixWord ++ tailWord_241585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241585).length < 2 ^ (prefixWord ++ tailWord_241585).sum := by decide
  have hdescent : baseEnd_241585 < baseStart_241585 := by decide
  rcases family_descends (prefixWord ++ tailWord_241585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241599 : List Nat := [1, 1, 2, 2, 2, 1, 6, 5]
def baseStart_241599 : Nat := 118140960795 + 241599 * 2 ^ 59
def prefixEnd_241599 : Nat := 4983230072969 + 3 ^ 40 * 241599 * 2
def baseEnd_241599 : Nat := 36757455598727548593011

theorem tailTrace_241599 : CollatzResearch.WordTrace tailWord_241599 prefixEnd_241599 36757455598727548593011 := by
  unfold tailWord_241599
  simp only [CollatzResearch.WordTrace]
  refine ⟨8811839451735559669287851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5874559634490373112858567 8811839451735559669287851)
  ·
    refine ⟨13217759177603339503931777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8811839451735559669287851 13217759177603339503931777)
    ·
      refine ⟨9913319383202504627948833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13217759177603339503931777 9913319383202504627948833)
      ·
        refine ⟨7434989537401878470961625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9913319383202504627948833 7434989537401878470961625)
        ·
          refine ⟨5576242153051408853221219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7434989537401878470961625 5576242153051408853221219)
          ·
            refine ⟨8364363229577113279831829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5576242153051408853221219 8364363229577113279831829)
            ·
              refine ⟨392079526386427184992117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8364363229577113279831829 392079526386427184992117)
              ·
                refine ⟨36757455598727548593011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 392079526386427184992117 36757455598727548593011)
                ·
                  rfl

theorem cell20_241599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 5].length) (baseStart_241599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241599 prefixEnd_241599 := by exact prefixLift 241599
  have htrace : WordTrace (prefixWord ++ tailWord_241599) baseStart_241599 baseEnd_241599 := by
    simpa [prefixWord, tailWord_241599, baseEnd_241599] using wordTrace_append hprefix tailTrace_241599
  have hstable : (prefixWord ++ tailWord_241599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241599).length < 2 ^ (prefixWord ++ tailWord_241599).sum := by decide
  have hdescent : baseEnd_241599 < baseStart_241599 := by decide
  rcases family_descends (prefixWord ++ tailWord_241599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241644 : List Nat := [2, 2, 1, 1, 2, 1, 1, 5, 5]
def baseStart_241644 : Nat := 118140960795 + 241644 * 2 ^ 59
def prefixEnd_241644 : Nat := 4983230072969 + 3 ^ 40 * 241644 * 2
def baseEnd_241644 : Nat := 110292906022362489278849

theorem tailTrace_241644 : CollatzResearch.WordTrace tailWord_241644 prefixEnd_241644 110292906022362489278849 := by
  unfold tailWord_241644
  simp only [CollatzResearch.WordTrace]
  refine ⟨4406740368286266177337993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5875653824381688236450657 4406740368286266177337993)
  ·
    refine ⟨3305055276214699633003495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4406740368286266177337993 3305055276214699633003495)
    ·
      refine ⟨4957582914322049449505243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3305055276214699633003495 4957582914322049449505243)
      ·
        refine ⟨7436374371483074174257865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4957582914322049449505243 7436374371483074174257865)
        ·
          refine ⟨5577280778612305630693399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7436374371483074174257865 5577280778612305630693399)
          ·
            refine ⟨8365921167918458446040099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5577280778612305630693399 8365921167918458446040099)
            ·
              refine ⟨12548881751877687669060149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8365921167918458446040099 12548881751877687669060149)
              ·
                refine ⟨1176457664238533218974389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12548881751877687669060149 1176457664238533218974389)
                ·
                  refine ⟨110292906022362489278849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1176457664238533218974389 110292906022362489278849)
                  ·
                    rfl

theorem cell20_241644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_241644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241644 prefixEnd_241644 := by exact prefixLift 241644
  have htrace : WordTrace (prefixWord ++ tailWord_241644) baseStart_241644 baseEnd_241644 := by
    simpa [prefixWord, tailWord_241644, baseEnd_241644] using wordTrace_append hprefix tailTrace_241644
  have hstable : (prefixWord ++ tailWord_241644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241644).length < 2 ^ (prefixWord ++ tailWord_241644).sum := by decide
  have hdescent : baseEnd_241644 < baseStart_241644 := by decide
  rcases family_descends (prefixWord ++ tailWord_241644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241647 : List Nat := [1, 1, 2, 1, 4, 2, 3, 4, 2]
def baseStart_241647 : Nat := 118140960795 + 241647 * 2 ^ 59
def prefixEnd_241647 : Nat := 4983230072969 + 3 ^ 40 * 241647 * 2
def baseEnd_241647 : Nat := 110294275304107812178837

theorem tailTrace_241647 : CollatzResearch.WordTrace tailWord_241647 prefixEnd_241647 110294275304107812178837 := by
  unfold tailWord_241647
  simp only [CollatzResearch.WordTrace]
  refine ⟨8813590155561663867035195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5875726770374442578023463 8813590155561663867035195)
  ·
    refine ⟨13220385233342495800552793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8813590155561663867035195 13220385233342495800552793)
    ·
      refine ⟨9915288925006871850414595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13220385233342495800552793 9915288925006871850414595)
      ·
        refine ⟨14872933387510307775621893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9915288925006871850414595 14872933387510307775621893)
        ·
          refine ⟨2788675010158182707929105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14872933387510307775621893 2788675010158182707929105)
          ·
            refine ⟨2091506257618637030946829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2788675010158182707929105 2091506257618637030946829)
            ·
              refine ⟨784314846606988886605061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2091506257618637030946829 784314846606988886605061)
              ·
                refine ⟨147059033738810416238449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 784314846606988886605061 147059033738810416238449)
                ·
                  refine ⟨110294275304107812178837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147059033738810416238449 110294275304107812178837)
                  ·
                    rfl

theorem cell20_241647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 4, 2].length) (baseStart_241647 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241647 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241647 prefixEnd_241647 := by exact prefixLift 241647
  have htrace : WordTrace (prefixWord ++ tailWord_241647) baseStart_241647 baseEnd_241647 := by
    simpa [prefixWord, tailWord_241647, baseEnd_241647] using wordTrace_append hprefix tailTrace_241647
  have hstable : (prefixWord ++ tailWord_241647).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241647).length < 2 ^ (prefixWord ++ tailWord_241647).sum := by decide
  have hdescent : baseEnd_241647 < baseStart_241647 := by decide
  rcases family_descends (prefixWord ++ tailWord_241647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241651 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 8]
def baseStart_241651 : Nat := 118140960795 + 241651 * 2 ^ 59
def prefixEnd_241651 : Nat := 4983230072969 + 3 ^ 40 * 241651 * 2
def baseEnd_241651 : Nat := 110296101013101576045487

theorem tailTrace_241651 : CollatzResearch.WordTrace tailWord_241651 prefixEnd_241651 110296101013101576045487 := by
  unfold tailWord_241651
  simp only [CollatzResearch.WordTrace]
  refine ⟨8813736047547172550180807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5875824031698115033453871 8813736047547172550180807)
  ·
    refine ⟨13220604071320758825271211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8813736047547172550180807 13220604071320758825271211)
    ·
      refine ⟨19830906106981138237906817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13220604071320758825271211 19830906106981138237906817)
      ·
        refine ⟨14873179580235853678430113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19830906106981138237906817 14873179580235853678430113)
        ·
          refine ⟨11154884685176890258822585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14873179580235853678430113 11154884685176890258822585)
          ·
            refine ⟨8366163513882667694116939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11154884685176890258822585 8366163513882667694116939)
            ·
              refine ⟨12549245270824001541175409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8366163513882667694116939 12549245270824001541175409)
              ·
                refine ⟨9411933953118001155881557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12549245270824001541175409 9411933953118001155881557)
                ·
                  refine ⟨110296101013101576045487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9411933953118001155881557 110296101013101576045487)
                  ·
                    rfl

theorem cell20_241651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 8].length) (baseStart_241651 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241651 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241651 prefixEnd_241651 := by exact prefixLift 241651
  have htrace : WordTrace (prefixWord ++ tailWord_241651) baseStart_241651 baseEnd_241651 := by
    simpa [prefixWord, tailWord_241651, baseEnd_241651] using wordTrace_append hprefix tailTrace_241651
  have hstable : (prefixWord ++ tailWord_241651).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241651).length < 2 ^ (prefixWord ++ tailWord_241651).sum := by decide
  have hdescent : baseEnd_241651 < baseStart_241651 := by decide
  rcases family_descends (prefixWord ++ tailWord_241651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241661 : List Nat := [1, 4, 1, 1, 1, 2, 4, 3, 3]
def baseStart_241661 : Nat := 118140960795 + 241661 * 2 ^ 59
def prefixEnd_241661 : Nat := 4983230072969 + 3 ^ 40 * 241661 * 2
def baseEnd_241661 : Nat := 110300665285585985712113

theorem tailTrace_241661 : CollatzResearch.WordTrace tailWord_241661 prefixEnd_241661 110300665285585985712113 := by
  unfold tailWord_241661
  simp only [CollatzResearch.WordTrace]
  refine ⟨8814100777510944258044837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5876067185007296172029891 8814100777510944258044837)
  ·
    refine ⟨1652643895783302048383407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8814100777510944258044837 1652643895783302048383407)
    ·
      refine ⟨2478965843674953072575111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1652643895783302048383407 2478965843674953072575111)
      ·
        refine ⟨3718448765512429608862667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2478965843674953072575111 3718448765512429608862667)
        ·
          refine ⟨5577673148268644413294001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3718448765512429608862667 5577673148268644413294001)
          ·
            refine ⟨4183254861201483309970501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5577673148268644413294001 4183254861201483309970501)
            ·
              refine ⟨784360286475278120619469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4183254861201483309970501 784360286475278120619469)
              ·
                refine ⟨294135107428229295232301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 784360286475278120619469 294135107428229295232301)
                ·
                  refine ⟨110300665285585985712113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 294135107428229295232301 110300665285585985712113)
                  ·
                    rfl

theorem cell20_241661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_241661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241661 prefixEnd_241661 := by exact prefixLift 241661
  have htrace : WordTrace (prefixWord ++ tailWord_241661) baseStart_241661 baseEnd_241661 := by
    simpa [prefixWord, tailWord_241661, baseEnd_241661] using wordTrace_append hprefix tailTrace_241661
  have hstable : (prefixWord ++ tailWord_241661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241661).length < 2 ^ (prefixWord ++ tailWord_241661).sum := by decide
  have hdescent : baseEnd_241661 < baseStart_241661 := by decide
  rcases family_descends (prefixWord ++ tailWord_241661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241677 : List Nat := [1, 7, 1, 2, 1, 1, 2, 3, 2]
def baseStart_241677 : Nat := 118140960795 + 241677 * 2 ^ 59
def prefixEnd_241677 : Nat := 4983230072969 + 3 ^ 40 * 241677 * 2
def baseEnd_241677 : Nat := 110307968121561041178715

theorem tailTrace_241677 : CollatzResearch.WordTrace tailWord_241677 prefixEnd_241677 110307968121561041178715 := by
  unfold tailWord_241677
  simp only [CollatzResearch.WordTrace]
  refine ⟨8814684345452978990627285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5876456230301985993751523 8814684345452978990627285)
  ·
    refine ⟨206594164346554195092827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 8814684345452978990627285 206594164346554195092827)
    ·
      refine ⟨309891246519831292639241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206594164346554195092827 309891246519831292639241)
      ·
        refine ⟨232418434889873469479431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309891246519831292639241 232418434889873469479431)
        ·
          refine ⟨348627652334810204219147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232418434889873469479431 348627652334810204219147)
          ·
            refine ⟨522941478502215306328721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348627652334810204219147 522941478502215306328721)
            ·
              refine ⟨392206108876661479746541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 522941478502215306328721 392206108876661479746541)
              ·
                refine ⟨147077290828748054904953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 392206108876661479746541 147077290828748054904953)
                ·
                  refine ⟨110307968121561041178715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147077290828748054904953 110307968121561041178715)
                  ·
                    rfl

theorem cell20_241677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_241677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241677 prefixEnd_241677 := by exact prefixLift 241677
  have htrace : WordTrace (prefixWord ++ tailWord_241677) baseStart_241677 baseEnd_241677 := by
    simpa [prefixWord, tailWord_241677, baseEnd_241677] using wordTrace_append hprefix tailTrace_241677
  have hstable : (prefixWord ++ tailWord_241677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241677).length < 2 ^ (prefixWord ++ tailWord_241677).sum := by decide
  have hdescent : baseEnd_241677 < baseStart_241677 := by decide
  rcases family_descends (prefixWord ++ tailWord_241677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241689 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 8]
def baseStart_241689 : Nat := 118140960795 + 241689 * 2 ^ 59
def prefixEnd_241689 : Nat := 4983230072969 + 3 ^ 40 * 241689 * 2
def baseEnd_241689 : Nat := 110313445248542332778665

theorem tailTrace_241689 : CollatzResearch.WordTrace tailWord_241689 prefixEnd_241689 110313445248542332778665 := by
  unfold tailWord_241689
  simp only [CollatzResearch.WordTrace]
  refine ⟨8815122021409505040064121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5876748014273003360042747 8815122021409505040064121)
  ·
    refine ⟨6611341516057128780048091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8815122021409505040064121 6611341516057128780048091)
    ·
      refine ⟨9917012274085693170072137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6611341516057128780048091 9917012274085693170072137)
      ·
        refine ⟨7437759205564269877554103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9917012274085693170072137 7437759205564269877554103)
        ·
          refine ⟨11156638808346404816331155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7437759205564269877554103 11156638808346404816331155)
          ·
            refine ⟨16734958212519607224496733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11156638808346404816331155 16734958212519607224496733)
            ·
              refine ⟨6275609329694852709186275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16734958212519607224496733 6275609329694852709186275)
              ·
                refine ⟨9413413994542279063779413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6275609329694852709186275 9413413994542279063779413)
                ·
                  refine ⟨110313445248542332778665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9413413994542279063779413 110313445248542332778665)
                  ·
                    rfl

theorem cell20_241689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_241689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241689 prefixEnd_241689 := by exact prefixLift 241689
  have htrace : WordTrace (prefixWord ++ tailWord_241689) baseStart_241689 baseEnd_241689 := by
    simpa [prefixWord, tailWord_241689, baseEnd_241689] using wordTrace_append hprefix tailTrace_241689
  have hstable : (prefixWord ++ tailWord_241689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241689).length < 2 ^ (prefixWord ++ tailWord_241689).sum := by decide
  have hdescent : baseEnd_241689 < baseStart_241689 := by decide
  rcases family_descends (prefixWord ++ tailWord_241689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241726 : List Nat := [4, 2, 1, 3, 2, 2, 2, 4]
def baseStart_241726 : Nat := 118140960795 + 241726 * 2 ^ 59
def prefixEnd_241726 : Nat := 4983230072969 + 3 ^ 40 * 241726 * 2
def baseEnd_241726 : Nat := 36776777685578216181727

theorem tailTrace_241726 : CollatzResearch.WordTrace tailWord_241726 prefixEnd_241726 36776777685578216181727 := by
  unfold tailWord_241726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1102058940284432544895129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5877647681516973572774021 1102058940284432544895129)
  ·
    refine ⟨826544205213324408671347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1102058940284432544895129 826544205213324408671347)
    ·
      refine ⟨1239816307819986613007021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 826544205213324408671347 1239816307819986613007021)
      ·
        refine ⟨464931115432494979877633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1239816307819986613007021 464931115432494979877633)
        ·
          refine ⟨348698336574371234908225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464931115432494979877633 348698336574371234908225)
          ·
            refine ⟨261523752430778426181169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348698336574371234908225 261523752430778426181169)
            ·
              refine ⟨196142814323083819635877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261523752430778426181169 196142814323083819635877)
              ·
                refine ⟨36776777685578216181727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 196142814323083819635877 36776777685578216181727)
                ·
                  rfl

theorem cell20_241726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_241726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241726 prefixEnd_241726 := by exact prefixLift 241726
  have htrace : WordTrace (prefixWord ++ tailWord_241726) baseStart_241726 baseEnd_241726 := by
    simpa [prefixWord, tailWord_241726, baseEnd_241726] using wordTrace_append hprefix tailTrace_241726
  have hstable : (prefixWord ++ tailWord_241726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241726).length < 2 ^ (prefixWord ++ tailWord_241726).sum := by decide
  have hdescent : baseEnd_241726 < baseStart_241726 := by decide
  rcases family_descends (prefixWord ++ tailWord_241726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241775 : List Nat := [1, 1, 2, 1, 3, 5, 1, 3, 3]
def baseStart_241775 : Nat := 118140960795 + 241775 * 2 ^ 59
def prefixEnd_241775 : Nat := 4983230072969 + 3 ^ 40 * 241775 * 2
def baseEnd_241775 : Nat := 110352697991908255911647

theorem tailTrace_241775 : CollatzResearch.WordTrace tailWord_241775 prefixEnd_241775 110352697991908255911647 := by
  unfold tailWord_241775
  simp only [CollatzResearch.WordTrace]
  refine ⟨8818258699097941727694779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5878839132731961151796519 8818258699097941727694779)
  ·
    refine ⟨13227388048646912591542169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8818258699097941727694779 13227388048646912591542169)
    ·
      refine ⟨9920541036485184443656627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13227388048646912591542169 9920541036485184443656627)
      ·
        refine ⟨14880811554727776665484941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9920541036485184443656627 14880811554727776665484941)
        ·
          refine ⟨5580304333022916249556853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14880811554727776665484941 5580304333022916249556853)
          ·
            refine ⟨523153531220898398395955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5580304333022916249556853 523153531220898398395955)
            ·
              refine ⟨784730296831347597593933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523153531220898398395955 784730296831347597593933)
              ·
                refine ⟨294273861311755349097725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 784730296831347597593933 294273861311755349097725)
                ·
                  refine ⟨110352697991908255911647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 294273861311755349097725 110352697991908255911647)
                  ·
                    rfl

theorem cell20_241775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3, 3].length) (baseStart_241775 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241775 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241775 prefixEnd_241775 := by exact prefixLift 241775
  have htrace : WordTrace (prefixWord ++ tailWord_241775) baseStart_241775 baseEnd_241775 := by
    simpa [prefixWord, tailWord_241775, baseEnd_241775] using wordTrace_append hprefix tailTrace_241775
  have hstable : (prefixWord ++ tailWord_241775).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241775).length < 2 ^ (prefixWord ++ tailWord_241775).sum := by decide
  have hdescent : baseEnd_241775 < baseStart_241775 := by decide
  rcases family_descends (prefixWord ++ tailWord_241775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241789 : List Nat := [1, 4, 1, 1, 3, 2, 2, 6]
def baseStart_241789 : Nat := 118140960795 + 241789 * 2 ^ 59
def prefixEnd_241789 : Nat := 4983230072969 + 3 ^ 40 * 241789 * 2
def baseEnd_241789 : Nat := 36786362657795476481641

theorem tailTrace_241789 : CollatzResearch.WordTrace tailWord_241789 prefixEnd_241789 36786362657795476481641 := by
  unfold tailWord_241789
  simp only [CollatzResearch.WordTrace]
  refine ⟨8818769321047222118704421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5879179547364814745802947 8818769321047222118704421)
  ·
    refine ⟨1653519247696354147257079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8818769321047222118704421 1653519247696354147257079)
    ·
      refine ⟨2480278871544531220885619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1653519247696354147257079 2480278871544531220885619)
      ·
        refine ⟨3720418307316796831328429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2480278871544531220885619 3720418307316796831328429)
        ·
          refine ⟨1395156865243798811748161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3720418307316796831328429 1395156865243798811748161)
          ·
            refine ⟨1046367648932849108811121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1395156865243798811748161 1046367648932849108811121)
            ·
              refine ⟨784775736699636831608341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1046367648932849108811121 784775736699636831608341)
              ·
                refine ⟨36786362657795476481641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 784775736699636831608341 36786362657795476481641)
                ·
                  rfl

theorem cell20_241789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 6].length) (baseStart_241789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241789 prefixEnd_241789 := by exact prefixLift 241789
  have htrace : WordTrace (prefixWord ++ tailWord_241789) baseStart_241789 baseEnd_241789 := by
    simpa [prefixWord, tailWord_241789, baseEnd_241789] using wordTrace_append hprefix tailTrace_241789
  have hstable : (prefixWord ++ tailWord_241789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241789).length < 2 ^ (prefixWord ++ tailWord_241789).sum := by decide
  have hdescent : baseEnd_241789 < baseStart_241789 := by decide
  rcases family_descends (prefixWord ++ tailWord_241789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241806 : List Nat := [4, 1, 1, 3, 4, 7]
def baseStart_241806 : Nat := 118140960795 + 241806 * 2 ^ 59
def prefixEnd_241806 : Nat := 4983230072969 + 3 ^ 40 * 241806 * 2
def baseEnd_241806 : Nat := 4087661008763330588081

theorem tailTrace_241806 : CollatzResearch.WordTrace tailWord_241806 prefixEnd_241806 4087661008763330588081 := by
  unfold tailWord_241806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1102423670248204252759159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5879592907990422681382181 1102423670248204252759159)
  ·
    refine ⟨1653635505372306379138739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1102423670248204252759159 1653635505372306379138739)
    ·
      refine ⟨2480453258058459568708109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1653635505372306379138739 2480453258058459568708109)
      ·
        refine ⟨930169971771922338265541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2480453258058459568708109 930169971771922338265541)
        ·
          refine ⟨174406869707235438424789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 930169971771922338265541 174406869707235438424789)
          ·
            refine ⟨4087661008763330588081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 174406869707235438424789 4087661008763330588081)
            ·
              rfl

theorem cell20_241806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 7].length) (baseStart_241806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241806 prefixEnd_241806 := by exact prefixLift 241806
  have htrace : WordTrace (prefixWord ++ tailWord_241806) baseStart_241806 baseEnd_241806 := by
    simpa [prefixWord, tailWord_241806, baseEnd_241806] using wordTrace_append hprefix tailTrace_241806
  have hstable : (prefixWord ++ tailWord_241806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241806).length < 2 ^ (prefixWord ++ tailWord_241806).sum := by decide
  have hdescent : baseEnd_241806 < baseStart_241806 := by decide
  rcases family_descends (prefixWord ++ tailWord_241806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241813 : List Nat := [1, 3, 2, 1, 1, 1, 6, 2, 3]
def baseStart_241813 : Nat := 118140960795 + 241813 * 2 ^ 59
def prefixEnd_241813 : Nat := 4983230072969 + 3 ^ 40 * 241813 * 2
def baseEnd_241813 : Nat := 110370042227349012644825

theorem tailTrace_241813 : CollatzResearch.WordTrace tailWord_241813 prefixEnd_241813 110370042227349012644825 := by
  unfold tailWord_241813
  simp only [CollatzResearch.WordTrace]
  refine ⟨8819644672960274217578093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5879763115306849478385395 8819644672960274217578093)
  ·
    refine ⟨3307366752360102831591785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8819644672960274217578093 3307366752360102831591785)
    ·
      refine ⟨2480525064270077123693839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3307366752360102831591785 2480525064270077123693839)
      ·
        refine ⟨3720787596405115685540759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2480525064270077123693839 3720787596405115685540759)
        ·
          refine ⟨5581181394607673528311139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3720787596405115685540759 5581181394607673528311139)
          ·
            refine ⟨8371772091911510292466709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5581181394607673528311139 8371772091911510292466709)
            ·
              refine ⟨392426816808352044959377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8371772091911510292466709 392426816808352044959377)
              ·
                refine ⟨294320112606264033719533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 392426816808352044959377 294320112606264033719533)
                ·
                  refine ⟨110370042227349012644825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 294320112606264033719533 110370042227349012644825)
                  ·
                    rfl

theorem cell20_241813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2, 3].length) (baseStart_241813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241813 prefixEnd_241813 := by exact prefixLift 241813
  have htrace : WordTrace (prefixWord ++ tailWord_241813) baseStart_241813 baseEnd_241813 := by
    simpa [prefixWord, tailWord_241813, baseEnd_241813] using wordTrace_append hprefix tailTrace_241813
  have hstable : (prefixWord ++ tailWord_241813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241813).length < 2 ^ (prefixWord ++ tailWord_241813).sum := by decide
  have hdescent : baseEnd_241813 < baseStart_241813 := by decide
  rcases family_descends (prefixWord ++ tailWord_241813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241816 : List Nat := [2, 1, 2, 4, 3, 1, 1, 4, 2]
def baseStart_241816 : Nat := 118140960795 + 241816 * 2 ^ 59
def prefixEnd_241816 : Nat := 4983230072969 + 3 ^ 40 * 241816 * 2
def baseEnd_241816 : Nat := 110371411509094335544813

theorem tailTrace_241816 : CollatzResearch.WordTrace tailWord_241816 prefixEnd_241816 110371411509094335544813 := by
  unfold tailWord_241816
  simp only [CollatzResearch.WordTrace]
  refine ⟨4409877045974702864968651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5879836061299603819958201 4409877045974702864968651)
  ·
    refine ⟨6614815568962054297452977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4409877045974702864968651 6614815568962054297452977)
    ·
      refine ⟨4961111676721540723089733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6614815568962054297452977 4961111676721540723089733)
      ·
        refine ⟨930208439385288885579325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4961111676721540723089733 930208439385288885579325)
        ·
          refine ⟨348828164769483332092247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 930208439385288885579325 348828164769483332092247)
          ·
            refine ⟨523242247154224998138371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348828164769483332092247 523242247154224998138371)
            ·
              refine ⟨784863370731337497207557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523242247154224998138371 784863370731337497207557)
              ·
                refine ⟨147161882012125780726417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 784863370731337497207557 147161882012125780726417)
                ·
                  refine ⟨110371411509094335544813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147161882012125780726417 110371411509094335544813)
                  ·
                    rfl

theorem cell20_241816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 4, 2].length) (baseStart_241816 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241816 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241816 prefixEnd_241816 := by exact prefixLift 241816
  have htrace : WordTrace (prefixWord ++ tailWord_241816) baseStart_241816 baseEnd_241816 := by
    simpa [prefixWord, tailWord_241816, baseEnd_241816] using wordTrace_append hprefix tailTrace_241816
  have hstable : (prefixWord ++ tailWord_241816).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241816).length < 2 ^ (prefixWord ++ tailWord_241816).sum := by decide
  have hdescent : baseEnd_241816 < baseStart_241816 := by decide
  rcases family_descends (prefixWord ++ tailWord_241816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241820 : List Nat := [2, 2, 3, 2, 1, 1, 2, 3, 4]
def baseStart_241820 : Nat := 118140960795 + 241820 * 2 ^ 59
def prefixEnd_241820 : Nat := 4983230072969 + 3 ^ 40 * 241820 * 2
def baseEnd_241820 : Nat := 110373237218088099411463

theorem tailTrace_241820 : CollatzResearch.WordTrace tailWord_241820 prefixEnd_241820 110373237218088099411463 := by
  unfold tailWord_241820
  simp only [CollatzResearch.WordTrace]
  refine ⟨4409949991967457206541457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5879933322623276275388609 4409949991967457206541457)
  ·
    refine ⟨3307462493975592904906093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4409949991967457206541457 3307462493975592904906093)
    ·
      refine ⟨1240298435240847339339785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3307462493975592904906093 1240298435240847339339785)
      ·
        refine ⟨930223826430635504504839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1240298435240847339339785 930223826430635504504839)
        ·
          refine ⟨1395335739645953256757259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 930223826430635504504839 1395335739645953256757259)
          ·
            refine ⟨2093003609468929885135889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1395335739645953256757259 2093003609468929885135889)
            ·
              refine ⟨1569752707101697413851917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2093003609468929885135889 1569752707101697413851917)
              ·
                refine ⟨588657265163136530194469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1569752707101697413851917 588657265163136530194469)
                ·
                  refine ⟨110373237218088099411463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 588657265163136530194469 110373237218088099411463)
                  ·
                    rfl

theorem cell20_241820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_241820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241820 prefixEnd_241820 := by exact prefixLift 241820
  have htrace : WordTrace (prefixWord ++ tailWord_241820) baseStart_241820 baseEnd_241820 := by
    simpa [prefixWord, tailWord_241820, baseEnd_241820] using wordTrace_append hprefix tailTrace_241820
  have hstable : (prefixWord ++ tailWord_241820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241820).length < 2 ^ (prefixWord ++ tailWord_241820).sum := by decide
  have hdescent : baseEnd_241820 < baseStart_241820 := by decide
  rcases family_descends (prefixWord ++ tailWord_241820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241837 : List Nat := [1, 5, 2, 1, 2, 2, 1, 2, 4]
def baseStart_241837 : Nat := 118140960795 + 241837 * 2 ^ 59
def prefixEnd_241837 : Nat := 4983230072969 + 3 ^ 40 * 241837 * 2
def baseEnd_241837 : Nat := 110380996481311595844727

theorem tailTrace_241837 : CollatzResearch.WordTrace tailWord_241837 prefixEnd_241837 110380996481311595844727 := by
  unfold tailWord_241837
  simp only [CollatzResearch.WordTrace]
  refine ⟨8820520024873326316451765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5880346683248884210967843 8820520024873326316451765)
  ·
    refine ⟨826923752331874342167353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8820520024873326316451765 826923752331874342167353)
    ·
      refine ⟨620192814248905756625515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 826923752331874342167353 620192814248905756625515)
      ·
        refine ⟨930289221373358634938273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 620192814248905756625515 930289221373358634938273)
        ·
          refine ⟨697716916030018976203705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 930289221373358634938273 697716916030018976203705)
          ·
            refine ⟨523287687022514232152779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 697716916030018976203705 523287687022514232152779)
            ·
              refine ⟨784931530533771348229169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523287687022514232152779 784931530533771348229169)
              ·
                refine ⟨588698647900328511171877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 784931530533771348229169 588698647900328511171877)
                ·
                  refine ⟨110380996481311595844727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 588698647900328511171877 110380996481311595844727)
                  ·
                    rfl

theorem cell20_241837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_241837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241837 prefixEnd_241837 := by exact prefixLift 241837
  have htrace : WordTrace (prefixWord ++ tailWord_241837) baseStart_241837 baseEnd_241837 := by
    simpa [prefixWord, tailWord_241837, baseEnd_241837] using wordTrace_append hprefix tailTrace_241837
  have hstable : (prefixWord ++ tailWord_241837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241837).length < 2 ^ (prefixWord ++ tailWord_241837).sum := by decide
  have hdescent : baseEnd_241837 < baseStart_241837 := by decide
  rcases family_descends (prefixWord ++ tailWord_241837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241868 : List Nat := [2, 2, 1, 6, 1, 1, 1, 1, 5]
def baseStart_241868 : Nat := 118140960795 + 241868 * 2 ^ 59
def prefixEnd_241868 : Nat := 4983230072969 + 3 ^ 40 * 241868 * 2
def baseEnd_241868 : Nat := 110395145726013265811267

theorem tailTrace_241868 : CollatzResearch.WordTrace tailWord_241868 prefixEnd_241868 110395145726013265811267 := by
  unfold tailWord_241868
  simp only [CollatzResearch.WordTrace]
  refine ⟨4410825343880509305415129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5881100458507345740553505 4410825343880509305415129)
  ·
    refine ⟨3308119007910381979061347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4410825343880509305415129 3308119007910381979061347)
    ·
      refine ⟨4962178511865572968592021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3308119007910381979061347 4962178511865572968592021)
      ·
        refine ⟨232602117743698732902751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4962178511865572968592021 232602117743698732902751)
        ·
          refine ⟨348903176615548099354127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232602117743698732902751 348903176615548099354127)
          ·
            refine ⟨523354764923322149031191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348903176615548099354127 523354764923322149031191)
            ·
              refine ⟨785032147384983223546787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523354764923322149031191 785032147384983223546787)
              ·
                refine ⟨1177548221077474835320181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 785032147384983223546787 1177548221077474835320181)
                ·
                  refine ⟨110395145726013265811267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1177548221077474835320181 110395145726013265811267)
                  ·
                    rfl

theorem cell20_241868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 5].length) (baseStart_241868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241868 prefixEnd_241868 := by exact prefixLift 241868
  have htrace : WordTrace (prefixWord ++ tailWord_241868) baseStart_241868 baseEnd_241868 := by
    simpa [prefixWord, tailWord_241868, baseEnd_241868] using wordTrace_append hprefix tailTrace_241868
  have hstable : (prefixWord ++ tailWord_241868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241868).length < 2 ^ (prefixWord ++ tailWord_241868).sum := by decide
  have hdescent : baseEnd_241868 < baseStart_241868 := by decide
  rcases family_descends (prefixWord ++ tailWord_241868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241885 : List Nat := [1, 4, 3, 2, 1, 2, 3, 1, 3]
def baseStart_241885 : Nat := 118140960795 + 241885 * 2 ^ 59
def prefixEnd_241885 : Nat := 4983230072969 + 3 ^ 40 * 241885 * 2
def baseEnd_241885 : Nat := 110402904989236762244531

theorem tailTrace_241885 : CollatzResearch.WordTrace tailWord_241885 prefixEnd_241885 110402904989236762244531 := by
  unfold tailWord_241885
  simp only [CollatzResearch.WordTrace]
  refine ⟨8822270728699430514199109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5881513819132953676132739 8822270728699430514199109)
  ·
    refine ⟨1654175761631143221412333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8822270728699430514199109 1654175761631143221412333)
    ·
      refine ⟨620315910611678708029625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1654175761631143221412333 620315910611678708029625)
      ·
        refine ⟨465236932958759031022219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 620315910611678708029625 465236932958759031022219)
        ·
          refine ⟨697855399438138546533329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465236932958759031022219 697855399438138546533329)
          ·
            refine ⟨523391549578603909899997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 697855399438138546533329 523391549578603909899997)
            ·
              refine ⟨196271831091976466212499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 523391549578603909899997 196271831091976466212499)
              ·
                refine ⟨294407746637964699318749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196271831091976466212499 294407746637964699318749)
                ·
                  refine ⟨110402904989236762244531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 294407746637964699318749 110402904989236762244531)
                  ·
                    rfl

theorem cell20_241885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_241885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241885 prefixEnd_241885 := by exact prefixLift 241885
  have htrace : WordTrace (prefixWord ++ tailWord_241885) baseStart_241885 baseEnd_241885 := by
    simpa [prefixWord, tailWord_241885, baseEnd_241885] using wordTrace_append hprefix tailTrace_241885
  have hstable : (prefixWord ++ tailWord_241885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241885).length < 2 ^ (prefixWord ++ tailWord_241885).sum := by decide
  have hdescent : baseEnd_241885 < baseStart_241885 := by decide
  rcases family_descends (prefixWord ++ tailWord_241885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241896 : List Nat := [2, 1, 4, 1, 2, 2, 2, 2, 4]
def baseStart_241896 : Nat := 118140960795 + 241896 * 2 ^ 59
def prefixEnd_241896 : Nat := 4983230072969 + 3 ^ 40 * 241896 * 2
def baseEnd_241896 : Nat := 110407925688969612877819

theorem tailTrace_241896 : CollatzResearch.WordTrace tailWord_241896 prefixEnd_241896 110407925688969612877819 := by
  unfold tailWord_241896
  simp only [CollatzResearch.WordTrace]
  refine ⟨4411335965829789696424771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5881781287773052928566361 4411335965829789696424771)
  ·
    refine ⟨6617003948744684544637157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4411335965829789696424771 6617003948744684544637157)
    ·
      refine ⟨1240688240389628352119467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6617003948744684544637157 1240688240389628352119467)
      ·
        refine ⟨1861032360584442528179201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1240688240389628352119467 1861032360584442528179201)
        ·
          refine ⟨1395774270438331896134401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1861032360584442528179201 1395774270438331896134401)
          ·
            refine ⟨1046830702828748922100801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1395774270438331896134401 1046830702828748922100801)
            ·
              refine ⟨785123027121561691575601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1046830702828748922100801 785123027121561691575601)
              ·
                refine ⟨588842270341171268681701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 785123027121561691575601 588842270341171268681701)
                ·
                  refine ⟨110407925688969612877819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 588842270341171268681701 110407925688969612877819)
                  ·
                    rfl

theorem cell20_241896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 4].length) (baseStart_241896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241896 prefixEnd_241896 := by exact prefixLift 241896
  have htrace : WordTrace (prefixWord ++ tailWord_241896) baseStart_241896 baseEnd_241896 := by
    simpa [prefixWord, tailWord_241896, baseEnd_241896] using wordTrace_append hprefix tailTrace_241896
  have hstable : (prefixWord ++ tailWord_241896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241896).length < 2 ^ (prefixWord ++ tailWord_241896).sum := by decide
  have hdescent : baseEnd_241896 < baseStart_241896 := by decide
  rcases family_descends (prefixWord ++ tailWord_241896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241903 : List Nat := [1, 1, 2, 1, 6, 2, 1, 6]
def baseStart_241903 : Nat := 118140960795 + 241903 * 2 ^ 59
def prefixEnd_241903 : Nat := 4983230072969 + 3 ^ 40 * 241903 * 2
def baseEnd_241903 : Nat := 36803706893236233214819

theorem tailTrace_241903 : CollatzResearch.WordTrace tailWord_241903 prefixEnd_241903 36803706893236233214819 := by
  unfold tailWord_241903
  simp only [CollatzResearch.WordTrace]
  refine ⟨8822927242634219588354363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5881951495089479725569575 8822927242634219588354363)
  ·
    refine ⟨13234390863951329382531545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8822927242634219588354363 13234390863951329382531545)
    ·
      refine ⟨9925793147963497036898659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13234390863951329382531545 9925793147963497036898659)
      ·
        refine ⟨14888689721945245555347989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9925793147963497036898659 14888689721945245555347989)
        ·
          refine ⟨697907330716183385406937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14888689721945245555347989 697907330716183385406937)
          ·
            refine ⟨523430498037137539055203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 697907330716183385406937 523430498037137539055203)
            ·
              refine ⟨785145747055706308582805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523430498037137539055203 785145747055706308582805)
              ·
                refine ⟨36803706893236233214819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 785145747055706308582805 36803706893236233214819)
                ·
                  rfl

theorem cell20_241903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 6].length) (baseStart_241903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241903 prefixEnd_241903 := by exact prefixLift 241903
  have htrace : WordTrace (prefixWord ++ tailWord_241903) baseStart_241903 baseEnd_241903 := by
    simpa [prefixWord, tailWord_241903, baseEnd_241903] using wordTrace_append hprefix tailTrace_241903
  have hstable : (prefixWord ++ tailWord_241903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241903).length < 2 ^ (prefixWord ++ tailWord_241903).sum := by decide
  have hdescent : baseEnd_241903 < baseStart_241903 := by decide
  rcases family_descends (prefixWord ++ tailWord_241903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241917 : List Nat := [1, 4, 1, 1, 1, 1, 1, 4, 6]
def baseStart_241917 : Nat := 118140960795 + 241917 * 2 ^ 59
def prefixEnd_241917 : Nat := 4983230072969 + 3 ^ 40 * 241917 * 2
def baseEnd_241917 : Nat := 110417510661186873177733

theorem tailTrace_241917 : CollatzResearch.WordTrace tailWord_241917 prefixEnd_241917 110417510661186873177733 := by
  unfold tailWord_241917
  simp only [CollatzResearch.WordTrace]
  refine ⟨8823437864583499979364005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5882291909722333319576003 8823437864583499979364005)
  ·
    refine ⟨1654394599609406246130751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8823437864583499979364005 1654394599609406246130751)
    ·
      refine ⟨2481591899414109369196127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1654394599609406246130751 2481591899414109369196127)
      ·
        refine ⟨3722387849121164053794191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2481591899414109369196127 3722387849121164053794191)
        ·
          refine ⟨5583581773681746080691287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3722387849121164053794191 5583581773681746080691287)
          ·
            refine ⟨8375372660522619121036931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5583581773681746080691287 8375372660522619121036931)
            ·
              refine ⟨12563058990783928681555397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8375372660522619121036931 12563058990783928681555397)
              ·
                refine ⟨2355573560771986627791637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12563058990783928681555397 2355573560771986627791637)
                ·
                  refine ⟨110417510661186873177733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2355573560771986627791637 110417510661186873177733)
                  ·
                    rfl

theorem cell20_241917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_241917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241917 prefixEnd_241917 := by exact prefixLift 241917
  have htrace : WordTrace (prefixWord ++ tailWord_241917) baseStart_241917 baseEnd_241917 := by
    simpa [prefixWord, tailWord_241917, baseEnd_241917] using wordTrace_append hprefix tailTrace_241917
  have hstable : (prefixWord ++ tailWord_241917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241917).length < 2 ^ (prefixWord ++ tailWord_241917).sum := by decide
  have hdescent : baseEnd_241917 < baseStart_241917 := by decide
  rcases family_descends (prefixWord ++ tailWord_241917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241955 : List Nat := [1, 1, 1, 4, 2, 2, 2, 1, 6]
def baseStart_241955 : Nat := 118140960795 + 241955 * 2 ^ 59
def prefixEnd_241955 : Nat := 4983230072969 + 3 ^ 40 * 241955 * 2
def baseEnd_241955 : Nat := 110434854896627629910911

theorem tailTrace_241955 : CollatzResearch.WordTrace tailWord_241955 prefixEnd_241955 110434854896627629910911 := by
  unfold tailWord_241955
  simp only [CollatzResearch.WordTrace]
  refine ⟨8824823838445832469247319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5883215892297221646164879 8824823838445832469247319)
  ·
    refine ⟨13237235757668748703870979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8824823838445832469247319 13237235757668748703870979)
    ·
      refine ⟨19855853636503123055806469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13237235757668748703870979 19855853636503123055806469)
      ·
        refine ⟨3722972556844335572963713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19855853636503123055806469 3722972556844335572963713)
        ·
          refine ⟨2792229417633251679722785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3722972556844335572963713 2792229417633251679722785)
          ·
            refine ⟨2094172063224938759792089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2792229417633251679722785 2094172063224938759792089)
            ·
              refine ⟨1570629047418704069844067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2094172063224938759792089 1570629047418704069844067)
              ·
                refine ⟨2355943571128056104766101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1570629047418704069844067 2355943571128056104766101)
                ·
                  refine ⟨110434854896627629910911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2355943571128056104766101 110434854896627629910911)
                  ·
                    rfl

theorem cell20_241955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 6].length) (baseStart_241955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241955 prefixEnd_241955 := by exact prefixLift 241955
  have htrace : WordTrace (prefixWord ++ tailWord_241955) baseStart_241955 baseEnd_241955 := by
    simpa [prefixWord, tailWord_241955, baseEnd_241955] using wordTrace_append hprefix tailTrace_241955
  have hstable : (prefixWord ++ tailWord_241955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241955).length < 2 ^ (prefixWord ++ tailWord_241955).sum := by decide
  have hdescent : baseEnd_241955 < baseStart_241955 := by decide
  rcases family_descends (prefixWord ++ tailWord_241955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241982 : List Nat := [4, 2, 1, 2, 1, 3, 2, 2, 3]
def baseStart_241982 : Nat := 118140960795 + 241982 * 2 ^ 59
def prefixEnd_241982 : Nat := 4983230072969 + 3 ^ 40 * 241982 * 2
def baseEnd_241982 : Nat := 110447178432335536010801

theorem tailTrace_241982 : CollatzResearch.WordTrace tailWord_241982 prefixEnd_241982 110447178432335536010801 := by
  unfold tailWord_241982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1103226076168502010060025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5883872406232010720320133 1103226076168502010060025)
  ·
    refine ⟨827419557126376507545019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1103226076168502010060025 827419557126376507545019)
    ·
      refine ⟨1241129335689564761317529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 827419557126376507545019 1241129335689564761317529)
      ·
        refine ⟨930847001767173570988147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1241129335689564761317529 930847001767173570988147)
        ·
          refine ⟨1396270502650760356482221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 930847001767173570988147 1396270502650760356482221)
          ·
            refine ⟨523601438494035133680833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1396270502650760356482221 523601438494035133680833)
            ·
              refine ⟨392701078870526350260625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 523601438494035133680833 392701078870526350260625)
              ·
                refine ⟨294525809152894762695469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 392701078870526350260625 294525809152894762695469)
                ·
                  refine ⟨110447178432335536010801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 294525809152894762695469 110447178432335536010801)
                  ·
                    rfl

theorem cell20_241982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_241982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241982 prefixEnd_241982 := by exact prefixLift 241982
  have htrace : WordTrace (prefixWord ++ tailWord_241982) baseStart_241982 baseEnd_241982 := by
    simpa [prefixWord, tailWord_241982, baseEnd_241982] using wordTrace_append hprefix tailTrace_241982
  have hstable : (prefixWord ++ tailWord_241982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241982).length < 2 ^ (prefixWord ++ tailWord_241982).sum := by decide
  have hdescent : baseEnd_241982 < baseStart_241982 := by decide
  rcases family_descends (prefixWord ++ tailWord_241982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241993 : List Nat := [1, 2, 1, 1, 2, 3, 1, 5, 4]
def baseStart_241993 : Nat := 118140960795 + 241993 * 2 ^ 59
def prefixEnd_241993 : Nat := 4983230072969 + 3 ^ 40 * 241993 * 2
def baseEnd_241993 : Nat := 110452199132068386644089

theorem tailTrace_241993 : CollatzResearch.WordTrace tailWord_241993 prefixEnd_241993 110452199132068386644089 := by
  unfold tailWord_241993
  simp only [CollatzResearch.WordTrace]
  refine ⟨8826209812308164959130633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5884139874872109972753755 8826209812308164959130633)
  ·
    refine ⟨6619657359231123719347975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8826209812308164959130633 6619657359231123719347975)
    ·
      refine ⟨9929486038846685579021963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6619657359231123719347975 9929486038846685579021963)
      ·
        refine ⟨14894229058270028368532945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9929486038846685579021963 14894229058270028368532945)
        ·
          refine ⟨11170671793702521276399709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14894229058270028368532945 11170671793702521276399709)
          ·
            refine ⟨4189001922638445478649891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11170671793702521276399709 4189001922638445478649891)
            ·
              refine ⟨6283502883957668217974837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4189001922638445478649891 6283502883957668217974837)
              ·
                refine ⟨589078395371031395435141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6283502883957668217974837 589078395371031395435141)
                ·
                  refine ⟨110452199132068386644089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 589078395371031395435141 110452199132068386644089)
                  ·
                    rfl

theorem cell20_241993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 4].length) (baseStart_241993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_241993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_241993 prefixEnd_241993 := by exact prefixLift 241993
  have htrace : WordTrace (prefixWord ++ tailWord_241993) baseStart_241993 baseEnd_241993 := by
    simpa [prefixWord, tailWord_241993, baseEnd_241993] using wordTrace_append hprefix tailTrace_241993
  have hstable : (prefixWord ++ tailWord_241993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241993).length < 2 ^ (prefixWord ++ tailWord_241993).sum := by decide
  have hdescent : baseEnd_241993 < baseStart_241993 := by decide
  rcases family_descends (prefixWord ++ tailWord_241993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242068 : List Nat := [2, 4, 2, 1, 4, 1, 2, 4]
def baseStart_242068 : Nat := 118140960795 + 242068 * 2 ^ 59
def prefixEnd_242068 : Nat := 4983230072969 + 3 ^ 40 * 242068 * 2
def baseEnd_242068 : Nat := 36828810391900486381261

theorem tailTrace_242068 : CollatzResearch.WordTrace tailWord_242068 prefixEnd_242068 36828810391900486381261 := by
  unfold tailWord_242068
  simp only [CollatzResearch.WordTrace]
  refine ⟨4414472643518226384055429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5885963524690968512073905 4414472643518226384055429)
  ·
    refine ⟨827713620659667447010393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4414472643518226384055429 827713620659667447010393)
    ·
      refine ⟨620785215494750585257795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 827713620659667447010393 620785215494750585257795)
      ·
        refine ⟨931177823242125877886693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 620785215494750585257795 931177823242125877886693)
        ·
          refine ⟨174595841857898602103755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 931177823242125877886693 174595841857898602103755)
          ·
            refine ⟨261893762786847903155633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174595841857898602103755 261893762786847903155633)
            ·
              refine ⟨196420322090135927366725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261893762786847903155633 196420322090135927366725)
              ·
                refine ⟨36828810391900486381261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 196420322090135927366725 36828810391900486381261)
                ·
                  rfl

theorem cell20_242068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 4].length) (baseStart_242068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_242068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_242068 prefixEnd_242068 := by exact prefixLift 242068
  have htrace : WordTrace (prefixWord ++ tailWord_242068) baseStart_242068 baseEnd_242068 := by
    simpa [prefixWord, tailWord_242068, baseEnd_242068] using wordTrace_append hprefix tailTrace_242068
  have hstable : (prefixWord ++ tailWord_242068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242068).length < 2 ^ (prefixWord ++ tailWord_242068).sum := by decide
  have hdescent : baseEnd_242068 < baseStart_242068 := by decide
  rcases family_descends (prefixWord ++ tailWord_242068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242072 : List Nat := [2, 1, 2, 5, 1, 1, 4, 4]
def baseStart_242072 : Nat := 118140960795 + 242072 * 2 ^ 59
def prefixEnd_242072 : Nat := 4983230072969 + 3 ^ 40 * 242072 * 2
def baseEnd_242072 : Nat := 36829418961565074336811

theorem tailTrace_242072 : CollatzResearch.WordTrace tailWord_242072 prefixEnd_242072 36829418961565074336811 := by
  unfold tailWord_242072
  simp only [CollatzResearch.WordTrace]
  refine ⟨4414545589510980725628235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5886060786014640967504313 4414545589510980725628235)
  ·
    refine ⟨6621818384266471088442353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4414545589510980725628235 6621818384266471088442353)
    ·
      refine ⟨4966363788199853316331765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6621818384266471088442353 4966363788199853316331765)
      ·
        refine ⟨465596605143736248406103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4966363788199853316331765 465596605143736248406103)
        ·
          refine ⟨698394907715604372609155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465596605143736248406103 698394907715604372609155)
          ·
            refine ⟨1047592361573406558913733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 698394907715604372609155 1047592361573406558913733)
            ·
              refine ⟨196423567795013729796325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1047592361573406558913733 196423567795013729796325)
              ·
                refine ⟨36829418961565074336811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 196423567795013729796325 36829418961565074336811)
                ·
                  rfl

theorem cell20_242072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 4].length) (baseStart_242072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_242072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_242072 prefixEnd_242072 := by exact prefixLift 242072
  have htrace : WordTrace (prefixWord ++ tailWord_242072) baseStart_242072 baseEnd_242072 := by
    simpa [prefixWord, tailWord_242072, baseEnd_242072] using wordTrace_append hprefix tailTrace_242072
  have hstable : (prefixWord ++ tailWord_242072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242072).length < 2 ^ (prefixWord ++ tailWord_242072).sum := by decide
  have hdescent : baseEnd_242072 < baseStart_242072 := by decide
  rcases family_descends (prefixWord ++ tailWord_242072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242141 : List Nat := [1, 4, 3, 1, 1, 1, 2, 5, 2]
def baseStart_242141 : Nat := 118140960795 + 242141 * 2 ^ 59
def prefixEnd_242141 : Nat := 4983230072969 + 3 ^ 40 * 242141 * 2
def baseEnd_242141 : Nat := 110519750364837649710151

theorem tailTrace_242141 : CollatzResearch.WordTrace tailWord_242141 prefixEnd_242141 110519750364837649710151 := by
  unfold tailWord_242141
  simp only [CollatzResearch.WordTrace]
  refine ⟨8831607815771986235518277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5887738543847990823678851 8831607815771986235518277)
  ·
    refine ⟨1655926465457247419159677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8831607815771986235518277 1655926465457247419159677)
    ·
      refine ⟨620972424546467782184879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1655926465457247419159677 620972424546467782184879)
      ·
        refine ⟨931458636819701673277319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 620972424546467782184879 931458636819701673277319)
        ·
          refine ⟨1397187955229552509915979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 931458636819701673277319 1397187955229552509915979)
          ·
            refine ⟨2095781932844328764873969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1397187955229552509915979 2095781932844328764873969)
            ·
              refine ⟨1571836449633246573655477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2095781932844328764873969 1571836449633246573655477)
              ·
                refine ⟨147359667153116866280201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1571836449633246573655477 147359667153116866280201)
                ·
                  refine ⟨110519750364837649710151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147359667153116866280201 110519750364837649710151)
                  ·
                    rfl

theorem cell20_242141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 5, 2].length) (baseStart_242141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_242141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_242141 prefixEnd_242141 := by exact prefixLift 242141
  have htrace : WordTrace (prefixWord ++ tailWord_242141) baseStart_242141 baseEnd_242141 := by
    simpa [prefixWord, tailWord_242141, baseEnd_242141] using wordTrace_append hprefix tailTrace_242141
  have hstable : (prefixWord ++ tailWord_242141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242141).length < 2 ^ (prefixWord ++ tailWord_242141).sum := by decide
  have hdescent : baseEnd_242141 < baseStart_242141 := by decide
  rcases family_descends (prefixWord ++ tailWord_242141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242152 : List Nat := [2, 1, 4, 1, 1, 11]
def baseStart_242152 : Nat := 118140960795 + 242152 * 2 ^ 59
def prefixEnd_242152 : Nat := 4983230072969 + 3 ^ 40 * 242152 * 2
def baseEnd_242152 : Nat := 4093510039428537049757

theorem tailTrace_242152 : CollatzResearch.WordTrace tailWord_242152 prefixEnd_242152 4093510039428537049757 := by
  unfold tailWord_242152
  simp only [CollatzResearch.WordTrace]
  refine ⟨4416004509366067557084355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5888006012488090076112473 4416004509366067557084355)
  ·
    refine ⟨6624006764049101335626533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4416004509366067557084355 6624006764049101335626533)
    ·
      refine ⟨1242001268259206500429975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6624006764049101335626533 1242001268259206500429975)
      ·
        refine ⟨1863001902388809750644963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1242001268259206500429975 1863001902388809750644963)
        ·
          refine ⟨2794502853583214625967445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1863001902388809750644963 2794502853583214625967445)
          ·
            refine ⟨4093510039428537049757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2794502853583214625967445 4093510039428537049757)
            ·
              rfl

theorem cell20_242152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 11].length) (baseStart_242152 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_242152 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_242152 prefixEnd_242152 := by exact prefixLift 242152
  have htrace : WordTrace (prefixWord ++ tailWord_242152) baseStart_242152 baseEnd_242152 := by
    simpa [prefixWord, tailWord_242152, baseEnd_242152] using wordTrace_append hprefix tailTrace_242152
  have hstable : (prefixWord ++ tailWord_242152).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242152).length < 2 ^ (prefixWord ++ tailWord_242152).sum := by decide
  have hdescent : baseEnd_242152 < baseStart_242152 := by decide
  rcases family_descends (prefixWord ++ tailWord_242152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242158 : List Nat := [4, 1, 2, 1, 2, 2, 4, 2, 2]
def baseStart_242158 : Nat := 118140960795 + 242158 * 2 ^ 59
def prefixEnd_242158 : Nat := 4983230072969 + 3 ^ 40 * 242158 * 2
def baseEnd_242158 : Nat := 110527509628061146143415

theorem tailTrace_242158 : CollatzResearch.WordTrace tailWord_242158 prefixEnd_242158 110527509628061146143415 := by
  unfold tailWord_242158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1104028482088799767360891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5888151904473598759258085 1104028482088799767360891)
  ·
    refine ⟨1656042723133199651041337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1104028482088799767360891 1656042723133199651041337)
    ·
      refine ⟨1242032042349899738281003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1656042723133199651041337 1242032042349899738281003)
      ·
        refine ⟨1863048063524849607421505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1242032042349899738281003 1863048063524849607421505)
        ·
          refine ⟨1397286047643637205566129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1863048063524849607421505 1397286047643637205566129)
          ·
            refine ⟨1047964535732727904174597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1397286047643637205566129 1047964535732727904174597)
            ·
              refine ⟨196493350449886482032737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1047964535732727904174597 196493350449886482032737)
              ·
                refine ⟨147370012837414861524553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196493350449886482032737 147370012837414861524553)
                ·
                  refine ⟨110527509628061146143415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147370012837414861524553 110527509628061146143415)
                  ·
                    rfl

theorem cell20_242158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 2, 2].length) (baseStart_242158 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_242158 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_242158 prefixEnd_242158 := by exact prefixLift 242158
  have htrace : WordTrace (prefixWord ++ tailWord_242158) baseStart_242158 baseEnd_242158 := by
    simpa [prefixWord, tailWord_242158, baseEnd_242158] using wordTrace_append hprefix tailTrace_242158
  have hstable : (prefixWord ++ tailWord_242158).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242158).length < 2 ^ (prefixWord ++ tailWord_242158).sum := by decide
  have hdescent : baseEnd_242158 < baseStart_242158 := by decide
  rcases family_descends (prefixWord ++ tailWord_242158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242165 : List Nat := [1, 3, 5, 1, 2, 2, 1, 5]
def baseStart_242165 : Nat := 118140960795 + 242165 * 2 ^ 59
def prefixEnd_242165 : Nat := 4983230072969 + 3 ^ 40 * 242165 * 2
def baseEnd_242165 : Nat := 36843568206266744303351

theorem tailTrace_242165 : CollatzResearch.WordTrace tailWord_242165 prefixEnd_242165 36843568206266744303351 := by
  unfold tailWord_242165
  simp only [CollatzResearch.WordTrace]
  refine ⟨8832483167685038334391949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5888322111790025556261299 8832483167685038334391949)
  ·
    refine ⟨3312181187881889375396981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8832483167685038334391949 3312181187881889375396981)
    ·
      refine ⟨310516986363927128943467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3312181187881889375396981 310516986363927128943467)
      ·
        refine ⟨465775479545890693415201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310516986363927128943467 465775479545890693415201)
        ·
          refine ⟨349331609659418020061401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 465775479545890693415201 349331609659418020061401)
          ·
            refine ⟨261998707244563515046051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 349331609659418020061401 261998707244563515046051)
            ·
              refine ⟨392998060866845272569077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261998707244563515046051 392998060866845272569077)
              ·
                refine ⟨36843568206266744303351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 392998060866845272569077 36843568206266744303351)
                ·
                  rfl

theorem cell20_242165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 5].length) (baseStart_242165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_242165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_242165 prefixEnd_242165 := by exact prefixLift 242165
  have htrace : WordTrace (prefixWord ++ tailWord_242165) baseStart_242165 baseEnd_242165 := by
    simpa [prefixWord, tailWord_242165, baseEnd_242165] using wordTrace_append hprefix tailTrace_242165
  have hstable : (prefixWord ++ tailWord_242165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242165).length < 2 ^ (prefixWord ++ tailWord_242165).sum := by decide
  have hdescent : baseEnd_242165 < baseStart_242165 := by decide
  rcases family_descends (prefixWord ++ tailWord_242165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242196 : List Nat := [2, 4, 3, 1, 1, 1, 1, 5, 2]
def baseStart_242196 : Nat := 118140960795 + 242196 * 2 ^ 59
def prefixEnd_242196 : Nat := 4983230072969 + 3 ^ 40 * 242196 * 2
def baseEnd_242196 : Nat := 110544853863501902876593

theorem tailTrace_242196 : CollatzResearch.WordTrace tailWord_242196 prefixEnd_242196 110544853863501902876593 := by
  unfold tailWord_242196
  simp only [CollatzResearch.WordTrace]
  refine ⟨4416806915286365314385221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5889075887048487085846961 4416806915286365314385221)
  ·
    refine ⟨828151296616193496447229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4416806915286365314385221 828151296616193496447229)
    ·
      refine ⟨310556736231072561167711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 828151296616193496447229 310556736231072561167711)
      ·
        refine ⟨465835104346608841751567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310556736231072561167711 465835104346608841751567)
        ·
          refine ⟨698752656519913262627351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465835104346608841751567 698752656519913262627351)
          ·
            refine ⟨1048128984779869893941027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 698752656519913262627351 1048128984779869893941027)
            ·
              refine ⟨1572193477169804840911541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1048128984779869893941027 1572193477169804840911541)
              ·
                refine ⟨147393138484669203835457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1572193477169804840911541 147393138484669203835457)
                ·
                  refine ⟨110544853863501902876593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147393138484669203835457 110544853863501902876593)
                  ·
                    rfl

theorem cell20_242196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_242196 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_242196 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_242196 prefixEnd_242196 := by exact prefixLift 242196
  have htrace : WordTrace (prefixWord ++ tailWord_242196) baseStart_242196 baseEnd_242196 := by
    simpa [prefixWord, tailWord_242196, baseEnd_242196] using wordTrace_append hprefix tailTrace_242196
  have hstable : (prefixWord ++ tailWord_242196).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242196).length < 2 ^ (prefixWord ++ tailWord_242196).sum := by decide
  have hdescent : baseEnd_242196 < baseStart_242196 := by decide
  rcases family_descends (prefixWord ++ tailWord_242196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242231 : List Nat := [1, 1, 3, 1, 2, 3, 5, 1, 3]
def baseStart_242231 : Nat := 118140960795 + 242231 * 2 ^ 59
def prefixEnd_242231 : Nat := 4983230072969 + 3 ^ 40 * 242231 * 2
def baseEnd_242231 : Nat := 110560828817197336709783

theorem tailTrace_242231 : CollatzResearch.WordTrace tailWord_242231 prefixEnd_242231 110560828817197336709783 := by
  unfold tailWord_242231
  simp only [CollatzResearch.WordTrace]
  refine ⟨8834890385445931606294547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5889926923630621070863031 8834890385445931606294547)
  ·
    refine ⟨13252335578168897409441821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8834890385445931606294547 13252335578168897409441821)
    ·
      refine ⟨4969625841813336528540683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13252335578168897409441821 4969625841813336528540683)
      ·
        refine ⟨7454438762720004792811025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4969625841813336528540683 7454438762720004792811025)
        ·
          refine ⟨5590829072040003594608269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7454438762720004792811025 5590829072040003594608269)
          ·
            refine ⟨2096560902015001347978101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5590829072040003594608269 2096560902015001347978101)
            ·
              refine ⟨196552584563906376372947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2096560902015001347978101 196552584563906376372947)
              ·
                refine ⟨294828876845859564559421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196552584563906376372947 294828876845859564559421)
                ·
                  refine ⟨110560828817197336709783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 294828876845859564559421 110560828817197336709783)
                  ·
                    rfl

theorem cell20_242231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 1, 3].length) (baseStart_242231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_242231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_242231 prefixEnd_242231 := by exact prefixLift 242231
  have htrace : WordTrace (prefixWord ++ tailWord_242231) baseStart_242231 baseEnd_242231 := by
    simpa [prefixWord, tailWord_242231, baseEnd_242231] using wordTrace_append hprefix tailTrace_242231
  have hstable : (prefixWord ++ tailWord_242231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242231).length < 2 ^ (prefixWord ++ tailWord_242231).sum := by decide
  have hdescent : baseEnd_242231 < baseStart_242231 := by decide
  rcases family_descends (prefixWord ++ tailWord_242231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242245 : List Nat := [1, 3, 1, 1, 1, 5, 4, 4]
def baseStart_242245 : Nat := 118140960795 + 242245 * 2 ^ 59
def prefixEnd_242245 : Nat := 4983230072969 + 3 ^ 40 * 242245 * 2
def baseEnd_242245 : Nat := 36855739599558503414353

theorem tailTrace_242245 : CollatzResearch.WordTrace tailWord_242245 prefixEnd_242245 36855739599558503414353 := by
  unfold tailWord_242245
  simp only [CollatzResearch.WordTrace]
  refine ⟨8835401007395211997304189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5890267338263474664869459 8835401007395211997304189)
  ·
    refine ⟨3313275377773204498989071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8835401007395211997304189 3313275377773204498989071)
    ·
      refine ⟨4969913066659806748483607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3313275377773204498989071 4969913066659806748483607)
      ·
        refine ⟨7454869599989710122725411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4969913066659806748483607 7454869599989710122725411)
        ·
          refine ⟨11182304399984565184088117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7454869599989710122725411 11182304399984565184088117)
          ·
            refine ⟨1048341037498552986008261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11182304399984565184088117 1048341037498552986008261)
            ·
              refine ⟨196563944530978684876549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1048341037498552986008261 196563944530978684876549)
              ·
                refine ⟨36855739599558503414353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 196563944530978684876549 36855739599558503414353)
                ·
                  rfl

theorem cell20_242245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 4].length) (baseStart_242245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_242245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_242245 prefixEnd_242245 := by exact prefixLift 242245
  have htrace : WordTrace (prefixWord ++ tailWord_242245) baseStart_242245 baseEnd_242245 := by
    simpa [prefixWord, tailWord_242245, baseEnd_242245] using wordTrace_append hprefix tailTrace_242245
  have hstable : (prefixWord ++ tailWord_242245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242245).length < 2 ^ (prefixWord ++ tailWord_242245).sum := by decide
  have hdescent : baseEnd_242245 < baseStart_242245 := by decide
  rcases family_descends (prefixWord ++ tailWord_242245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242286 : List Nat := [4, 1, 2, 2, 2, 1, 4, 1, 3]
def baseStart_242286 : Nat := 118140960795 + 242286 * 2 ^ 59
def prefixEnd_242286 : Nat := 4983230072969 + 3 ^ 40 * 242286 * 2
def baseEnd_242286 : Nat := 110585932315861589876225

theorem tailTrace_242286 : CollatzResearch.WordTrace tailWord_242286 prefixEnd_242286 110585932315861589876225 := by
  unfold tailWord_242286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1104612050030834499943339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5891264266831117333031141 1104612050030834499943339)
  ·
    refine ⟨1656918075046251749915009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1104612050030834499943339 1656918075046251749915009)
    ·
      refine ⟨1242688556284688812436257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1656918075046251749915009 1242688556284688812436257)
      ·
        refine ⟨932016417213516609327193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1242688556284688812436257 932016417213516609327193)
        ·
          refine ⟨699012312910137456995395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 932016417213516609327193 699012312910137456995395)
          ·
            refine ⟨1048518469365206185493093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699012312910137456995395 1048518469365206185493093)
            ·
              refine ⟨196597213005976159779955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1048518469365206185493093 196597213005976159779955)
              ·
                refine ⟨294895819508964239669933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196597213005976159779955 294895819508964239669933)
                ·
                  refine ⟨110585932315861589876225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 294895819508964239669933 110585932315861589876225)
                  ·
                    rfl

theorem cell20_242286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_242286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_242286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_242286 prefixEnd_242286 := by exact prefixLift 242286
  have htrace : WordTrace (prefixWord ++ tailWord_242286) baseStart_242286 baseEnd_242286 := by
    simpa [prefixWord, tailWord_242286, baseEnd_242286] using wordTrace_append hprefix tailTrace_242286
  have hstable : (prefixWord ++ tailWord_242286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242286).length < 2 ^ (prefixWord ++ tailWord_242286).sum := by decide
  have hdescent : baseEnd_242286 < baseStart_242286 := by decide
  rcases family_descends (prefixWord ++ tailWord_242286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242304 : List Nat := [2, 1, 1, 2, 1, 5, 2, 6]
def baseStart_242304 : Nat := 118140960795 + 242304 * 2 ^ 59
def prefixEnd_242304 : Nat := 4983230072969 + 3 ^ 40 * 242304 * 2
def baseEnd_242304 : Nat := 36864716002111175758717

theorem tailTrace_242304 : CollatzResearch.WordTrace tailWord_242304 prefixEnd_242304 36864716002111175758717 := by
  unfold tailWord_242304
  simp only [CollatzResearch.WordTrace]
  refine ⟨4418776457090732536850983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5891701942787643382467977 4418776457090732536850983)
  ·
    refine ⟨6628164685636098805276475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4418776457090732536850983 6628164685636098805276475)
    ·
      refine ⟨9942247028454148207914713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6628164685636098805276475 9942247028454148207914713)
      ·
        refine ⟨7456685271340611155936035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9942247028454148207914713 7456685271340611155936035)
        ·
          refine ⟨11185027907010916733904053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7456685271340611155936035 11185027907010916733904053)
          ·
            refine ⟨1048596366282273443803505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11185027907010916733904053 1048596366282273443803505)
            ·
              refine ⟨786447274711705082852629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1048596366282273443803505 786447274711705082852629)
              ·
                refine ⟨36864716002111175758717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 786447274711705082852629 36864716002111175758717)
                ·
                  rfl

theorem cell20_242304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 6].length) (baseStart_242304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_242304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_242304 prefixEnd_242304 := by exact prefixLift 242304
  have htrace : WordTrace (prefixWord ++ tailWord_242304) baseStart_242304 baseEnd_242304 := by
    simpa [prefixWord, tailWord_242304, baseEnd_242304] using wordTrace_append hprefix tailTrace_242304
  have hstable : (prefixWord ++ tailWord_242304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242304).length < 2 ^ (prefixWord ++ tailWord_242304).sum := by decide
  have hdescent : baseEnd_242304 < baseStart_242304 := by decide
  rcases family_descends (prefixWord ++ tailWord_242304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242324 : List Nat := [2, 4, 2, 2, 1, 2, 2, 2, 3]
def baseStart_242324 : Nat := 118140960795 + 242324 * 2 ^ 59
def prefixEnd_242324 : Nat := 4983230072969 + 3 ^ 40 * 242324 * 2
def baseEnd_242324 : Nat := 110603276551302346609403

theorem tailTrace_242324 : CollatzResearch.WordTrace tailWord_242324 prefixEnd_242324 110603276551302346609403 := by
  unfold tailWord_242324
  simp only [CollatzResearch.WordTrace]
  refine ⟨4419141187054504244715013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5892188249406005659620017 4419141187054504244715013)
  ·
    refine ⟨828588972572719545884065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4419141187054504244715013 828588972572719545884065)
    ·
      refine ⟨621441729429539659413049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 828588972572719545884065 621441729429539659413049)
      ·
        refine ⟨466081297072154744559787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 621441729429539659413049 466081297072154744559787)
        ·
          refine ⟨699121945608232116839681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466081297072154744559787 699121945608232116839681)
          ·
            refine ⟨524341459206174087629761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 699121945608232116839681 524341459206174087629761)
            ·
              refine ⟨393256094404630565722321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 524341459206174087629761 393256094404630565722321)
              ·
                refine ⟨294942070803472924291741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 393256094404630565722321 294942070803472924291741)
                ·
                  refine ⟨110603276551302346609403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 294942070803472924291741 110603276551302346609403)
                  ·
                    rfl

theorem cell20_242324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_242324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_242324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_242324 prefixEnd_242324 := by exact prefixLift 242324
  have htrace : WordTrace (prefixWord ++ tailWord_242324) baseStart_242324 baseEnd_242324 := by
    simpa [prefixWord, tailWord_242324, baseEnd_242324] using wordTrace_append hprefix tailTrace_242324
  have hstable : (prefixWord ++ tailWord_242324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242324).length < 2 ^ (prefixWord ++ tailWord_242324).sum := by decide
  have hdescent : baseEnd_242324 < baseStart_242324 := by decide
  rcases family_descends (prefixWord ++ tailWord_242324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242366 : List Nat := [4, 2, 1, 1, 2, 1, 2, 2, 5]
def baseStart_242366 : Nat := 118140960795 + 242366 * 2 ^ 59
def prefixEnd_242366 : Nat := 4983230072969 + 3 ^ 40 * 242366 * 2
def baseEnd_242366 : Nat := 110622446495736867209231

theorem tailTrace_242366 : CollatzResearch.WordTrace tailWord_242366 prefixEnd_242366 110622446495736867209231 := by
  unfold tailWord_242366
  simp only [CollatzResearch.WordTrace]
  refine ⟨1104976779994606207807369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5893209493304566441639301 1104976779994606207807369)
  ·
    refine ⟨828732584995954655855527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1104976779994606207807369 828732584995954655855527)
    ·
      refine ⟨1243098877493931983783291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 828732584995954655855527 1243098877493931983783291)
      ·
        refine ⟨1864648316240897975674937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1243098877493931983783291 1864648316240897975674937)
        ·
          refine ⟨1398486237180673481756203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1864648316240897975674937 1398486237180673481756203)
          ·
            refine ⟨2097729355771010222634305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1398486237180673481756203 2097729355771010222634305)
            ·
              refine ⟨1573297016828257666975729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2097729355771010222634305 1573297016828257666975729)
              ·
                refine ⟨1179972762621193250231797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1573297016828257666975729 1179972762621193250231797)
                ·
                  refine ⟨110622446495736867209231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1179972762621193250231797 110622446495736867209231)
                  ·
                    rfl

theorem cell20_242366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_242366 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_242366 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_242366 prefixEnd_242366 := by exact prefixLift 242366
  have htrace : WordTrace (prefixWord ++ tailWord_242366) baseStart_242366 baseEnd_242366 := by
    simpa [prefixWord, tailWord_242366, baseEnd_242366] using wordTrace_append hprefix tailTrace_242366
  have hstable : (prefixWord ++ tailWord_242366).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242366).length < 2 ^ (prefixWord ++ tailWord_242366).sum := by decide
  have hdescent : baseEnd_242366 < baseStart_242366 := by decide
  rcases family_descends (prefixWord ++ tailWord_242366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242414 : List Nat := [4, 1, 2, 1, 1, 5, 2, 4]
def baseStart_242414 : Nat := 118140960795 + 242414 * 2 ^ 59
def prefixEnd_242414 : Nat := 4983230072969 + 3 ^ 40 * 242414 * 2
def baseEnd_242414 : Nat := 36881451667887344536345

theorem tailTrace_242414 : CollatzResearch.WordTrace tailWord_242414 prefixEnd_242414 36881451667887344536345 := by
  unfold tailWord_242414
  simp only [CollatzResearch.WordTrace]
  refine ⟨1105195617972869232525787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5894376629188635906804197 1105195617972869232525787)
  ·
    refine ⟨1657793426959303848788681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1105195617972869232525787 1657793426959303848788681)
    ·
      refine ⟨1243345070219477886591511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1657793426959303848788681 1243345070219477886591511)
      ·
        refine ⟨1865017605329216829887267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1243345070219477886591511 1865017605329216829887267)
        ·
          refine ⟨2797526407993825244830901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1865017605329216829887267 2797526407993825244830901)
          ·
            refine ⟨262268100749421116702897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2797526407993825244830901 262268100749421116702897)
            ·
              refine ⟨196701075562065837527173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262268100749421116702897 196701075562065837527173)
              ·
                refine ⟨36881451667887344536345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 196701075562065837527173 36881451667887344536345)
                ·
                  rfl

theorem cell20_242414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_242414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_242414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_242414 prefixEnd_242414 := by exact prefixLift 242414
  have htrace : WordTrace (prefixWord ++ tailWord_242414) baseStart_242414 baseEnd_242414 := by
    simpa [prefixWord, tailWord_242414, baseEnd_242414] using wordTrace_append hprefix tailTrace_242414
  have hstable : (prefixWord ++ tailWord_242414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242414).length < 2 ^ (prefixWord ++ tailWord_242414).sum := by decide
  have hdescent : baseEnd_242414 < baseStart_242414 := by decide
  rcases family_descends (prefixWord ++ tailWord_242414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242420 : List Nat := [2, 6, 1, 1, 2, 2, 1, 3, 2]
def baseStart_242420 : Nat := 118140960795 + 242420 * 2 ^ 59
def prefixEnd_242420 : Nat := 4983230072969 + 3 ^ 40 * 242420 * 2
def baseEnd_242420 : Nat := 110647093567152679409011

theorem tailTrace_242420 : CollatzResearch.WordTrace tailWord_242420 prefixEnd_242420 110647093567152679409011 := by
  unfold tailWord_242420
  simp only [CollatzResearch.WordTrace]
  refine ⟨4420891890880608442462357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5894522521174144589949809 4420891890880608442462357)
  ·
    refine ⟨207229307385028520740423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4420891890880608442462357 207229307385028520740423)
    ·
      refine ⟨310843961077542781110635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207229307385028520740423 310843961077542781110635)
      ·
        refine ⟨466265941616314171665953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310843961077542781110635 466265941616314171665953)
        ·
          refine ⟨349699456212235628749465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 466265941616314171665953 349699456212235628749465)
          ·
            refine ⟨262274592159176721562099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 349699456212235628749465 262274592159176721562099)
            ·
              refine ⟨393411888238765082343149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262274592159176721562099 393411888238765082343149)
              ·
                refine ⟨147529458089536905878681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 393411888238765082343149 147529458089536905878681)
                ·
                  refine ⟨110647093567152679409011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147529458089536905878681 110647093567152679409011)
                  ·
                    rfl

theorem cell20_242420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_242420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_242420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_242420 prefixEnd_242420 := by exact prefixLift 242420
  have htrace : WordTrace (prefixWord ++ tailWord_242420) baseStart_242420 baseEnd_242420 := by
    simpa [prefixWord, tailWord_242420, baseEnd_242420] using wordTrace_append hprefix tailTrace_242420
  have hstable : (prefixWord ++ tailWord_242420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242420).length < 2 ^ (prefixWord ++ tailWord_242420).sum := by decide
  have hdescent : baseEnd_242420 < baseStart_242420 := by decide
  rcases family_descends (prefixWord ++ tailWord_242420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242442 : List Nat := [3, 1, 2, 2, 1, 2, 2, 4, 3]
def baseStart_242442 : Nat := 118140960795 + 242442 * 2 ^ 59
def prefixEnd_242442 : Nat := 4983230072969 + 3 ^ 40 * 242442 * 2
def baseEnd_242442 : Nat := 110657134966618380675587

theorem tailTrace_242442 : CollatzResearch.WordTrace tailWord_242442 prefixEnd_242442 110657134966618380675587 := by
  unfold tailWord_242442
  simp only [CollatzResearch.WordTrace]
  refine ⟨2210646546920378660556395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5895057458454343094817053 2210646546920378660556395)
  ·
    refine ⟨3315969820380567990834593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2210646546920378660556395 3315969820380567990834593)
    ·
      refine ⟨2486977365285425993125945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3315969820380567990834593 2486977365285425993125945)
      ·
        refine ⟨1865233023964069494844459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2486977365285425993125945 1865233023964069494844459)
        ·
          refine ⟨2797849535946104242266689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1865233023964069494844459 2797849535946104242266689)
          ·
            refine ⟨2098387151959578181700017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2797849535946104242266689 2098387151959578181700017)
            ·
              refine ⟨1573790363969683636275013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2098387151959578181700017 1573790363969683636275013)
              ·
                refine ⟨295085693244315681801565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1573790363969683636275013 295085693244315681801565)
                ·
                  refine ⟨110657134966618380675587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 295085693244315681801565 110657134966618380675587)
                  ·
                    rfl

theorem cell20_242442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4, 3].length) (baseStart_242442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_242442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_242442 prefixEnd_242442 := by exact prefixLift 242442
  have htrace : WordTrace (prefixWord ++ tailWord_242442) baseStart_242442 baseEnd_242442 := by
    simpa [prefixWord, tailWord_242442, baseEnd_242442] using wordTrace_append hprefix tailTrace_242442
  have hstable : (prefixWord ++ tailWord_242442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242442).length < 2 ^ (prefixWord ++ tailWord_242442).sum := by decide
  have hdescent : baseEnd_242442 < baseStart_242442 := by decide
  rcases family_descends (prefixWord ++ tailWord_242442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242449 : List Nat := [1, 2, 2, 1, 1, 3, 5, 1, 4]
def baseStart_242449 : Nat := 118140960795 + 242449 * 2 ^ 59
def prefixEnd_242449 : Nat := 4983230072969 + 3 ^ 40 * 242449 * 2
def baseEnd_242449 : Nat := 110660329957357467442225

theorem tailTrace_242449 : CollatzResearch.WordTrace tailWord_242449 prefixEnd_242449 110660329957357467442225 := by
  unfold tailWord_242449
  simp only [CollatzResearch.WordTrace]
  refine ⟨8842841498656154837730401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5895227665770769891820267 8842841498656154837730401)
  ·
    refine ⟨6632131123992116128297801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8842841498656154837730401 6632131123992116128297801)
    ·
      refine ⟨4974098342994087096223351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6632131123992116128297801 4974098342994087096223351)
      ·
        refine ⟨7461147514491130644335027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4974098342994087096223351 7461147514491130644335027)
        ·
          refine ⟨11191721271736695966502541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7461147514491130644335027 11191721271736695966502541)
          ·
            refine ⟨4196895476901260987438453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11191721271736695966502541 4196895476901260987438453)
            ·
              refine ⟨393458950959493217572355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4196895476901260987438453 393458950959493217572355)
              ·
                refine ⟨590188426439239826358533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 393458950959493217572355 590188426439239826358533)
                ·
                  refine ⟨110660329957357467442225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 590188426439239826358533 110660329957357467442225)
                  ·
                    rfl

theorem cell20_242449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 4].length) (baseStart_242449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_242449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_242449 prefixEnd_242449 := by exact prefixLift 242449
  have htrace : WordTrace (prefixWord ++ tailWord_242449) baseStart_242449 baseEnd_242449 := by
    simpa [prefixWord, tailWord_242449, baseEnd_242449] using wordTrace_append hprefix tailTrace_242449
  have hstable : (prefixWord ++ tailWord_242449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242449).length < 2 ^ (prefixWord ++ tailWord_242449).sum := by decide
  have hdescent : baseEnd_242449 < baseStart_242449 := by decide
  rcases family_descends (prefixWord ++ tailWord_242449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242455 : List Nat := [1, 1, 3, 4, 4, 1, 2, 1, 3]
def baseStart_242455 : Nat := 118140960795 + 242455 * 2 ^ 59
def prefixEnd_242455 : Nat := 4983230072969 + 3 ^ 40 * 242455 * 2
def baseEnd_242455 : Nat := 110663068520848113242201

theorem tailTrace_242455 : CollatzResearch.WordTrace tailWord_242455 prefixEnd_242455 110663068520848113242201 := by
  unfold tailWord_242455
  simp only [CollatzResearch.WordTrace]
  refine ⟨8843060336634417862448819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5895373557756278574965879 8843060336634417862448819)
  ·
    refine ⟨13264590504951626793673229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8843060336634417862448819 13264590504951626793673229)
    ·
      refine ⟨4974221439356860047627461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13264590504951626793673229 4974221439356860047627461)
      ·
        refine ⟨932666519879411258930149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4974221439356860047627461 932666519879411258930149)
        ·
          refine ⟨174874972477389611049403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 932666519879411258930149 174874972477389611049403)
          ·
            refine ⟨262312458716084416574105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174874972477389611049403 262312458716084416574105)
            ·
              refine ⟨196734344037063312430579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262312458716084416574105 196734344037063312430579)
              ·
                refine ⟨295101516055594968645869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196734344037063312430579 295101516055594968645869)
                ·
                  refine ⟨110663068520848113242201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 295101516055594968645869 110663068520848113242201)
                  ·
                    rfl

theorem cell20_242455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 1, 3].length) (baseStart_242455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_242455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_242455 prefixEnd_242455 := by exact prefixLift 242455
  have htrace : WordTrace (prefixWord ++ tailWord_242455) baseStart_242455 baseEnd_242455 := by
    simpa [prefixWord, tailWord_242455, baseEnd_242455] using wordTrace_append hprefix tailTrace_242455
  have hstable : (prefixWord ++ tailWord_242455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242455).length < 2 ^ (prefixWord ++ tailWord_242455).sum := by decide
  have hdescent : baseEnd_242455 < baseStart_242455 := by decide
  rcases family_descends (prefixWord ++ tailWord_242455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242494 : List Nat := [4, 2, 1, 2, 11]
def baseStart_242494 : Nat := 118140960795 + 242494 * 2 ^ 59
def prefixEnd_242494 : Nat := 4983230072969 + 3 ^ 40 * 242494 * 2
def baseEnd_242494 : Nat := 1366430483747374209161

theorem tailTrace_242494 : CollatzResearch.WordTrace tailWord_242494 prefixEnd_242494 1366430483747374209161 := by
  unfold tailWord_242494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1105560347936640940389817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5896321855662085015412357 1105560347936640940389817)
  ·
    refine ⟨829170260952480705292363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1105560347936640940389817 829170260952480705292363)
    ·
      refine ⟨1243755391428721057938545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 829170260952480705292363 1243755391428721057938545)
      ·
        refine ⟨932816543571540793453909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1243755391428721057938545 932816543571540793453909)
        ·
          refine ⟨1366430483747374209161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 932816543571540793453909 1366430483747374209161)
          ·
            rfl

theorem cell20_242494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 11].length) (baseStart_242494 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_242494 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_242494 prefixEnd_242494 := by exact prefixLift 242494
  have htrace : WordTrace (prefixWord ++ tailWord_242494) baseStart_242494 baseEnd_242494 := by
    simpa [prefixWord, tailWord_242494, baseEnd_242494] using wordTrace_append hprefix tailTrace_242494
  have hstable : (prefixWord ++ tailWord_242494).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242494).length < 2 ^ (prefixWord ++ tailWord_242494).sum := by decide
  have hdescent : baseEnd_242494 < baseStart_242494 := by decide
  rcases family_descends (prefixWord ++ tailWord_242494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242504 : List Nat := [2, 1, 3, 1, 1, 3, 3, 4, 2]
def baseStart_242504 : Nat := 118140960795 + 242504 * 2 ^ 59
def prefixEnd_242504 : Nat := 4983230072969 + 3 ^ 40 * 242504 * 2
def baseEnd_242504 : Nat := 110685433456021720608667

theorem tailTrace_242504 : CollatzResearch.WordTrace tailWord_242504 prefixEnd_242504 110685433456021720608667 := by
  unfold tailWord_242504
  simp only [CollatzResearch.WordTrace]
  refine ⟨4422423756728449615491283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5896565008971266153988377 4422423756728449615491283)
  ·
    refine ⟨6633635635092674423236925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4422423756728449615491283 6633635635092674423236925)
    ·
      refine ⟨2487613363159752908713847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6633635635092674423236925 2487613363159752908713847)
      ·
        refine ⟨3731420044739629363070771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2487613363159752908713847 3731420044739629363070771)
        ·
          refine ⟨5597130067109444044606157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3731420044739629363070771 5597130067109444044606157)
          ·
            refine ⟨2098923775166041516727309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5597130067109444044606157 2098923775166041516727309)
            ·
              refine ⟨787096415687265568772741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2098923775166041516727309 787096415687265568772741)
              ·
                refine ⟨147580577941362294144889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 787096415687265568772741 147580577941362294144889)
                ·
                  refine ⟨110685433456021720608667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147580577941362294144889 110685433456021720608667)
                  ·
                    rfl

theorem cell20_242504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 4, 2].length) (baseStart_242504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_242504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_242504 prefixEnd_242504 := by exact prefixLift 242504
  have htrace : WordTrace (prefixWord ++ tailWord_242504) baseStart_242504 baseEnd_242504 := by
    simpa [prefixWord, tailWord_242504, baseEnd_242504] using wordTrace_append hprefix tailTrace_242504
  have hstable : (prefixWord ++ tailWord_242504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242504).length < 2 ^ (prefixWord ++ tailWord_242504).sum := by decide
  have hdescent : baseEnd_242504 < baseStart_242504 := by decide
  rcases family_descends (prefixWord ++ tailWord_242504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242563 : List Nat := [1, 1, 1, 3, 4, 1, 4, 1, 4]
def baseStart_242563 : Nat := 118140960795 + 242563 * 2 ^ 59
def prefixEnd_242563 : Nat := 4983230072969 + 3 ^ 40 * 242563 * 2
def baseEnd_242563 : Nat := 110712362663679737641759

theorem tailTrace_242563 : CollatzResearch.WordTrace tailWord_242563 prefixEnd_242563 110712362663679737641759 := by
  unfold tailWord_242563
  simp only [CollatzResearch.WordTrace]
  refine ⟨8846999420243152307380343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5897999613495434871586895 8846999420243152307380343)
  ·
    refine ⟨13270499130364728461070515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8846999420243152307380343 13270499130364728461070515)
    ·
      refine ⟨19905748695547092691605773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13270499130364728461070515 19905748695547092691605773)
      ·
        refine ⟨7464655760830159759352165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19905748695547092691605773 7464655760830159759352165)
        ·
          refine ⟨1399622955155654954878531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7464655760830159759352165 1399622955155654954878531)
          ·
            refine ⟨2099434432733482432317797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1399622955155654954878531 2099434432733482432317797)
            ·
              refine ⟨393643956137527956059587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2099434432733482432317797 393643956137527956059587)
              ·
                refine ⟨590465934206291934089381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 393643956137527956059587 590465934206291934089381)
                ·
                  refine ⟨110712362663679737641759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 590465934206291934089381 110712362663679737641759)
                  ·
                    rfl

theorem cell20_242563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 4].length) (baseStart_242563 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_242563 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_242563 prefixEnd_242563 := by exact prefixLift 242563
  have htrace : WordTrace (prefixWord ++ tailWord_242563) baseStart_242563 baseEnd_242563 := by
    simpa [prefixWord, tailWord_242563, baseEnd_242563] using wordTrace_append hprefix tailTrace_242563
  have hstable : (prefixWord ++ tailWord_242563).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242563).length < 2 ^ (prefixWord ++ tailWord_242563).sum := by decide
  have hdescent : baseEnd_242563 < baseStart_242563 := by decide
  rcases family_descends (prefixWord ++ tailWord_242563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242594 : List Nat := [3, 3, 1, 2, 2, 1, 1, 2, 5]
def baseStart_242594 : Nat := 118140960795 + 242594 * 2 ^ 59
def prefixEnd_242594 : Nat := 4983230072969 + 3 ^ 40 * 242594 * 2
def baseEnd_242594 : Nat := 110726511908381407608299

theorem tailTrace_242594 : CollatzResearch.WordTrace tailWord_242594 prefixEnd_242594 110726511908381407608299 := by
  unfold tailWord_242594
  simp only [CollatzResearch.WordTrace]
  refine ⟨2212032520782711150439709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5898753388753896401172557 2212032520782711150439709)
  ·
    refine ⟨829512195293516681414891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2212032520782711150439709 829512195293516681414891)
    ·
      refine ⟨1244268292940275022122337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 829512195293516681414891 1244268292940275022122337)
      ·
        refine ⟨933201219705206266591753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1244268292940275022122337 933201219705206266591753)
        ·
          refine ⟨699900914778904699943815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 933201219705206266591753 699900914778904699943815)
          ·
            refine ⟨1049851372168357049915723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699900914778904699943815 1049851372168357049915723)
            ·
              refine ⟨1574777058252535574873585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1049851372168357049915723 1574777058252535574873585)
              ·
                refine ⟨1181082793689401681155189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1574777058252535574873585 1181082793689401681155189)
                ·
                  refine ⟨110726511908381407608299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1181082793689401681155189 110726511908381407608299)
                  ·
                    rfl

theorem cell20_242594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_242594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_242594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_242594 prefixEnd_242594 := by exact prefixLift 242594
  have htrace : WordTrace (prefixWord ++ tailWord_242594) baseStart_242594 baseEnd_242594 := by
    simpa [prefixWord, tailWord_242594, baseEnd_242594] using wordTrace_append hprefix tailTrace_242594
  have hstable : (prefixWord ++ tailWord_242594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242594).length < 2 ^ (prefixWord ++ tailWord_242594).sum := by decide
  have hdescent : baseEnd_242594 < baseStart_242594 := by decide
  rcases family_descends (prefixWord ++ tailWord_242594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242615 : List Nat := [1, 1, 3, 1, 3, 1, 4, 1, 5]
def baseStart_242615 : Nat := 118140960795 + 242615 * 2 ^ 59
def prefixEnd_242615 : Nat := 4983230072969 + 3 ^ 40 * 242615 * 2
def baseEnd_242615 : Nat := 110736096880598667908213

theorem tailTrace_242615 : CollatzResearch.WordTrace tailWord_242615 prefixEnd_242615 110736096880598667908213 := by
  unfold tailWord_242615
  simp only [CollatzResearch.WordTrace]
  refine ⟨8848896016054765188273299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5899264010703176792182199 8848896016054765188273299)
  ·
    refine ⟨13273344024082147782409949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8848896016054765188273299 13273344024082147782409949)
    ·
      refine ⟨4977504009030805418403731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13273344024082147782409949 4977504009030805418403731)
      ·
        refine ⟨7466256013546208127605597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4977504009030805418403731 7466256013546208127605597)
        ·
          refine ⟨2799846005079828047852099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7466256013546208127605597 2799846005079828047852099)
          ·
            refine ⟨4199769007619742071778149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2799846005079828047852099 4199769007619742071778149)
            ·
              refine ⟨787456688928701638458403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4199769007619742071778149 787456688928701638458403)
              ·
                refine ⟨1181185033393052457687605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 787456688928701638458403 1181185033393052457687605)
                ·
                  refine ⟨110736096880598667908213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1181185033393052457687605 110736096880598667908213)
                  ·
                    rfl

theorem cell20_242615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 5].length) (baseStart_242615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_242615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_242615 prefixEnd_242615 := by exact prefixLift 242615
  have htrace : WordTrace (prefixWord ++ tailWord_242615) baseStart_242615 baseEnd_242615 := by
    simpa [prefixWord, tailWord_242615, baseEnd_242615] using wordTrace_append hprefix tailTrace_242615
  have hstable : (prefixWord ++ tailWord_242615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242615).length < 2 ^ (prefixWord ++ tailWord_242615).sum := by decide
  have hdescent : baseEnd_242615 < baseStart_242615 := by decide
  rcases family_descends (prefixWord ++ tailWord_242615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242628 : List Nat := [2, 3, 3, 3, 1, 1, 1, 3, 3]
def baseStart_242628 : Nat := 118140960795 + 242628 * 2 ^ 59
def prefixEnd_242628 : Nat := 4983230072969 + 3 ^ 40 * 242628 * 2
def baseEnd_242628 : Nat := 110742030434828400474827

theorem tailTrace_242628 : CollatzResearch.WordTrace tailWord_242628 prefixEnd_242628 110742030434828400474827 := by
  unfold tailWord_242628
  simp only [CollatzResearch.WordTrace]
  refine ⟨4424685082503834204248269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5899580110005112272331025 4424685082503834204248269)
  ·
    refine ⟨1659256905938937826593101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4424685082503834204248269 1659256905938937826593101)
    ·
      refine ⟨622221339727101684972413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1659256905938937826593101 622221339727101684972413)
      ·
        refine ⟨233333002397663131864655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 622221339727101684972413 233333002397663131864655)
        ·
          refine ⟨349999503596494697796983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233333002397663131864655 349999503596494697796983)
          ·
            refine ⟨524999255394742046695475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349999503596494697796983 524999255394742046695475)
            ·
              refine ⟨787498883092113070043213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 524999255394742046695475 787498883092113070043213)
              ·
                refine ⟨295312081159542401266205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 787498883092113070043213 295312081159542401266205)
                ·
                  refine ⟨110742030434828400474827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 295312081159542401266205 110742030434828400474827)
                  ·
                    rfl

theorem cell20_242628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_242628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_242628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_242628 prefixEnd_242628 := by exact prefixLift 242628
  have htrace : WordTrace (prefixWord ++ tailWord_242628) baseStart_242628 baseEnd_242628 := by
    simpa [prefixWord, tailWord_242628, baseEnd_242628] using wordTrace_append hprefix tailTrace_242628
  have hstable : (prefixWord ++ tailWord_242628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242628).length < 2 ^ (prefixWord ++ tailWord_242628).sum := by decide
  have hdescent : baseEnd_242628 < baseStart_242628 := by decide
  rcases family_descends (prefixWord ++ tailWord_242628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242660 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 8]
def baseStart_242660 : Nat := 118140960795 + 242660 * 2 ^ 59
def prefixEnd_242660 : Nat := 4983230072969 + 3 ^ 40 * 242660 * 2
def baseEnd_242660 : Nat := 110756636106778511408029

theorem tailTrace_242660 : CollatzResearch.WordTrace tailWord_242660 prefixEnd_242660 110756636106778511408029 := by
  unfold tailWord_242660
  simp only [CollatzResearch.WordTrace]
  refine ⟨4425268650445868936830717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5900358200594491915774289 4425268650445868936830717)
  ·
    refine ⟨1659475743917200851311519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4425268650445868936830717 1659475743917200851311519)
    ·
      refine ⟨2489213615875801276967279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1659475743917200851311519 2489213615875801276967279)
      ·
        refine ⟨3733820423813701915450919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2489213615875801276967279 3733820423813701915450919)
        ·
          refine ⟨5600730635720552873176379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3733820423813701915450919 5600730635720552873176379)
          ·
            refine ⟨8401095953580829309764569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5600730635720552873176379 8401095953580829309764569)
            ·
              refine ⟨6300821965185621982323427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8401095953580829309764569 6300821965185621982323427)
              ·
                refine ⟨9451232947778432973485141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6300821965185621982323427 9451232947778432973485141)
                ·
                  refine ⟨110756636106778511408029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9451232947778432973485141 110756636106778511408029)
                  ·
                    rfl

theorem cell20_242660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_242660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_242660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_242660 prefixEnd_242660 := by exact prefixLift 242660
  have htrace : WordTrace (prefixWord ++ tailWord_242660) baseStart_242660 baseEnd_242660 := by
    simpa [prefixWord, tailWord_242660, baseEnd_242660] using wordTrace_append hprefix tailTrace_242660
  have hstable : (prefixWord ++ tailWord_242660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242660).length < 2 ^ (prefixWord ++ tailWord_242660).sum := by decide
  have hdescent : baseEnd_242660 < baseStart_242660 := by decide
  rcases family_descends (prefixWord ++ tailWord_242660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242673 : List Nat := [1, 2, 2, 2, 4, 1, 4, 2, 2]
def baseStart_242673 : Nat := 118140960795 + 242673 * 2 ^ 59
def prefixEnd_242673 : Nat := 4983230072969 + 3 ^ 40 * 242673 * 2
def baseEnd_242673 : Nat := 110762569661008243974643

theorem tailTrace_242673 : CollatzResearch.WordTrace tailWord_242673 prefixEnd_242673 110762569661008243974643 := by
  unfold tailWord_242673
  simp only [CollatzResearch.WordTrace]
  refine ⟨8851011449844641093884673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5900674299896427395923115 8851011449844641093884673)
  ·
    refine ⟨6638258587383480820413505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8851011449844641093884673 6638258587383480820413505)
    ·
      refine ⟨4978693940537610615310129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6638258587383480820413505 4978693940537610615310129)
      ·
        refine ⟨3734020455403207961482597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4978693940537610615310129 3734020455403207961482597)
        ·
          refine ⟨700128835388101492777987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3734020455403207961482597 700128835388101492777987)
          ·
            refine ⟨1050193253082152239166981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700128835388101492777987 1050193253082152239166981)
            ·
              refine ⟨196911234952903544843809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1050193253082152239166981 196911234952903544843809)
              ·
                refine ⟨147683426214677658632857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196911234952903544843809 147683426214677658632857)
                ·
                  refine ⟨110762569661008243974643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147683426214677658632857 110762569661008243974643)
                  ·
                    rfl

theorem cell20_242673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 2, 2].length) (baseStart_242673 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_242673 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_242673 prefixEnd_242673 := by exact prefixLift 242673
  have htrace : WordTrace (prefixWord ++ tailWord_242673) baseStart_242673 baseEnd_242673 := by
    simpa [prefixWord, tailWord_242673, baseEnd_242673] using wordTrace_append hprefix tailTrace_242673
  have hstable : (prefixWord ++ tailWord_242673).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242673).length < 2 ^ (prefixWord ++ tailWord_242673).sum := by decide
  have hdescent : baseEnd_242673 < baseStart_242673 := by decide
  rcases family_descends (prefixWord ++ tailWord_242673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242684 : List Nat := [2, 2, 2, 1, 2, 3, 3, 5]
def baseStart_242684 : Nat := 118140960795 + 242684 * 2 ^ 59
def prefixEnd_242684 : Nat := 4983230072969 + 3 ^ 40 * 242684 * 2
def baseEnd_242684 : Nat := 36922530120247031535977

theorem tailTrace_242684 : CollatzResearch.WordTrace tailWord_242684 prefixEnd_242684 36922530120247031535977 := by
  unfold tailWord_242684
  simp only [CollatzResearch.WordTrace]
  refine ⟨4425706326402394986267553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5900941768536526648356737 4425706326402394986267553)
  ·
    refine ⟨3319279744801796239700665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4425706326402394986267553 3319279744801796239700665)
    ·
      refine ⟨2489459808601347179775499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3319279744801796239700665 2489459808601347179775499)
      ·
        refine ⟨3734189712902020769663249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2489459808601347179775499 3734189712902020769663249)
        ·
          refine ⟨2800642284676515577247437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3734189712902020769663249 2800642284676515577247437)
          ·
            refine ⟨1050240856753693341467789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2800642284676515577247437 1050240856753693341467789)
            ·
              refine ⟨393840321282635003050421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1050240856753693341467789 393840321282635003050421)
              ·
                refine ⟨36922530120247031535977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 393840321282635003050421 36922530120247031535977)
                ·
                  rfl

theorem cell20_242684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 5].length) (baseStart_242684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_242684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_242684 prefixEnd_242684 := by exact prefixLift 242684
  have htrace : WordTrace (prefixWord ++ tailWord_242684) baseStart_242684 baseEnd_242684 := by
    simpa [prefixWord, tailWord_242684, baseEnd_242684] using wordTrace_append hprefix tailTrace_242684
  have hstable : (prefixWord ++ tailWord_242684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242684).length < 2 ^ (prefixWord ++ tailWord_242684).sum := by decide
  have hdescent : baseEnd_242684 < baseStart_242684 := by decide
  rcases family_descends (prefixWord ++ tailWord_242684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242705 : List Nat := [1, 2, 2, 1, 1, 2, 1, 10]
def baseStart_242705 : Nat := 118140960795 + 242705 * 2 ^ 59
def prefixEnd_242705 : Nat := 4983230072969 + 3 ^ 40 * 242705 * 2
def baseEnd_242705 : Nat := 36925725110986118302615

theorem tailTrace_242705 : CollatzResearch.WordTrace tailWord_242705 prefixEnd_242705 36925725110986118302615 := by
  unfold tailWord_242705
  simp only [CollatzResearch.WordTrace]
  refine ⟨8852178585728710559049569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5901452390485807039366379 8852178585728710559049569)
  ·
    refine ⟨6639133939296532919287177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8852178585728710559049569 6639133939296532919287177)
    ·
      refine ⟨4979350454472399689465383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6639133939296532919287177 4979350454472399689465383)
      ·
        refine ⟨7469025681708599534198075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4979350454472399689465383 7469025681708599534198075)
        ·
          refine ⟨11203538522562899301297113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7469025681708599534198075 11203538522562899301297113)
          ·
            refine ⟨8402653891922174475972835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11203538522562899301297113 8402653891922174475972835)
            ·
              refine ⟨12603980837883261713959253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8402653891922174475972835 12603980837883261713959253)
              ·
                refine ⟨36925725110986118302615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 12603980837883261713959253 36925725110986118302615)
                ·
                  rfl

theorem cell20_242705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 10].length) (baseStart_242705 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_242705 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_242705 prefixEnd_242705 := by exact prefixLift 242705
  have htrace : WordTrace (prefixWord ++ tailWord_242705) baseStart_242705 baseEnd_242705 := by
    simpa [prefixWord, tailWord_242705, baseEnd_242705] using wordTrace_append hprefix tailTrace_242705
  have hstable : (prefixWord ++ tailWord_242705).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242705).length < 2 ^ (prefixWord ++ tailWord_242705).sum := by decide
  have hdescent : baseEnd_242705 < baseStart_242705 := by decide
  rcases family_descends (prefixWord ++ tailWord_242705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242711 : List Nat := [1, 1, 3, 5, 1, 2, 2, 3, 2]
def baseStart_242711 : Nat := 118140960795 + 242711 * 2 ^ 59
def prefixEnd_242711 : Nat := 4983230072969 + 3 ^ 40 * 242711 * 2
def baseEnd_242711 : Nat := 110779913896449000707821

theorem tailTrace_242711 : CollatzResearch.WordTrace tailWord_242711 prefixEnd_242711 110779913896449000707821 := by
  unfold tailWord_242711
  simp only [CollatzResearch.WordTrace]
  refine ⟨8852397423706973583767987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5901598282471315722511991 8852397423706973583767987)
  ·
    refine ⟨13278596135560460375651981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8852397423706973583767987 13278596135560460375651981)
    ·
      refine ⟨4979473550835172640869493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13278596135560460375651981 4979473550835172640869493)
      ·
        refine ⟨466825645390797435081515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4979473550835172640869493 466825645390797435081515)
        ·
          refine ⟨700238468086196152622273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466825645390797435081515 700238468086196152622273)
          ·
            refine ⟨525178851064647114466705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 700238468086196152622273 525178851064647114466705)
            ·
              refine ⟨393884138298485335850029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 525178851064647114466705 393884138298485335850029)
              ·
                refine ⟨147706551861932000943761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 393884138298485335850029 147706551861932000943761)
                ·
                  refine ⟨110779913896449000707821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147706551861932000943761 110779913896449000707821)
                  ·
                    rfl

theorem cell20_242711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 3, 2].length) (baseStart_242711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_242711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_242711 prefixEnd_242711 := by exact prefixLift 242711
  have htrace : WordTrace (prefixWord ++ tailWord_242711) baseStart_242711 baseEnd_242711 := by
    simpa [prefixWord, tailWord_242711, baseEnd_242711] using wordTrace_append hprefix tailTrace_242711
  have hstable : (prefixWord ++ tailWord_242711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242711).length < 2 ^ (prefixWord ++ tailWord_242711).sum := by decide
  have hdescent : baseEnd_242711 < baseStart_242711 := by decide
  rcases family_descends (prefixWord ++ tailWord_242711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242722 : List Nat := [3, 3, 1, 1, 1, 4, 7]
def baseStart_242722 : Nat := 118140960795 + 242722 * 2 ^ 59
def prefixEnd_242722 : Nat := 4983230072969 + 3 ^ 40 * 242722 * 2
def baseEnd_242722 : Nat := 12309437177353539037901

theorem tailTrace_242722 : CollatzResearch.WordTrace tailWord_242722 prefixEnd_242722 12309437177353539037901 := by
  unfold tailWord_242722
  simp only [CollatzResearch.WordTrace]
  refine ⟨2213199656666780615604605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5901865751111414974945613 2213199656666780615604605)
  ·
    refine ⟨829949871250042730851727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2213199656666780615604605 829949871250042730851727)
    ·
      refine ⟨1244924806875064096277591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 829949871250042730851727 1244924806875064096277591)
      ·
        refine ⟨1867387210312596144416387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1244924806875064096277591 1867387210312596144416387)
        ·
          refine ⟨2801080815468894216624581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1867387210312596144416387 2801080815468894216624581)
          ·
            refine ⟨525202652900417665617109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2801080815468894216624581 525202652900417665617109)
            ·
              refine ⟨12309437177353539037901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 525202652900417665617109 12309437177353539037901)
              ·
                rfl

theorem cell20_242722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 7].length) (baseStart_242722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_242722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_242722 prefixEnd_242722 := by exact prefixLift 242722
  have htrace : WordTrace (prefixWord ++ tailWord_242722) baseStart_242722 baseEnd_242722 := by
    simpa [prefixWord, tailWord_242722, baseEnd_242722] using wordTrace_append hprefix tailTrace_242722
  have hstable : (prefixWord ++ tailWord_242722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242722).length < 2 ^ (prefixWord ++ tailWord_242722).sum := by decide
  have hdescent : baseEnd_242722 < baseStart_242722 := by decide
  rcases family_descends (prefixWord ++ tailWord_242722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242742 : List Nat := [5, 1, 2, 1, 1, 3, 3, 1, 3]
def baseStart_242742 : Nat := 118140960795 + 242742 * 2 ^ 59
def prefixEnd_242742 : Nat := 4983230072969 + 3 ^ 40 * 242742 * 2
def baseEnd_242742 : Nat := 110794063141150670674361

theorem tailTrace_242742 : CollatzResearch.WordTrace tailWord_242742 prefixEnd_242742 110794063141150670674361 := by
  unfold tailWord_242742
  simp only [CollatzResearch.WordTrace]
  refine ⟨553345505412166617384155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5902352057729777252097653 553345505412166617384155)
  ·
    refine ⟨830018258118249926076233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 553345505412166617384155 830018258118249926076233)
    ·
      refine ⟨622513693588687444557175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 830018258118249926076233 622513693588687444557175)
      ·
        refine ⟨933770540383031166835763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622513693588687444557175 933770540383031166835763)
        ·
          refine ⟨1400655810574546750253645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 933770540383031166835763 1400655810574546750253645)
          ·
            refine ⟨525245928965455031345117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1400655810574546750253645 525245928965455031345117)
            ·
              refine ⟨196967223362045636754419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 525245928965455031345117 196967223362045636754419)
              ·
                refine ⟨295450835043068455131629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196967223362045636754419 295450835043068455131629)
                ·
                  refine ⟨110794063141150670674361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 295450835043068455131629 110794063141150670674361)
                  ·
                    rfl

theorem cell20_242742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_242742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_242742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_242742 prefixEnd_242742 := by exact prefixLift 242742
  have htrace : WordTrace (prefixWord ++ tailWord_242742) baseStart_242742 baseEnd_242742 := by
    simpa [prefixWord, tailWord_242742, baseEnd_242742] using wordTrace_append hprefix tailTrace_242742
  have hstable : (prefixWord ++ tailWord_242742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242742).length < 2 ^ (prefixWord ++ tailWord_242742).sum := by decide
  have hdescent : baseEnd_242742 < baseStart_242742 := by decide
  rcases family_descends (prefixWord ++ tailWord_242742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242743 : List Nat := [1, 1, 3, 1, 2, 2, 1, 9]
def baseStart_242743 : Nat := 118140960795 + 242743 * 2 ^ 59
def prefixEnd_242743 : Nat := 4983230072969 + 3 ^ 40 * 242743 * 2
def baseEnd_242743 : Nat := 36931506522799703880341

theorem tailTrace_242743 : CollatzResearch.WordTrace tailWord_242743 prefixEnd_242743 36931506522799703880341 := by
  unfold tailWord_242743
  simp only [CollatzResearch.WordTrace]
  refine ⟨8853564559591043048932883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5902376373060695365955255 8853564559591043048932883)
  ·
    refine ⟨13280346839386564573399325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8853564559591043048932883 13280346839386564573399325)
    ·
      refine ⟨4980130064769961715024747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13280346839386564573399325 4980130064769961715024747)
      ·
        refine ⟨7470195097154942572537121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4980130064769961715024747 7470195097154942572537121)
        ·
          refine ⟨5602646322866206929402841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7470195097154942572537121 5602646322866206929402841)
          ·
            refine ⟨4201984742149655197052131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5602646322866206929402841 4201984742149655197052131)
            ·
              refine ⟨6302977113224482795578197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4201984742149655197052131 6302977113224482795578197)
              ·
                refine ⟨36931506522799703880341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6302977113224482795578197 36931506522799703880341)
                ·
                  rfl

theorem cell20_242743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 9].length) (baseStart_242743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_242743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_242743 prefixEnd_242743 := by exact prefixLift 242743
  have htrace : WordTrace (prefixWord ++ tailWord_242743) baseStart_242743 baseEnd_242743 := by
    simpa [prefixWord, tailWord_242743, baseEnd_242743] using wordTrace_append hprefix tailTrace_242743
  have hstable : (prefixWord ++ tailWord_242743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242743).length < 2 ^ (prefixWord ++ tailWord_242743).sum := by decide
  have hdescent : baseEnd_242743 < baseStart_242743 := by decide
  rcases family_descends (prefixWord ++ tailWord_242743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242791 : List Nat := [1, 1, 5, 1, 1, 3, 3, 1, 4]
def baseStart_242791 : Nat := 118140960795 + 242791 * 2 ^ 59
def prefixEnd_242791 : Nat := 4983230072969 + 3 ^ 40 * 242791 * 2
def baseEnd_242791 : Nat := 110816428076324278040827

theorem tailTrace_242791 : CollatzResearch.WordTrace tailWord_242791 prefixEnd_242791 110816428076324278040827 := by
  unfold tailWord_242791
  simp only [CollatzResearch.WordTrace]
  refine ⟨8855315263417147246680227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5903543508944764831120151 8855315263417147246680227)
  ·
    refine ⟨13282972895125720870020341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8855315263417147246680227 13282972895125720870020341)
    ·
      refine ⟨1245278708918036331564407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13282972895125720870020341 1245278708918036331564407)
      ·
        refine ⟨1867918063377054497346611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1245278708918036331564407 1867918063377054497346611)
        ·
          refine ⟨2801877095065581746019917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1867918063377054497346611 2801877095065581746019917)
          ·
            refine ⟨1050703910649593154757469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2801877095065581746019917 1050703910649593154757469)
            ·
              refine ⟨394013966493597433034051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1050703910649593154757469 394013966493597433034051)
              ·
                refine ⟨591020949740396149551077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 394013966493597433034051 591020949740396149551077)
                ·
                  refine ⟨110816428076324278040827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 591020949740396149551077 110816428076324278040827)
                  ·
                    rfl

theorem cell20_242791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 4].length) (baseStart_242791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_242791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_242791 prefixEnd_242791 := by exact prefixLift 242791
  have htrace : WordTrace (prefixWord ++ tailWord_242791) baseStart_242791 baseEnd_242791 := by
    simpa [prefixWord, tailWord_242791, baseEnd_242791] using wordTrace_append hprefix tailTrace_242791
  have hstable : (prefixWord ++ tailWord_242791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242791).length < 2 ^ (prefixWord ++ tailWord_242791).sum := by decide
  have hdescent : baseEnd_242791 < baseStart_242791 := by decide
  rcases family_descends (prefixWord ++ tailWord_242791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242798 : List Nat := [4, 1, 2, 2, 1, 2, 1, 7]
def baseStart_242798 : Nat := 118140960795 + 242798 * 2 ^ 59
def prefixEnd_242798 : Nat := 4983230072969 + 3 ^ 40 * 242798 * 2
def baseEnd_242798 : Nat := 36939874355687788269155

theorem tailTrace_242798 : CollatzResearch.WordTrace tailWord_242798 prefixEnd_242798 36939874355687788269155 := by
  unfold tailWord_242798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1106946321798973430273131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5903713716261191628123365 1106946321798973430273131)
  ·
    refine ⟨1660419482698460145409697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1106946321798973430273131 1660419482698460145409697)
    ·
      refine ⟨1245314612023845109057273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1660419482698460145409697 1245314612023845109057273)
      ·
        refine ⟨933985959017883831792955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1245314612023845109057273 933985959017883831792955)
        ·
          refine ⟨1400978938526825747689433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 933985959017883831792955 1400978938526825747689433)
          ·
            refine ⟨1050734203895119310767075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1400978938526825747689433 1050734203895119310767075)
            ·
              refine ⟨1576101305842678966150613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1050734203895119310767075 1576101305842678966150613)
              ·
                refine ⟨36939874355687788269155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1576101305842678966150613 36939874355687788269155)
                ·
                  rfl

theorem cell20_242798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_242798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_242798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_242798 prefixEnd_242798 := by exact prefixLift 242798
  have htrace : WordTrace (prefixWord ++ tailWord_242798) baseStart_242798 baseEnd_242798 := by
    simpa [prefixWord, tailWord_242798, baseEnd_242798] using wordTrace_append hprefix tailTrace_242798
  have hstable : (prefixWord ++ tailWord_242798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242798).length < 2 ^ (prefixWord ++ tailWord_242798).sum := by decide
  have hdescent : baseEnd_242798 < baseStart_242798 := by decide
  rcases family_descends (prefixWord ++ tailWord_242798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242812 : List Nat := [2, 2, 2, 1, 1, 3, 2, 1, 6]
def baseStart_242812 : Nat := 118140960795 + 242812 * 2 ^ 59
def prefixEnd_242812 : Nat := 4983230072969 + 3 ^ 40 * 242812 * 2
def baseEnd_242812 : Nat := 110826013048541538340741

theorem tailTrace_242812 : CollatzResearch.WordTrace tailWord_242812 prefixEnd_242812 110826013048541538340741 := by
  unfold tailWord_242812
  simp only [CollatzResearch.WordTrace]
  refine ⟨4428040598170533916597345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5904054130894045222129793 4428040598170533916597345)
  ·
    refine ⟨3321030448627900437448009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4428040598170533916597345 3321030448627900437448009)
    ·
      refine ⟨2490772836470925328086007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3321030448627900437448009 2490772836470925328086007)
      ·
        refine ⟨3736159254706387992129011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2490772836470925328086007 3736159254706387992129011)
        ·
          refine ⟨5604238882059581988193517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3736159254706387992129011 5604238882059581988193517)
          ·
            refine ⟨2101589580772343245572569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5604238882059581988193517 2101589580772343245572569)
            ·
              refine ⟨1576192185579257434179427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2101589580772343245572569 1576192185579257434179427)
              ·
                refine ⟨2364288278368886151269141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1576192185579257434179427 2364288278368886151269141)
                ·
                  refine ⟨110826013048541538340741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2364288278368886151269141 110826013048541538340741)
                  ·
                    rfl

theorem cell20_242812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_242812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_242812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_242812 prefixEnd_242812 := by exact prefixLift 242812
  have htrace : WordTrace (prefixWord ++ tailWord_242812) baseStart_242812 baseEnd_242812 := by
    simpa [prefixWord, tailWord_242812, baseEnd_242812] using wordTrace_append hprefix tailTrace_242812
  have hstable : (prefixWord ++ tailWord_242812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242812).length < 2 ^ (prefixWord ++ tailWord_242812).sum := by decide
  have hdescent : baseEnd_242812 < baseStart_242812 := by decide
  rcases family_descends (prefixWord ++ tailWord_242812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242819 : List Nat := [1, 1, 1, 3, 3, 2, 1, 8]
def baseStart_242819 : Nat := 118140960795 + 242819 * 2 ^ 59
def prefixEnd_242819 : Nat := 4983230072969 + 3 ^ 40 * 242819 * 2
def baseEnd_242819 : Nat := 36943069346426875035793

theorem tailTrace_242819 : CollatzResearch.WordTrace tailWord_242819 prefixEnd_242819 36943069346426875035793 := by
  unfold tailWord_242819
  simp only [CollatzResearch.WordTrace]
  refine ⟨8856336507315708028699511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5904224338210472019133007 8856336507315708028699511)
  ·
    refine ⟨13284504760973562043049267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8856336507315708028699511 13284504760973562043049267)
    ·
      refine ⟨19926757141460343064573901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13284504760973562043049267 19926757141460343064573901)
      ·
        refine ⟨7472533928047628649215213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19926757141460343064573901 7472533928047628649215213)
        ·
          refine ⟨2802200223017860743455705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7472533928047628649215213 2802200223017860743455705)
          ·
            refine ⟨2101650167263395557591779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2802200223017860743455705 2101650167263395557591779)
            ·
              refine ⟨3152475250895093336387669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2101650167263395557591779 3152475250895093336387669)
              ·
                refine ⟨36943069346426875035793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3152475250895093336387669 36943069346426875035793)
                ·
                  rfl

theorem cell20_242819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 8].length) (baseStart_242819 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_242819 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_242819 prefixEnd_242819 := by exact prefixLift 242819
  have htrace : WordTrace (prefixWord ++ tailWord_242819) baseStart_242819 baseEnd_242819 := by
    simpa [prefixWord, tailWord_242819, baseEnd_242819] using wordTrace_append hprefix tailTrace_242819
  have hstable : (prefixWord ++ tailWord_242819).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242819).length < 2 ^ (prefixWord ++ tailWord_242819).sum := by decide
  have hdescent : baseEnd_242819 < baseStart_242819 := by decide
  rcases family_descends (prefixWord ++ tailWord_242819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242842 : List Nat := [3, 1, 1, 5, 1, 3, 2, 2, 2]
def baseStart_242842 : Nat := 118140960795 + 242842 * 2 ^ 59
def prefixEnd_242842 : Nat := 4983230072969 + 3 ^ 40 * 242842 * 2
def baseEnd_242842 : Nat := 110839705865994767340619

theorem tailTrace_242842 : CollatzResearch.WordTrace tailWord_242842 prefixEnd_242842 110839705865994767340619 := by
  unfold tailWord_242842
  simp only [CollatzResearch.WordTrace]
  refine ⟨2214293846558095739196695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5904783590821588637857853 2214293846558095739196695)
  ·
    refine ⟨3321440769837143608795043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2214293846558095739196695 3321440769837143608795043)
    ·
      refine ⟨4982161154755715413192565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3321440769837143608795043 4982161154755715413192565)
      ·
        refine ⟨467077608258348319986803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4982161154755715413192565 467077608258348319986803)
        ·
          refine ⟨700616412387522479980205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467077608258348319986803 700616412387522479980205)
          ·
            refine ⟨262731154645320929992577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 700616412387522479980205 262731154645320929992577)
            ·
              refine ⟨197048365983990697494433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262731154645320929992577 197048365983990697494433)
              ·
                refine ⟨147786274487993023120825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197048365983990697494433 147786274487993023120825)
                ·
                  refine ⟨110839705865994767340619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147786274487993023120825 110839705865994767340619)
                  ·
                    rfl

theorem cell20_242842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 2, 2].length) (baseStart_242842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_242842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_242842 prefixEnd_242842 := by exact prefixLift 242842
  have htrace : WordTrace (prefixWord ++ tailWord_242842) baseStart_242842 baseEnd_242842 := by
    simpa [prefixWord, tailWord_242842, baseEnd_242842] using wordTrace_append hprefix tailTrace_242842
  have hstable : (prefixWord ++ tailWord_242842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242842).length < 2 ^ (prefixWord ++ tailWord_242842).sum := by decide
  have hdescent : baseEnd_242842 < baseStart_242842 := by decide
  rcases family_descends (prefixWord ++ tailWord_242842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242894 : List Nat := [4, 1, 1, 1, 6, 1, 1, 2, 3]
def baseStart_242894 : Nat := 118140960795 + 242894 * 2 ^ 59
def prefixEnd_242894 : Nat := 4983230072969 + 3 ^ 40 * 242894 * 2
def baseEnd_242894 : Nat := 110863440082913697607073

theorem tailTrace_242894 : CollatzResearch.WordTrace tailWord_242894 prefixEnd_242894 110863440082913697607073 := by
  unfold tailWord_242894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1107383997755499479709967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5906047988029330558453157 1107383997755499479709967)
  ·
    refine ⟨1661075996633249219564951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1107383997755499479709967 1661075996633249219564951)
    ·
      refine ⟨2491613994949873829347427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1661075996633249219564951 2491613994949873829347427)
      ·
        refine ⟨3737420992424810744021141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2491613994949873829347427 3737420992424810744021141)
        ·
          refine ⟨175191609019913003625991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3737420992424810744021141 175191609019913003625991)
          ·
            refine ⟨262787413529869505438987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175191609019913003625991 262787413529869505438987)
            ·
              refine ⟨394181120294804258158481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262787413529869505438987 394181120294804258158481)
              ·
                refine ⟨295635840221103193618861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 394181120294804258158481 295635840221103193618861)
                ·
                  refine ⟨110863440082913697607073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 295635840221103193618861 110863440082913697607073)
                  ·
                    rfl

theorem cell20_242894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 2, 3].length) (baseStart_242894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_242894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_242894 prefixEnd_242894 := by exact prefixLift 242894
  have htrace : WordTrace (prefixWord ++ tailWord_242894) baseStart_242894 baseEnd_242894 := by
    simpa [prefixWord, tailWord_242894, baseEnd_242894] using wordTrace_append hprefix tailTrace_242894
  have hstable : (prefixWord ++ tailWord_242894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242894).length < 2 ^ (prefixWord ++ tailWord_242894).sum := by decide
  have hdescent : baseEnd_242894 < baseStart_242894 := by decide
  rcases family_descends (prefixWord ++ tailWord_242894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242946 : List Nat := [3, 4, 1, 1, 4, 1, 6]
def baseStart_242946 : Nat := 118140960795 + 242946 * 2 ^ 59
def prefixEnd_242946 : Nat := 4983230072969 + 3 ^ 40 * 242946 * 2
def baseEnd_242946 : Nat := 12320797144425847541503

theorem tailTrace_242946 : CollatzResearch.WordTrace tailWord_242946 prefixEnd_242946 12320797144425847541503 := by
  unfold tailWord_242946
  simp only [CollatzResearch.WordTrace]
  refine ⟨2215242144463902179643173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5907312385237072479048461 2215242144463902179643173)
  ·
    refine ⟨415357902086981658683095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2215242144463902179643173 415357902086981658683095)
    ·
      refine ⟨623036853130472488024643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415357902086981658683095 623036853130472488024643)
      ·
        refine ⟨934555279695708732036965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 623036853130472488024643 934555279695708732036965)
        ·
          refine ⟨175229114942945387256931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 934555279695708732036965 175229114942945387256931)
          ·
            refine ⟨262843672414418080885397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175229114942945387256931 262843672414418080885397)
            ·
              refine ⟨12320797144425847541503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 262843672414418080885397 12320797144425847541503)
              ·
                rfl

theorem cell20_242946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 6].length) (baseStart_242946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_242946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_242946 prefixEnd_242946 := by exact prefixLift 242946
  have htrace : WordTrace (prefixWord ++ tailWord_242946) baseStart_242946 baseEnd_242946 := by
    simpa [prefixWord, tailWord_242946, baseEnd_242946] using wordTrace_append hprefix tailTrace_242946
  have hstable : (prefixWord ++ tailWord_242946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242946).length < 2 ^ (prefixWord ++ tailWord_242946).sum := by decide
  have hdescent : baseEnd_242946 < baseStart_242946 := by decide
  rcases family_descends (prefixWord ++ tailWord_242946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243005 : List Nat := [1, 4, 1, 5, 2, 7]
def baseStart_243005 : Nat := 118140960795 + 243005 * 2 ^ 59
def prefixEnd_243005 : Nat := 4983230072969 + 3 ^ 40 * 243005 * 2
def baseEnd_243005 : Nat := 4107929759536690552097

theorem tailTrace_243005 : CollatzResearch.WordTrace tailWord_243005 prefixEnd_243005 4107929759536690552097 := by
  unfold tailWord_243005
  simp only [CollatzResearch.WordTrace]
  refine ⟨8863120484641861794970469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5908746989761241196646979 8863120484641861794970469)
  ·
    refine ⟨1661835090870349086556963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8863120484641861794970469 1661835090870349086556963)
    ·
      refine ⟨2492752636305523629835445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1661835090870349086556963 2492752636305523629835445)
      ·
        refine ⟨233695559653642840297073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2492752636305523629835445 233695559653642840297073)
        ·
          refine ⟨175271669740232130222805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233695559653642840297073 175271669740232130222805)
          ·
            refine ⟨4107929759536690552097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 175271669740232130222805 4107929759536690552097)
            ·
              rfl

theorem cell20_243005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 7].length) (baseStart_243005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243005 prefixEnd_243005 := by exact prefixLift 243005
  have htrace : WordTrace (prefixWord ++ tailWord_243005) baseStart_243005 baseEnd_243005 := by
    simpa [prefixWord, tailWord_243005, baseEnd_243005] using wordTrace_append hprefix tailTrace_243005
  have hstable : (prefixWord ++ tailWord_243005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243005).length < 2 ^ (prefixWord ++ tailWord_243005).sum := by decide
  have hdescent : baseEnd_243005 < baseStart_243005 := by decide
  rcases family_descends (prefixWord ++ tailWord_243005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243015 : List Nat := [1, 1, 4, 1, 2, 5, 2, 2, 2]
def baseStart_243015 : Nat := 118140960795 + 243015 * 2 ^ 59
def prefixEnd_243015 : Nat := 4983230072969 + 3 ^ 40 * 243015 * 2
def baseEnd_243015 : Nat := 110918667779975054573245

theorem tailTrace_243015 : CollatzResearch.WordTrace tailWord_243015 prefixEnd_243015 110918667779975054573245 := by
  unfold tailWord_243015
  simp only [CollatzResearch.WordTrace]
  refine ⟨8863485214605633502834499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5908990143070422335222999 8863485214605633502834499)
  ·
    refine ⟨13295227821908450254251749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8863485214605633502834499 13295227821908450254251749)
    ·
      refine ⟨2492855216607834422672203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13295227821908450254251749 2492855216607834422672203)
      ·
        refine ⟨3739282824911751634008305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2492855216607834422672203 3739282824911751634008305)
        ·
          refine ⟨2804462118683813725506229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3739282824911751634008305 2804462118683813725506229)
          ·
            refine ⟨262918323626607536766209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2804462118683813725506229 262918323626607536766209)
            ·
              refine ⟨197188742719955652574657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262918323626607536766209 197188742719955652574657)
              ·
                refine ⟨147891557039966739430993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197188742719955652574657 147891557039966739430993)
                ·
                  refine ⟨110918667779975054573245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147891557039966739430993 110918667779975054573245)
                  ·
                    rfl

theorem cell20_243015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 2, 2].length) (baseStart_243015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243015 prefixEnd_243015 := by exact prefixLift 243015
  have htrace : WordTrace (prefixWord ++ tailWord_243015) baseStart_243015 baseEnd_243015 := by
    simpa [prefixWord, tailWord_243015, baseEnd_243015] using wordTrace_append hprefix tailTrace_243015
  have hstable : (prefixWord ++ tailWord_243015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243015).length < 2 ^ (prefixWord ++ tailWord_243015).sum := by decide
  have hdescent : baseEnd_243015 < baseStart_243015 := by decide
  rcases family_descends (prefixWord ++ tailWord_243015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243033 : List Nat := [1, 2, 1, 2, 2, 2, 4, 3, 3]
def baseStart_243033 : Nat := 118140960795 + 243033 * 2 ^ 59
def prefixEnd_243033 : Nat := 4983230072969 + 3 ^ 40 * 243033 * 2
def baseEnd_243033 : Nat := 110926883470446991973171

theorem tailTrace_243033 : CollatzResearch.WordTrace tailWord_243033 prefixEnd_243033 110926883470446991973171 := by
  unfold tailWord_243033
  simp only [CollatzResearch.WordTrace]
  refine ⟨8864141728540422576989753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5909427819026948384659835 8864141728540422576989753)
  ·
    refine ⟨6648106296405316932742315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8864141728540422576989753 6648106296405316932742315)
    ·
      refine ⟨9972159444607975399113473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6648106296405316932742315 9972159444607975399113473)
      ·
        refine ⟨7479119583455981549335105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9972159444607975399113473 7479119583455981549335105)
        ·
          refine ⟨5609339687591986162001329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7479119583455981549335105 5609339687591986162001329)
          ·
            refine ⟨4207004765693989621500997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5609339687591986162001329 4207004765693989621500997)
            ·
              refine ⟨788813393567623054031437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4207004765693989621500997 788813393567623054031437)
              ·
                refine ⟨295805022587858645261789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 788813393567623054031437 295805022587858645261789)
                ·
                  refine ⟨110926883470446991973171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 295805022587858645261789 110926883470446991973171)
                  ·
                    rfl

theorem cell20_243033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3, 3].length) (baseStart_243033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243033 prefixEnd_243033 := by exact prefixLift 243033
  have htrace : WordTrace (prefixWord ++ tailWord_243033) baseStart_243033 baseEnd_243033 := by
    simpa [prefixWord, tailWord_243033, baseEnd_243033] using wordTrace_append hprefix tailTrace_243033
  have hstable : (prefixWord ++ tailWord_243033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243033).length < 2 ^ (prefixWord ++ tailWord_243033).sum := by decide
  have hdescent : baseEnd_243033 < baseStart_243033 := by decide
  rcases family_descends (prefixWord ++ tailWord_243033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
