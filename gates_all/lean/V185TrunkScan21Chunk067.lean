import V185TrunkScan21Chunk066

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_811533 : List Nat := [1, 7, 1, 1, 1, 1, 4, 2, 3]
def baseStart_811533 : Nat := 118140960795 + 811533 * 2 ^ 59
def prefixEnd_811533 : Nat := 4983230072969 + 3 ^ 40 * 811533 * 2
def baseEnd_811533 : Nat := 185202887104568269824593

theorem tailTrace_811533 : CollatzResearch.WordTrace tailWord_811533 prefixEnd_811533 185202887104568269824593 := by
  unfold tailWord_811533
  simp only [CollatzResearch.WordTrace]
  refine ⟨29599040168962014647095253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19732693445974676431396835 29599040168962014647095253)
  ·
    refine ⟨693727503960047218291295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 29599040168962014647095253 693727503960047218291295)
    ·
      refine ⟨1040591255940070827436943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 693727503960047218291295 1040591255940070827436943)
      ·
        refine ⟨1560886883910106241155415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1040591255940070827436943 1560886883910106241155415)
        ·
          refine ⟨2341330325865159361733123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1560886883910106241155415 2341330325865159361733123)
          ·
            refine ⟨3511995488797739042599685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2341330325865159361733123 3511995488797739042599685)
            ·
              refine ⟨658499154149576070487441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3511995488797739042599685 658499154149576070487441)
              ·
                refine ⟨493874365612182052865581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 658499154149576070487441 493874365612182052865581)
                ·
                  refine ⟨185202887104568269824593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 493874365612182052865581 185202887104568269824593)
                  ·
                    rfl

theorem cell21_811533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_811533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_811533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_811533 prefixEnd_811533 := by exact prefixLift 811533
  have htrace : WordTrace (prefixWord ++ tailWord_811533) baseStart_811533 baseEnd_811533 := by
    simpa [prefixWord, tailWord_811533, baseEnd_811533] using wordTrace_append hprefix tailTrace_811533
  have hstable : (prefixWord ++ tailWord_811533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811533).length < 2 ^ (prefixWord ++ tailWord_811533).sum := by decide
  have hdescent : baseEnd_811533 < baseStart_811533 := by decide
  rcases family_descends (prefixWord ++ tailWord_811533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811569 : List Nat := [1, 2, 2, 3, 1, 1, 2, 9]
def baseStart_811569 : Nat := 118140960795 + 811569 * 2 ^ 59
def prefixEnd_811569 : Nat := 4983230072969 + 3 ^ 40 * 811569 * 2
def baseEnd_811569 : Nat := 61737034265013402408173

theorem tailTrace_811569 : CollatzResearch.WordTrace tailWord_811569 prefixEnd_811569 61737034265013402408173 := by
  unfold tailWord_811569
  simp only [CollatzResearch.WordTrace]
  refine ⟨29600353196831592795405761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19733568797887728530270507 29600353196831592795405761)
  ·
    refine ⟨22200264897623694596554321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29600353196831592795405761 22200264897623694596554321)
    ·
      refine ⟨16650198673217770947415741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22200264897623694596554321 16650198673217770947415741)
      ·
        refine ⟨6243824502456664105280903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16650198673217770947415741 6243824502456664105280903)
        ·
          refine ⟨9365736753684996157921355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6243824502456664105280903 9365736753684996157921355)
          ·
            refine ⟨14048605130527494236882033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9365736753684996157921355 14048605130527494236882033)
            ·
              refine ⟨10536453847895620677661525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14048605130527494236882033 10536453847895620677661525)
              ·
                refine ⟨61737034265013402408173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10536453847895620677661525 61737034265013402408173)
                ·
                  rfl

theorem cell21_811569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 9].length) (baseStart_811569 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_811569 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_811569 prefixEnd_811569 := by exact prefixLift 811569
  have htrace : WordTrace (prefixWord ++ tailWord_811569) baseStart_811569 baseEnd_811569 := by
    simpa [prefixWord, tailWord_811569, baseEnd_811569] using wordTrace_append hprefix tailTrace_811569
  have hstable : (prefixWord ++ tailWord_811569).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811569).length < 2 ^ (prefixWord ++ tailWord_811569).sum := by decide
  have hdescent : baseEnd_811569 < baseStart_811569 := by decide
  rcases family_descends (prefixWord ++ tailWord_811569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811662 : List Nat := [4, 1, 1, 3, 1, 1, 4, 6]
def baseStart_811662 : Nat := 118140960795 + 811662 * 2 ^ 59
def prefixEnd_811662 : Nat := 4983230072969 + 3 ^ 40 * 811662 * 2
def baseEnd_811662 : Nat := 61744108887364237391443

theorem tailTrace_811662 : CollatzResearch.WordTrace tailWord_811662 prefixEnd_811662 61744108887364237391443 := by
  unfold tailWord_811662
  simp only [CollatzResearch.WordTrace]
  refine ⟨3700468148186833709817655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19735830123663113119027493 3700468148186833709817655)
  ·
    refine ⟨5550702222280250564726483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3700468148186833709817655 5550702222280250564726483)
    ·
      refine ⟨8326053333420375847089725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5550702222280250564726483 8326053333420375847089725)
      ·
        refine ⟨3122270000032640942658647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8326053333420375847089725 3122270000032640942658647)
        ·
          refine ⟨4683405000048961413987971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3122270000032640942658647 4683405000048961413987971)
          ·
            refine ⟨7025107500073442120981957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4683405000048961413987971 7025107500073442120981957)
            ·
              refine ⟨1317207656263770397684117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7025107500073442120981957 1317207656263770397684117)
              ·
                refine ⟨61744108887364237391443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1317207656263770397684117 61744108887364237391443)
                ·
                  rfl

theorem cell21_811662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_811662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_811662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_811662 prefixEnd_811662 := by exact prefixLift 811662
  have htrace : WordTrace (prefixWord ++ tailWord_811662) baseStart_811662 baseEnd_811662 := by
    simpa [prefixWord, tailWord_811662, baseEnd_811662] using wordTrace_append hprefix tailTrace_811662
  have hstable : (prefixWord ++ tailWord_811662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811662).length < 2 ^ (prefixWord ++ tailWord_811662).sum := by decide
  have hdescent : baseEnd_811662 < baseStart_811662 := by decide
  rcases family_descends (prefixWord ++ tailWord_811662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811702 : List Nat := [5, 1, 3, 1, 3, 1, 2, 2, 3]
def baseStart_811702 : Nat := 118140960795 + 811702 * 2 ^ 59
def prefixEnd_811702 : Nat := 4983230072969 + 3 ^ 40 * 811702 * 2
def baseEnd_811702 : Nat := 185241455207061531507581

theorem tailTrace_811702 : CollatzResearch.WordTrace tailWord_811702 prefixEnd_811702 185241455207061531507581 := by
  unfold tailWord_811702
  simp only [CollatzResearch.WordTrace]
  refine ⟨1850325256584359781874835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19736802736899837673331573 1850325256584359781874835)
  ·
    refine ⟨2775487884876539672812253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1850325256584359781874835 2775487884876539672812253)
    ·
      refine ⟨1040807956828702377304595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2775487884876539672812253 1040807956828702377304595)
      ·
        refine ⟨1561211935243053565956893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1040807956828702377304595 1561211935243053565956893)
        ·
          refine ⟨585454475716145087233835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1561211935243053565956893 585454475716145087233835)
          ·
            refine ⟨878181713574217630850753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585454475716145087233835 878181713574217630850753)
            ·
              refine ⟨658636285180663223138065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 878181713574217630850753 658636285180663223138065)
              ·
                refine ⟨493977213885497417353549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 658636285180663223138065 493977213885497417353549)
                ·
                  refine ⟨185241455207061531507581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 493977213885497417353549 185241455207061531507581)
                  ·
                    rfl

theorem cell21_811702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_811702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_811702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_811702 prefixEnd_811702 := by exact prefixLift 811702
  have htrace : WordTrace (prefixWord ++ tailWord_811702) baseStart_811702 baseEnd_811702 := by
    simpa [prefixWord, tailWord_811702, baseEnd_811702] using wordTrace_append hprefix tailTrace_811702
  have hstable : (prefixWord ++ tailWord_811702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811702).length < 2 ^ (prefixWord ++ tailWord_811702).sum := by decide
  have hdescent : baseEnd_811702 < baseStart_811702 := by decide
  rcases family_descends (prefixWord ++ tailWord_811702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811710 : List Nat := [4, 2, 1, 1, 2, 1, 3, 4, 3]
def baseStart_811710 : Nat := 118140960795 + 811710 * 2 ^ 59
def prefixEnd_811710 : Nat := 4983230072969 + 3 ^ 40 * 811710 * 2
def baseEnd_811710 : Nat := 185243280916055295374231

theorem tailTrace_811710 : CollatzResearch.WordTrace tailWord_811710 prefixEnd_811710 185243280916055295374231 := by
  unfold tailWord_811710
  simp only [CollatzResearch.WordTrace]
  refine ⟨3700686986165096734536073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19736997259547182584192389 3700686986165096734536073)
  ·
    refine ⟨2775515239623822550902055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3700686986165096734536073 2775515239623822550902055)
    ·
      refine ⟨4163272859435733826353083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2775515239623822550902055 4163272859435733826353083)
      ·
        refine ⟨6244909289153600739529625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4163272859435733826353083 6244909289153600739529625)
        ·
          refine ⟨4683681966865200554647219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6244909289153600739529625 4683681966865200554647219)
          ·
            refine ⟨7025522950297800831970829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4683681966865200554647219 7025522950297800831970829)
            ·
              refine ⟨2634571106361675311989061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7025522950297800831970829 2634571106361675311989061)
              ·
                refine ⟨493982082442814120997949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2634571106361675311989061 493982082442814120997949)
                ·
                  refine ⟨185243280916055295374231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 493982082442814120997949 185243280916055295374231)
                  ·
                    rfl

theorem cell21_811710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_811710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_811710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_811710 prefixEnd_811710 := by exact prefixLift 811710
  have htrace : WordTrace (prefixWord ++ tailWord_811710) baseStart_811710 baseEnd_811710 := by
    simpa [prefixWord, tailWord_811710, baseEnd_811710] using wordTrace_append hprefix tailTrace_811710
  have hstable : (prefixWord ++ tailWord_811710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811710).length < 2 ^ (prefixWord ++ tailWord_811710).sum := by decide
  have hdescent : baseEnd_811710 < baseStart_811710 := by decide
  rcases family_descends (prefixWord ++ tailWord_811710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811713 : List Nat := [1, 2, 6, 2, 2, 1, 1, 6]
def baseStart_811713 : Nat := 118140960795 + 811713 * 2 ^ 59
def prefixEnd_811713 : Nat := 4983230072969 + 3 ^ 40 * 811713 * 2
def baseEnd_811713 : Nat := 61747988518975985608075

theorem tailTrace_811713 : CollatzResearch.WordTrace tailWord_811713 prefixEnd_811713 61747988518975985608075 := by
  unfold tailWord_811713
  simp only [CollatzResearch.WordTrace]
  refine ⟨29605605308309905388647793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19737070205539936925765195 29605605308309905388647793)
  ·
    refine ⟨22204203981232429041485845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29605605308309905388647793 22204203981232429041485845)
    ·
      refine ⟨1040822061620270111319649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22204203981232429041485845 1040822061620270111319649)
      ·
        refine ⟨780616546215202583489737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1040822061620270111319649 780616546215202583489737)
        ·
          refine ⟨585462409661401937617303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 780616546215202583489737 585462409661401937617303)
          ·
            refine ⟨878193614492102906425955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585462409661401937617303 878193614492102906425955)
            ·
              refine ⟨1317290421738154359638933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 878193614492102906425955 1317290421738154359638933)
              ·
                refine ⟨61747988518975985608075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1317290421738154359638933 61747988518975985608075)
                ·
                  rfl

theorem cell21_811713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 6].length) (baseStart_811713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_811713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_811713 prefixEnd_811713 := by exact prefixLift 811713
  have htrace : WordTrace (prefixWord ++ tailWord_811713) baseStart_811713 baseEnd_811713 := by
    simpa [prefixWord, tailWord_811713, baseEnd_811713] using wordTrace_append hprefix tailTrace_811713
  have hstable : (prefixWord ++ tailWord_811713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811713).length < 2 ^ (prefixWord ++ tailWord_811713).sum := by decide
  have hdescent : baseEnd_811713 < baseStart_811713 := by decide
  rcases family_descends (prefixWord ++ tailWord_811713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811724 : List Nat := [2, 2, 1, 5, 1, 1, 2, 3, 4]
def baseStart_811724 : Nat := 118140960795 + 811724 * 2 ^ 59
def prefixEnd_811724 : Nat := 4983230072969 + 3 ^ 40 * 811724 * 2
def baseEnd_811724 : Nat := 185246475906794382140869

theorem tailTrace_811724 : CollatzResearch.WordTrace tailWord_811724 prefixEnd_811724 185246475906794382140869 := by
  unfold tailWord_811724
  simp only [CollatzResearch.WordTrace]
  refine ⟨14803003255635027133649113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19737337674180036178198817 14803003255635027133649113)
  ·
    refine ⟨11102252441726270350236835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14803003255635027133649113 11102252441726270350236835)
    ·
      refine ⟨16653378662589405525355253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11102252441726270350236835 16653378662589405525355253)
      ·
        refine ⟨1561254249617756768002055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16653378662589405525355253 1561254249617756768002055)
        ·
          refine ⟨2341881374426635152003083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1561254249617756768002055 2341881374426635152003083)
          ·
            refine ⟨3512822061639952728004625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2341881374426635152003083 3512822061639952728004625)
            ·
              refine ⟨2634616546229964546003469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3512822061639952728004625 2634616546229964546003469)
              ·
                refine ⟨987981204836236704751301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2634616546229964546003469 987981204836236704751301)
                ·
                  refine ⟨185246475906794382140869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 987981204836236704751301 185246475906794382140869)
                  ·
                    rfl

theorem cell21_811724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3, 4].length) (baseStart_811724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_811724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_811724 prefixEnd_811724 := by exact prefixLift 811724
  have htrace : WordTrace (prefixWord ++ tailWord_811724) baseStart_811724 baseEnd_811724 := by
    simpa [prefixWord, tailWord_811724, baseEnd_811724] using wordTrace_append hprefix tailTrace_811724
  have hstable : (prefixWord ++ tailWord_811724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811724).length < 2 ^ (prefixWord ++ tailWord_811724).sum := by decide
  have hdescent : baseEnd_811724 < baseStart_811724 := by decide
  rcases family_descends (prefixWord ++ tailWord_811724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811738 : List Nat := [3, 1, 1, 2, 2, 2, 5, 5]
def baseStart_811738 : Nat := 118140960795 + 811738 * 2 ^ 59
def prefixEnd_811738 : Nat := 4983230072969 + 3 ^ 40 * 811738 * 2
def baseEnd_811738 : Nat := 61749890299177822969169

theorem tailTrace_811738 : CollatzResearch.WordTrace tailWord_811738 prefixEnd_811738 61749890299177822969169 := by
  unfold tailWord_811738
  simp only [CollatzResearch.WordTrace]
  refine ⟨7401629283304833664576967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19737678088812889772205245 7401629283304833664576967)
  ·
    refine ⟨11102443924957250496865451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7401629283304833664576967 11102443924957250496865451)
    ·
      refine ⟨16653665887435875745298177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11102443924957250496865451 16653665887435875745298177)
      ·
        refine ⟨12490249415576906808973633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16653665887435875745298177 12490249415576906808973633)
        ·
          refine ⟨9367687061682680106730225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12490249415576906808973633 9367687061682680106730225)
          ·
            refine ⟨7025765296262010080047669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9367687061682680106730225 7025765296262010080047669)
            ·
              refine ⟨658665496524563445004469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7025765296262010080047669 658665496524563445004469)
              ·
                refine ⟨61749890299177822969169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 658665496524563445004469 61749890299177822969169)
                ·
                  rfl

theorem cell21_811738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 5].length) (baseStart_811738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_811738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_811738 prefixEnd_811738 := by exact prefixLift 811738
  have htrace : WordTrace (prefixWord ++ tailWord_811738) baseStart_811738 baseEnd_811738 := by
    simpa [prefixWord, tailWord_811738, baseEnd_811738] using wordTrace_append hprefix tailTrace_811738
  have hstable : (prefixWord ++ tailWord_811738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811738).length < 2 ^ (prefixWord ++ tailWord_811738).sum := by decide
  have hdescent : baseEnd_811738 < baseStart_811738 := by decide
  rcases family_descends (prefixWord ++ tailWord_811738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811797 : List Nat := [1, 3, 2, 1, 2, 2, 3, 7]
def baseStart_811797 : Nat := 118140960795 + 811797 * 2 ^ 59
def prefixEnd_811797 : Nat := 4983230072969 + 3 ^ 40 * 811797 * 2
def baseEnd_811797 : Nat := 61754378500454159141351

theorem tailTrace_811797 : CollatzResearch.WordTrace tailWord_811797 prefixEnd_811797 61754378500454159141351 := by
  unfold tailWord_811797
  simp only [CollatzResearch.WordTrace]
  refine ⟨29608669040005587734705645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19739112693337058489803763 29608669040005587734705645)
  ·
    refine ⟨11103250890002095400514617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29608669040005587734705645 11103250890002095400514617)
    ·
      refine ⟨8327438167501571550385963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11103250890002095400514617 8327438167501571550385963)
      ·
        refine ⟨12491157251252357325578945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8327438167501571550385963 12491157251252357325578945)
        ·
          refine ⟨9368367938439267994184209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12491157251252357325578945 9368367938439267994184209)
          ·
            refine ⟨7026275953829450995638157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9368367938439267994184209 7026275953829450995638157)
            ·
              refine ⟨2634853482686044123364309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7026275953829450995638157 2634853482686044123364309)
              ·
                refine ⟨61754378500454159141351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2634853482686044123364309 61754378500454159141351)
                ·
                  rfl

theorem cell21_811797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 7].length) (baseStart_811797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_811797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_811797 prefixEnd_811797 := by exact prefixLift 811797
  have htrace : WordTrace (prefixWord ++ tailWord_811797) baseStart_811797 baseEnd_811797 := by
    simpa [prefixWord, tailWord_811797, baseEnd_811797] using wordTrace_append hprefix tailTrace_811797
  have hstable : (prefixWord ++ tailWord_811797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811797).length < 2 ^ (prefixWord ++ tailWord_811797).sum := by decide
  have hdescent : baseEnd_811797 < baseStart_811797 := by decide
  rcases family_descends (prefixWord ++ tailWord_811797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811834 : List Nat := [3, 1, 1, 1, 7, 1, 2, 1, 4]
def baseStart_811834 : Nat := 118140960795 + 811834 * 2 ^ 59
def prefixEnd_811834 : Nat := 4983230072969 + 3 ^ 40 * 811834 * 2
def baseEnd_811834 : Nat := 185271579405458635307311

theorem tailTrace_811834 : CollatzResearch.WordTrace tailWord_811834 prefixEnd_811834 185271579405458635307311 := by
  unfold tailWord_811834
  simp only [CollatzResearch.WordTrace]
  refine ⟨7402504635217885763450639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19740012360581028702535037 7402504635217885763450639)
  ·
    refine ⟨11103756952826828645175959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7402504635217885763450639 11103756952826828645175959)
    ·
      refine ⟨16655635429240242967763939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11103756952826828645175959 16655635429240242967763939)
      ·
        refine ⟨24983453143860364451645909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16655635429240242967763939 24983453143860364451645909)
        ·
          refine ⟨585549683059227291835451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 24983453143860364451645909 585549683059227291835451)
          ·
            refine ⟨878324524588840937753177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585549683059227291835451 878324524588840937753177)
            ·
              refine ⟨658743393441630703314883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 878324524588840937753177 658743393441630703314883)
              ·
                refine ⟨988115090162446054972325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 658743393441630703314883 988115090162446054972325)
                ·
                  refine ⟨185271579405458635307311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 988115090162446054972325 185271579405458635307311)
                  ·
                    rfl

theorem cell21_811834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 1, 4].length) (baseStart_811834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_811834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_811834 prefixEnd_811834 := by exact prefixLift 811834
  have htrace : WordTrace (prefixWord ++ tailWord_811834) baseStart_811834 baseEnd_811834 := by
    simpa [prefixWord, tailWord_811834, baseEnd_811834] using wordTrace_append hprefix tailTrace_811834
  have hstable : (prefixWord ++ tailWord_811834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811834).length < 2 ^ (prefixWord ++ tailWord_811834).sum := by decide
  have hdescent : baseEnd_811834 < baseStart_811834 := by decide
  rcases family_descends (prefixWord ++ tailWord_811834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811876 : List Nat := [2, 3, 1, 1, 4, 2, 2, 2, 4]
def baseStart_811876 : Nat := 118140960795 + 811876 * 2 ^ 59
def prefixEnd_811876 : Nat := 4983230072969 + 3 ^ 40 * 811876 * 2
def baseEnd_811876 : Nat := 185281164377675895607225

theorem tailTrace_811876 : CollatzResearch.WordTrace tailWord_811876 prefixEnd_811876 185281164377675895607225 := by
  unfold tailWord_811876
  simp only [CollatzResearch.WordTrace]
  refine ⟨14805775203359692113415741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19741033604479589484554321 14805775203359692113415741)
  ·
    refine ⟨5552165701259884542530903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14805775203359692113415741 5552165701259884542530903)
    ·
      refine ⟨8328248551889826813796355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5552165701259884542530903 8328248551889826813796355)
      ·
        refine ⟨12492372827834740220694533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8328248551889826813796355 12492372827834740220694533)
        ·
          refine ⟨2342319905219013791380225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12492372827834740220694533 2342319905219013791380225)
          ·
            refine ⟨1756739928914260343535169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2342319905219013791380225 1756739928914260343535169)
            ·
              refine ⟨1317554946685695257651377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1756739928914260343535169 1317554946685695257651377)
              ·
                refine ⟨988166210014271443238533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1317554946685695257651377 988166210014271443238533)
                ·
                  refine ⟨185281164377675895607225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 988166210014271443238533 185281164377675895607225)
                  ·
                    rfl

theorem cell21_811876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_811876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_811876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_811876 prefixEnd_811876 := by exact prefixLift 811876
  have htrace : WordTrace (prefixWord ++ tailWord_811876) baseStart_811876 baseEnd_811876 := by
    simpa [prefixWord, tailWord_811876, baseEnd_811876] using wordTrace_append hprefix tailTrace_811876
  have hstable : (prefixWord ++ tailWord_811876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811876).length < 2 ^ (prefixWord ++ tailWord_811876).sum := by decide
  have hdescent : baseEnd_811876 < baseStart_811876 := by decide
  rcases family_descends (prefixWord ++ tailWord_811876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811879 : List Nat := [1, 1, 5, 1, 2, 4, 2, 2, 3]
def baseStart_811879 : Nat := 118140960795 + 811879 * 2 ^ 59
def prefixEnd_811879 : Nat := 4983230072969 + 3 ^ 40 * 811879 * 2
def baseEnd_811879 : Nat := 185281849018548557057219

theorem tailTrace_811879 : CollatzResearch.WordTrace tailWord_811879 prefixEnd_811879 185281849018548557057219 := by
  unfold tailWord_811879
  simp only [CollatzResearch.WordTrace]
  refine ⟨29611659825708515739190691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19741106550472343826127127 29611659825708515739190691)
  ·
    refine ⟨44417489738562773608786037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29611659825708515739190691 44417489738562773608786037)
    ·
      refine ⟨4164139662990260025823691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44417489738562773608786037 4164139662990260025823691)
      ·
        refine ⟨6246209494485390038735537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4164139662990260025823691 6246209494485390038735537)
        ·
          refine ⟨4684657120864042529051653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6246209494485390038735537 4684657120864042529051653)
          ·
            refine ⟨878373210162007974197185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4684657120864042529051653 878373210162007974197185)
            ·
              refine ⟨658779907621505980647889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 878373210162007974197185 658779907621505980647889)
              ·
                refine ⟨494084930716129485485917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 658779907621505980647889 494084930716129485485917)
                ·
                  refine ⟨185281849018548557057219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 494084930716129485485917 185281849018548557057219)
                  ·
                    rfl

theorem cell21_811879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 2, 3].length) (baseStart_811879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_811879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_811879 prefixEnd_811879 := by exact prefixLift 811879
  have htrace : WordTrace (prefixWord ++ tailWord_811879) baseStart_811879 baseEnd_811879 := by
    simpa [prefixWord, tailWord_811879, baseEnd_811879] using wordTrace_append hprefix tailTrace_811879
  have hstable : (prefixWord ++ tailWord_811879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811879).length < 2 ^ (prefixWord ++ tailWord_811879).sum := by decide
  have hdescent : baseEnd_811879 < baseStart_811879 := by decide
  rcases family_descends (prefixWord ++ tailWord_811879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811887 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 9]
def baseStart_811887 : Nat := 118140960795 + 811887 * 2 ^ 59
def prefixEnd_811887 : Nat := 4983230072969 + 3 ^ 40 * 811887 * 2
def baseEnd_811887 : Nat := 185283674727542320923869

theorem tailTrace_811887 : CollatzResearch.WordTrace tailWord_811887 prefixEnd_811887 185283674727542320923869 := by
  unfold tailWord_811887
  simp only [CollatzResearch.WordTrace]
  refine ⟨29611951609679533105481915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19741301073119688736987943 29611951609679533105481915)
  ·
    refine ⟨44417927414519299658222873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29611951609679533105481915 44417927414519299658222873)
    ·
      refine ⟨33313445560889474743667155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44417927414519299658222873 33313445560889474743667155)
      ·
        refine ⟨49970168341334212115500733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33313445560889474743667155 49970168341334212115500733)
        ·
          refine ⟨18738813128000329543312775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49970168341334212115500733 18738813128000329543312775)
          ·
            refine ⟨28108219692000494314969163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18738813128000329543312775 28108219692000494314969163)
            ·
              refine ⟨42162329538000741472453745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28108219692000494314969163 42162329538000741472453745)
              ·
                refine ⟨31621747153500556104340309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42162329538000741472453745 31621747153500556104340309)
                ·
                  refine ⟨185283674727542320923869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31621747153500556104340309 185283674727542320923869)
                  ·
                    rfl

theorem cell21_811887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 9].length) (baseStart_811887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_811887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_811887 prefixEnd_811887 := by exact prefixLift 811887
  have htrace : WordTrace (prefixWord ++ tailWord_811887) baseStart_811887 baseEnd_811887 := by
    simpa [prefixWord, tailWord_811887, baseEnd_811887] using wordTrace_append hprefix tailTrace_811887
  have hstable : (prefixWord ++ tailWord_811887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811887).length < 2 ^ (prefixWord ++ tailWord_811887).sum := by decide
  have hdescent : baseEnd_811887 < baseStart_811887 := by decide
  rcases family_descends (prefixWord ++ tailWord_811887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811935 : List Nat := [1, 1, 2, 5, 2, 2, 1, 1, 6]
def baseStart_811935 : Nat := 118140960795 + 811935 * 2 ^ 59
def prefixEnd_811935 : Nat := 4983230072969 + 3 ^ 40 * 811935 * 2
def baseEnd_811935 : Nat := 185294628981504904123771

theorem tailTrace_811935 : CollatzResearch.WordTrace tailWord_811935 prefixEnd_811935 185294628981504904123771 := by
  unfold tailWord_811935
  simp only [CollatzResearch.WordTrace]
  refine ⟨29613702313505637303229259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19742468209003758202152839 29613702313505637303229259)
  ·
    refine ⟨44420553470258455954843889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29613702313505637303229259 44420553470258455954843889)
    ·
      refine ⟨33315415102693841966132917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44420553470258455954843889 33315415102693841966132917)
      ·
        refine ⟨3123320165877547684324961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33315415102693841966132917 3123320165877547684324961)
        ·
          refine ⟨2342490124408160763243721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3123320165877547684324961 2342490124408160763243721)
          ·
            refine ⟨1756867593306120572432791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2342490124408160763243721 1756867593306120572432791)
            ·
              refine ⟨2635301389959180858649187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1756867593306120572432791 2635301389959180858649187)
              ·
                refine ⟨3952952084938771287973781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2635301389959180858649187 3952952084938771287973781)
                ·
                  refine ⟨185294628981504904123771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3952952084938771287973781 185294628981504904123771)
                  ·
                    rfl

theorem cell21_811935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 6].length) (baseStart_811935 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_811935 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_811935 prefixEnd_811935 := by exact prefixLift 811935
  have htrace : WordTrace (prefixWord ++ tailWord_811935) baseStart_811935 baseEnd_811935 := by
    simpa [prefixWord, tailWord_811935, baseEnd_811935] using wordTrace_append hprefix tailTrace_811935
  have hstable : (prefixWord ++ tailWord_811935).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811935).length < 2 ^ (prefixWord ++ tailWord_811935).sum := by decide
  have hdescent : baseEnd_811935 < baseStart_811935 := by decide
  rcases family_descends (prefixWord ++ tailWord_811935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811938 : List Nat := [3, 3, 1, 2, 2, 1, 2, 4, 3]
def baseStart_811938 : Nat := 118140960795 + 811938 * 2 ^ 59
def prefixEnd_811938 : Nat := 4983230072969 + 3 ^ 40 * 811938 * 2
def baseEnd_811938 : Nat := 185295313622377565573765

theorem tailTrace_811938 : CollatzResearch.WordTrace tailWord_811938 prefixEnd_811938 185295313622377565573765 := by
  unfold tailWord_811938
  simp only [CollatzResearch.WordTrace]
  refine ⟨7403452933123692203897117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19742541154996512543725645 7403452933123692203897117)
  ·
    refine ⟨2776294849921384576461419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7403452933123692203897117 2776294849921384576461419)
    ·
      refine ⟨4164442274882076864692129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2776294849921384576461419 4164442274882076864692129)
      ·
        refine ⟨3123331706161557648519097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4164442274882076864692129 3123331706161557648519097)
        ·
          refine ⟨2342498779621168236389323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3123331706161557648519097 2342498779621168236389323)
          ·
            refine ⟨3513748169431752354583985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2342498779621168236389323 3513748169431752354583985)
            ·
              refine ⟨2635311127073814265937989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3513748169431752354583985 2635311127073814265937989)
              ·
                refine ⟨494120836326340174863373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2635311127073814265937989 494120836326340174863373)
                ·
                  refine ⟨185295313622377565573765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 494120836326340174863373 185295313622377565573765)
                  ·
                    rfl

theorem cell21_811938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_811938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_811938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_811938 prefixEnd_811938 := by exact prefixLift 811938
  have htrace : WordTrace (prefixWord ++ tailWord_811938) baseStart_811938 baseEnd_811938 := by
    simpa [prefixWord, tailWord_811938, baseEnd_811938] using wordTrace_append hprefix tailTrace_811938
  have hstable : (prefixWord ++ tailWord_811938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811938).length < 2 ^ (prefixWord ++ tailWord_811938).sum := by decide
  have hdescent : baseEnd_811938 < baseStart_811938 := by decide
  rcases family_descends (prefixWord ++ tailWord_811938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811958 : List Nat := [5, 1, 4, 1, 1, 2, 2, 5]
def baseStart_811958 : Nat := 118140960795 + 811958 * 2 ^ 59
def prefixEnd_811958 : Nat := 4983230072969 + 3 ^ 40 * 811958 * 2
def baseEnd_811958 : Nat := 61766625964953991746797

theorem tailTrace_811958 : CollatzResearch.WordTrace tailWord_811958 prefixEnd_811958 61766625964953991746797 := by
  unfold tailWord_811958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1850908824526394514457283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19743027461614874820877685 1850908824526394514457283)
  ·
    refine ⟨2776363236789591771685925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1850908824526394514457283 2776363236789591771685925)
    ·
      refine ⟨520568106898048457191111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2776363236789591771685925 520568106898048457191111)
      ·
        refine ⟨780852160347072685786667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 520568106898048457191111 780852160347072685786667)
        ·
          refine ⟨1171278240520609028680001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 780852160347072685786667 1171278240520609028680001)
          ·
            refine ⟨878458680390456771510001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1171278240520609028680001 878458680390456771510001)
            ·
              refine ⟨658844010292842578632501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 878458680390456771510001 658844010292842578632501)
              ·
                refine ⟨61766625964953991746797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 658844010292842578632501 61766625964953991746797)
                ·
                  rfl

theorem cell21_811958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_811958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_811958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_811958 prefixEnd_811958 := by exact prefixLift 811958
  have htrace : WordTrace (prefixWord ++ tailWord_811958) baseStart_811958 baseEnd_811958 := by
    simpa [prefixWord, tailWord_811958, baseEnd_811958] using wordTrace_append hprefix tailTrace_811958
  have hstable : (prefixWord ++ tailWord_811958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811958).length < 2 ^ (prefixWord ++ tailWord_811958).sum := by decide
  have hdescent : baseEnd_811958 < baseStart_811958 := by decide
  rcases family_descends (prefixWord ++ tailWord_811958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811972 : List Nat := [2, 3, 3, 3, 1, 2, 1, 3, 3]
def baseStart_811972 : Nat := 118140960795 + 811972 * 2 ^ 59
def prefixEnd_811972 : Nat := 4983230072969 + 3 ^ 40 * 811972 * 2
def baseEnd_811972 : Nat := 185303072885601062007029

theorem tailTrace_811972 : CollatzResearch.WordTrace tailWord_811972 prefixEnd_811972 185303072885601062007029 := by
  unfold tailWord_811972
  simp only [CollatzResearch.WordTrace]
  refine ⟨14807525907185796311163085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19743367876247728414884113 14807525907185796311163085)
  ·
    refine ⟨5552822215194673616686157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14807525907185796311163085 5552822215194673616686157)
    ·
      refine ⟨2082308330698002606257309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5552822215194673616686157 2082308330698002606257309)
      ·
        refine ⟨780865624011750977346491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2082308330698002606257309 780865624011750977346491)
        ·
          refine ⟨1171298436017626466019737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 780865624011750977346491 1171298436017626466019737)
          ·
            refine ⟨878473827013219849514803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1171298436017626466019737 878473827013219849514803)
            ·
              refine ⟨1317710740519829774272205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 878473827013219849514803 1317710740519829774272205)
              ·
                refine ⟨494141527694936165352077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1317710740519829774272205 494141527694936165352077)
                ·
                  refine ⟨185303072885601062007029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 494141527694936165352077 185303072885601062007029)
                  ·
                    rfl

theorem cell21_811972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 3, 3].length) (baseStart_811972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_811972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_811972 prefixEnd_811972 := by exact prefixLift 811972
  have htrace : WordTrace (prefixWord ++ tailWord_811972) baseStart_811972 baseEnd_811972 := by
    simpa [prefixWord, tailWord_811972, baseEnd_811972] using wordTrace_append hprefix tailTrace_811972
  have hstable : (prefixWord ++ tailWord_811972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811972).length < 2 ^ (prefixWord ++ tailWord_811972).sum := by decide
  have hdescent : baseEnd_811972 < baseStart_811972 := by decide
  rcases family_descends (prefixWord ++ tailWord_811972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811997 : List Nat := [1, 4, 3, 1, 2, 1, 3, 1, 5]
def baseStart_811997 : Nat := 118140960795 + 811997 * 2 ^ 59
def prefixEnd_811997 : Nat := 4983230072969 + 3 ^ 40 * 811997 * 2
def baseEnd_811997 : Nat := 185308778226206574090311

theorem tailTrace_811997 : CollatzResearch.WordTrace tailWord_811997 prefixEnd_811997 185308778226206574090311 := by
  unfold tailWord_811997
  simp only [CollatzResearch.WordTrace]
  refine ⟨29615963639281021891986245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19743975759520681261324163 29615963639281021891986245)
  ·
    refine ⟨5552993182365191604747421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29615963639281021891986245 5552993182365191604747421)
    ·
      refine ⟨2082372443386946851780283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5552993182365191604747421 2082372443386946851780283)
      ·
        refine ⟨3123558665080420277670425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2082372443386946851780283 3123558665080420277670425)
        ·
          refine ⟨2342668998810315208252819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3123558665080420277670425 2342668998810315208252819)
          ·
            refine ⟨3514003498215472812379229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2342668998810315208252819 3514003498215472812379229)
            ·
              refine ⟨1317751311830802304642211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3514003498215472812379229 1317751311830802304642211)
              ·
                refine ⟨1976626967746203456963317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1317751311830802304642211 1976626967746203456963317)
                ·
                  refine ⟨185308778226206574090311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1976626967746203456963317 185308778226206574090311)
                  ·
                    rfl

theorem cell21_811997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_811997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_811997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_811997 prefixEnd_811997 := by exact prefixLift 811997
  have htrace : WordTrace (prefixWord ++ tailWord_811997) baseStart_811997 baseEnd_811997 := by
    simpa [prefixWord, tailWord_811997, baseEnd_811997] using wordTrace_append hprefix tailTrace_811997
  have hstable : (prefixWord ++ tailWord_811997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811997).length < 2 ^ (prefixWord ++ tailWord_811997).sum := by decide
  have hdescent : baseEnd_811997 < baseStart_811997 := by decide
  rcases family_descends (prefixWord ++ tailWord_811997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812115 : List Nat := [1, 1, 1, 2, 1, 1, 2, 7, 5]
def baseStart_812115 : Nat := 118140960795 + 812115 * 2 ^ 59
def prefixEnd_812115 : Nat := 4983230072969 + 3 ^ 40 * 812115 * 2
def baseEnd_812115 : Nat := 185335707433864591123403

theorem tailTrace_812115 : CollatzResearch.WordTrace tailWord_812115 prefixEnd_812115 185335707433864591123403 := by
  unfold tailWord_812115
  simp only [CollatzResearch.WordTrace]
  refine ⟨29620267452853528044781799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19746844968569018696521199 29620267452853528044781799)
  ·
    refine ⟨44430401179280292067172699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29620267452853528044781799 44430401179280292067172699)
    ·
      refine ⟨66645601768920438100759049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44430401179280292067172699 66645601768920438100759049)
      ·
        refine ⟨49984201326690328575569287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66645601768920438100759049 49984201326690328575569287)
        ·
          refine ⟨74976301990035492863353931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49984201326690328575569287 74976301990035492863353931)
          ·
            refine ⟨112464452985053239295030897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74976301990035492863353931 112464452985053239295030897)
            ·
              refine ⟨84348339738789929471273173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112464452985053239295030897 84348339738789929471273173)
              ·
                refine ⟨1976914212627888971982965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 84348339738789929471273173 1976914212627888971982965)
                ·
                  refine ⟨185335707433864591123403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1976914212627888971982965 185335707433864591123403)
                  ·
                    rfl

theorem cell21_812115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 5].length) (baseStart_812115 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_812115 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_812115 prefixEnd_812115 := by exact prefixLift 812115
  have htrace : WordTrace (prefixWord ++ tailWord_812115) baseStart_812115 baseEnd_812115 := by
    simpa [prefixWord, tailWord_812115, baseEnd_812115] using wordTrace_append hprefix tailTrace_812115
  have hstable : (prefixWord ++ tailWord_812115).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812115).length < 2 ^ (prefixWord ++ tailWord_812115).sum := by decide
  have hdescent : baseEnd_812115 < baseStart_812115 := by decide
  rcases family_descends (prefixWord ++ tailWord_812115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812146 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 8]
def baseStart_812146 : Nat := 118140960795 + 812146 * 2 ^ 59
def prefixEnd_812146 : Nat := 4983230072969 + 3 ^ 40 * 812146 * 2
def baseEnd_812146 : Nat := 185342782056215426106673

theorem tailTrace_812146 : CollatzResearch.WordTrace tailWord_812146 prefixEnd_812146 185342782056215426106673 := by
  unfold tailWord_812146
  simp only [CollatzResearch.WordTrace]
  refine ⟨7405349528935305084790073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19747598743827480226106861 7405349528935305084790073)
  ·
    refine ⟨5554012146701478813592555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7405349528935305084790073 5554012146701478813592555)
    ·
      refine ⟨8331018220052218220388833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5554012146701478813592555 8331018220052218220388833)
      ·
        refine ⟨6248263665039163665291625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8331018220052218220388833 6248263665039163665291625)
        ·
          refine ⟨4686197748779372748968719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6248263665039163665291625 4686197748779372748968719)
          ·
            refine ⟨7029296623169059123453079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4686197748779372748968719 7029296623169059123453079)
            ·
              refine ⟨10543944934753588685179619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7029296623169059123453079 10543944934753588685179619)
              ·
                refine ⟨15815917402130383027769429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10543944934753588685179619 15815917402130383027769429)
                ·
                  refine ⟨185342782056215426106673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15815917402130383027769429 185342782056215426106673)
                  ·
                    rfl

theorem cell21_812146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_812146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_812146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_812146 prefixEnd_812146 := by exact prefixLift 812146
  have htrace : WordTrace (prefixWord ++ tailWord_812146) baseStart_812146 baseEnd_812146 := by
    simpa [prefixWord, tailWord_812146, baseEnd_812146] using wordTrace_append hprefix tailTrace_812146
  have hstable : (prefixWord ++ tailWord_812146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812146).length < 2 ^ (prefixWord ++ tailWord_812146).sum := by decide
  have hdescent : baseEnd_812146 < baseStart_812146 := by decide
  rcases family_descends (prefixWord ++ tailWord_812146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812160 : List Nat := [2, 1, 1, 2, 1, 3, 11]
def baseStart_812160 : Nat := 118140960795 + 812160 * 2 ^ 59
def prefixEnd_812160 : Nat := 4983230072969 + 3 ^ 40 * 812160 * 2
def baseEnd_812160 : Nat := 20593997449661612541479

theorem tailTrace_812160 : CollatzResearch.WordTrace tailWord_812160 prefixEnd_812160 20593997449661612541479 := by
  unfold tailWord_812160
  simp only [CollatzResearch.WordTrace]
  refine ⟨14810954368845250365084967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19747939158460333820113289 14810954368845250365084967)
  ·
    refine ⟨22216431553267875547627451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14810954368845250365084967 22216431553267875547627451)
    ·
      refine ⟨33324647329901813321441177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22216431553267875547627451 33324647329901813321441177)
      ·
        refine ⟨24993485497426359991080883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33324647329901813321441177 24993485497426359991080883)
        ·
          refine ⟨37490228246139539986621325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24993485497426359991080883 37490228246139539986621325)
          ·
            refine ⟨14058835592302327494982997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37490228246139539986621325 14058835592302327494982997)
            ·
              refine ⟨20593997449661612541479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 14058835592302327494982997 20593997449661612541479)
              ·
                rfl

theorem cell21_812160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 11].length) (baseStart_812160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_812160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_812160 prefixEnd_812160 := by exact prefixLift 812160
  have htrace : WordTrace (prefixWord ++ tailWord_812160) baseStart_812160 baseEnd_812160 := by
    simpa [prefixWord, tailWord_812160, baseEnd_812160] using wordTrace_append hprefix tailTrace_812160
  have hstable : (prefixWord ++ tailWord_812160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812160).length < 2 ^ (prefixWord ++ tailWord_812160).sum := by decide
  have hdescent : baseEnd_812160 < baseStart_812160 := by decide
  rcases family_descends (prefixWord ++ tailWord_812160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812214 : List Nat := [5, 1, 3, 2, 1, 1, 2, 2, 4]
def baseStart_812214 : Nat := 118140960795 + 812214 * 2 ^ 59
def prefixEnd_812214 : Nat := 4983230072969 + 3 ^ 40 * 812214 * 2
def baseEnd_812214 : Nat := 185358300582662418973201

theorem tailTrace_812214 : CollatzResearch.WordTrace tailWord_812214 prefixEnd_812214 185358300582662418973201 := by
  unfold tailWord_812214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1851492392468429247039731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19749252186329911968423797 1851492392468429247039731)
  ·
    refine ⟨2777238588702643870559597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1851492392468429247039731 2777238588702643870559597)
    ·
      refine ⟨1041464470763491451459849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2777238588702643870559597 1041464470763491451459849)
      ·
        refine ⟨781098353072618588594887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1041464470763491451459849 781098353072618588594887)
        ·
          refine ⟨1171647529608927882892331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 781098353072618588594887 1171647529608927882892331)
          ·
            refine ⟨1757471294413391824338497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1171647529608927882892331 1757471294413391824338497)
            ·
              refine ⟨1318103470810043868253873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1757471294413391824338497 1318103470810043868253873)
              ·
                refine ⟨988577603107532901190405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1318103470810043868253873 988577603107532901190405)
                ·
                  refine ⟨185358300582662418973201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 988577603107532901190405 185358300582662418973201)
                  ·
                    rfl

theorem cell21_812214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_812214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_812214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_812214 prefixEnd_812214 := by exact prefixLift 812214
  have htrace : WordTrace (prefixWord ++ tailWord_812214) baseStart_812214 baseEnd_812214 := by
    simpa [prefixWord, tailWord_812214, baseEnd_812214] using wordTrace_append hprefix tailTrace_812214
  have hstable : (prefixWord ++ tailWord_812214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812214).length < 2 ^ (prefixWord ++ tailWord_812214).sum := by decide
  have hdescent : baseEnd_812214 < baseStart_812214 := by decide
  rcases family_descends (prefixWord ++ tailWord_812214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812388 : List Nat := [2, 3, 1, 1, 3, 11]
def baseStart_812388 : Nat := 118140960795 + 812388 * 2 ^ 59
def prefixEnd_812388 : Nat := 4983230072969 + 3 ^ 40 * 812388 * 2
def baseEnd_812388 : Nat := 6866592953825066039735

theorem tailTrace_812388 : CollatzResearch.WordTrace tailWord_812388 prefixEnd_812388 6866592953825066039735 := by
  unfold tailWord_812388
  simp only [CollatzResearch.WordTrace]
  refine ⟨14815112290432247834734909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19753483053909663779646545 14815112290432247834734909)
  ·
    refine ⟨5555667108912092938025591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14815112290432247834734909 5555667108912092938025591)
    ·
      refine ⟨8333500663368139407038387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5555667108912092938025591 8333500663368139407038387)
      ·
        refine ⟨12500250995052209110557581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8333500663368139407038387 12500250995052209110557581)
        ·
          refine ⟨4687594123144578416459093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12500250995052209110557581 4687594123144578416459093)
          ·
            refine ⟨6866592953825066039735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4687594123144578416459093 6866592953825066039735)
            ·
              rfl

theorem cell21_812388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 11].length) (baseStart_812388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_812388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_812388 prefixEnd_812388 := by exact prefixLift 812388
  have htrace : WordTrace (prefixWord ++ tailWord_812388) baseStart_812388 baseEnd_812388 := by
    simpa [prefixWord, tailWord_812388, baseEnd_812388] using wordTrace_append hprefix tailTrace_812388
  have hstable : (prefixWord ++ tailWord_812388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812388).length < 2 ^ (prefixWord ++ tailWord_812388).sum := by decide
  have hdescent : baseEnd_812388 < baseStart_812388 := by decide
  rcases family_descends (prefixWord ++ tailWord_812388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812394 : List Nat := [3, 1, 3, 3, 2, 1, 1, 4, 3]
def baseStart_812394 : Nat := 118140960795 + 812394 * 2 ^ 59
def prefixEnd_812394 : Nat := 4983230072969 + 3 ^ 40 * 812394 * 2
def baseEnd_812394 : Nat := 185399379035022105972833

theorem tailTrace_812394 : CollatzResearch.WordTrace tailWord_812394 prefixEnd_812394 185399379035022105972833 := by
  unfold tailWord_812394
  simp only [CollatzResearch.WordTrace]
  refine ⟨7407610854710689673547059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19753628945895172462792157 7407610854710689673547059)
  ·
    refine ⟨11111416282066034510320589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7407610854710689673547059 11111416282066034510320589)
    ·
      refine ⟨4166781105774762941370221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11111416282066034510320589 4166781105774762941370221)
      ·
        refine ⟨1562542914665536103013833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4166781105774762941370221 1562542914665536103013833)
        ·
          refine ⟨1171907185999152077260375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1562542914665536103013833 1171907185999152077260375)
          ·
            refine ⟨1757860778998728115890563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1171907185999152077260375 1757860778998728115890563)
            ·
              refine ⟨2636791168498092173835845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1757860778998728115890563 2636791168498092173835845)
              ·
                refine ⟨494398344093392282594221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2636791168498092173835845 494398344093392282594221)
                ·
                  refine ⟨185399379035022105972833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 494398344093392282594221 185399379035022105972833)
                  ·
                    rfl

theorem cell21_812394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 4, 3].length) (baseStart_812394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_812394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_812394 prefixEnd_812394 := by exact prefixLift 812394
  have htrace : WordTrace (prefixWord ++ tailWord_812394) baseStart_812394 baseEnd_812394 := by
    simpa [prefixWord, tailWord_812394, baseEnd_812394] using wordTrace_append hprefix tailTrace_812394
  have hstable : (prefixWord ++ tailWord_812394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812394).length < 2 ^ (prefixWord ++ tailWord_812394).sum := by decide
  have hdescent : baseEnd_812394 < baseStart_812394 := by decide
  rcases family_descends (prefixWord ++ tailWord_812394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812419 : List Nat := [1, 1, 1, 3, 5, 1, 1, 1, 7]
def baseStart_812419 : Nat := 118140960795 + 812419 * 2 ^ 59
def prefixEnd_812419 : Nat := 4983230072969 + 3 ^ 40 * 812419 * 2
def baseEnd_812419 : Nat := 185405084375627618056115

theorem tailTrace_812419 : CollatzResearch.WordTrace tailWord_812419 prefixEnd_812419 185405084375627618056115 := by
  unfold tailWord_812419
  simp only [CollatzResearch.WordTrace]
  refine ⟨29631355243752187963848311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19754236829168125309232207 29631355243752187963848311)
  ·
    refine ⟨44447032865628281945772467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29631355243752187963848311 44447032865628281945772467)
    ·
      refine ⟨66670549298442422918658701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44447032865628281945772467 66670549298442422918658701)
      ·
        refine ⟨25001455986915908594497013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66670549298442422918658701 25001455986915908594497013)
        ·
          refine ⟨2343886498773366430734095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25001455986915908594497013 2343886498773366430734095)
          ·
            refine ⟨3515829748160049646101143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2343886498773366430734095 3515829748160049646101143)
            ·
              refine ⟨5273744622240074469151715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3515829748160049646101143 5273744622240074469151715)
              ·
                refine ⟨7910616933360111703727573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5273744622240074469151715 7910616933360111703727573)
                ·
                  refine ⟨185405084375627618056115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7910616933360111703727573 185405084375627618056115)
                  ·
                    rfl

theorem cell21_812419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 7].length) (baseStart_812419 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_812419 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_812419 prefixEnd_812419 := by exact prefixLift 812419
  have htrace : WordTrace (prefixWord ++ tailWord_812419) baseStart_812419 baseEnd_812419 := by
    simpa [prefixWord, tailWord_812419, baseEnd_812419] using wordTrace_append hprefix tailTrace_812419
  have hstable : (prefixWord ++ tailWord_812419).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812419).length < 2 ^ (prefixWord ++ tailWord_812419).sum := by decide
  have hdescent : baseEnd_812419 < baseStart_812419 := by decide
  rcases family_descends (prefixWord ++ tailWord_812419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812433 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 8]
def baseStart_812433 : Nat := 118140960795 + 812433 * 2 ^ 59
def prefixEnd_812433 : Nat := 4983230072969 + 3 ^ 40 * 812433 * 2
def baseEnd_812433 : Nat := 185408279366366704822753

theorem tailTrace_812433 : CollatzResearch.WordTrace tailWord_812433 prefixEnd_812433 185408279366366704822753 := by
  unfold tailWord_812433
  simp only [CollatzResearch.WordTrace]
  refine ⟨29631865865701468354857953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19754577243800978903238635 29631865865701468354857953)
  ·
    refine ⟨22223899399276101266143465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29631865865701468354857953 22223899399276101266143465)
    ·
      refine ⟨16667924549457075949607599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22223899399276101266143465 16667924549457075949607599)
      ·
        refine ⟨25001886824185613924411399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16667924549457075949607599 25001886824185613924411399)
        ·
          refine ⟨37502830236278420886617099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25001886824185613924411399 37502830236278420886617099)
          ·
            refine ⟨56254245354417631329925649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37502830236278420886617099 56254245354417631329925649)
            ·
              refine ⟨42190684015813223497444237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56254245354417631329925649 42190684015813223497444237)
              ·
                refine ⟨15821506505929958811541589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42190684015813223497444237 15821506505929958811541589)
                ·
                  refine ⟨185408279366366704822753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15821506505929958811541589 185408279366366704822753)
                  ·
                    rfl

theorem cell21_812433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 8].length) (baseStart_812433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_812433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_812433 prefixEnd_812433 := by exact prefixLift 812433
  have htrace : WordTrace (prefixWord ++ tailWord_812433) baseStart_812433 baseEnd_812433 := by
    simpa [prefixWord, tailWord_812433, baseEnd_812433] using wordTrace_append hprefix tailTrace_812433
  have hstable : (prefixWord ++ tailWord_812433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812433).length < 2 ^ (prefixWord ++ tailWord_812433).sum := by decide
  have hdescent : baseEnd_812433 < baseStart_812433 := by decide
  rcases family_descends (prefixWord ++ tailWord_812433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812540 : List Nat := [2, 2, 2, 1, 2, 1, 4, 7]
def baseStart_812540 : Nat := 118140960795 + 812540 * 2 ^ 59
def prefixEnd_812540 : Nat := 4983230072969 + 3 ^ 40 * 812540 * 2
def baseEnd_812540 : Nat := 61810899408052765513067

theorem tailTrace_812540 : CollatzResearch.WordTrace tailWord_812540 prefixEnd_812540 61810899408052765513067 := by
  unfold tailWord_812540
  simp only [CollatzResearch.WordTrace]
  refine ⟨14817884238156912814501537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19757178984209217086002049 14817884238156912814501537)
  ·
    refine ⟨11113413178617684610876153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14817884238156912814501537 11113413178617684610876153)
    ·
      refine ⟨8335059883963263458157115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11113413178617684610876153 8335059883963263458157115)
      ·
        refine ⟨12502589825944895187235673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8335059883963263458157115 12502589825944895187235673)
        ·
          refine ⟨9376942369458671390426755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12502589825944895187235673 9376942369458671390426755)
          ·
            refine ⟨14065413554188007085640133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9376942369458671390426755 14065413554188007085640133)
            ·
              refine ⟨2637265041410251328557525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14065413554188007085640133 2637265041410251328557525)
              ·
                refine ⟨61810899408052765513067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2637265041410251328557525 61810899408052765513067)
                ·
                  rfl

theorem cell21_812540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 7].length) (baseStart_812540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_812540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_812540 prefixEnd_812540 := by exact prefixLift 812540
  have htrace : WordTrace (prefixWord ++ tailWord_812540) baseStart_812540 baseEnd_812540 := by
    simpa [prefixWord, tailWord_812540, baseEnd_812540] using wordTrace_append hprefix tailTrace_812540
  have hstable : (prefixWord ++ tailWord_812540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812540).length < 2 ^ (prefixWord ++ tailWord_812540).sum := by decide
  have hdescent : baseEnd_812540 < baseStart_812540 := by decide
  rcases family_descends (prefixWord ++ tailWord_812540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812636 : List Nat := [2, 2, 4, 1, 2, 2, 3, 1, 4]
def baseStart_812636 : Nat := 118140960795 + 812636 * 2 ^ 59
def prefixEnd_812636 : Nat := 4983230072969 + 3 ^ 40 * 812636 * 2
def baseEnd_812636 : Nat := 185454606732083462939005

theorem tailTrace_812636 : CollatzResearch.WordTrace tailWord_812636 prefixEnd_812636 185454606732083462939005 := by
  unfold tailWord_812636
  simp only [CollatzResearch.WordTrace]
  refine ⟨14819634941983017012248881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19759513255977356016331841 14819634941983017012248881)
  ·
    refine ⟨11114726206487262759186661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14819634941983017012248881 11114726206487262759186661)
    ·
      refine ⟨2084011163716361767347499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11114726206487262759186661 2084011163716361767347499)
      ·
        refine ⟨3126016745574542651021249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2084011163716361767347499 3126016745574542651021249)
        ·
          refine ⟨2344512559180906988265937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3126016745574542651021249 2344512559180906988265937)
          ·
            refine ⟨1758384419385680241199453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2344512559180906988265937 1758384419385680241199453)
            ·
              refine ⟨659394157269630090449795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1758384419385680241199453 659394157269630090449795)
              ·
                refine ⟨989091235904445135674693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 659394157269630090449795 989091235904445135674693)
                ·
                  refine ⟨185454606732083462939005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 989091235904445135674693 185454606732083462939005)
                  ·
                    rfl

theorem cell21_812636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 1, 4].length) (baseStart_812636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_812636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_812636 prefixEnd_812636 := by exact prefixLift 812636
  have htrace : WordTrace (prefixWord ++ tailWord_812636) baseStart_812636 baseEnd_812636 := by
    simpa [prefixWord, tailWord_812636, baseEnd_812636] using wordTrace_append hprefix tailTrace_812636
  have hstable : (prefixWord ++ tailWord_812636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812636).length < 2 ^ (prefixWord ++ tailWord_812636).sum := by decide
  have hdescent : baseEnd_812636 < baseStart_812636 := by decide
  rcases family_descends (prefixWord ++ tailWord_812636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812647 : List Nat := [1, 1, 5, 1, 1, 1, 4, 2, 5]
def baseStart_812647 : Nat := 118140960795 + 812647 * 2 ^ 59
def prefixEnd_812647 : Nat := 4983230072969 + 3 ^ 40 * 812647 * 2
def baseEnd_812647 : Nat := 185457117081949888255649

theorem tailTrace_812647 : CollatzResearch.WordTrace tailWord_812647 prefixEnd_812647 185457117081949888255649 := by
  unfold tailWord_812647
  simp only [CollatzResearch.WordTrace]
  refine ⟨29639671086926182903148195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19759780724617455268765463 29639671086926182903148195)
  ·
    refine ⟨44459506630389274354722293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29639671086926182903148195 44459506630389274354722293)
    ·
      refine ⟨4168078746598994470755215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44459506630389274354722293 4168078746598994470755215)
      ·
        refine ⟨6252118119898491706132823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4168078746598994470755215 6252118119898491706132823)
        ·
          refine ⟨9378177179847737559199235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6252118119898491706132823 9378177179847737559199235)
          ·
            refine ⟨14067265769771606338798853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9378177179847737559199235 14067265769771606338798853)
            ·
              refine ⟨2637612331832176188524785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14067265769771606338798853 2637612331832176188524785)
              ·
                refine ⟨1978209248874132141393589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2637612331832176188524785 1978209248874132141393589)
                ·
                  refine ⟨185457117081949888255649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1978209248874132141393589 185457117081949888255649)
                  ·
                    rfl

theorem cell21_812647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 5].length) (baseStart_812647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_812647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_812647 prefixEnd_812647 := by exact prefixLift 812647
  have htrace : WordTrace (prefixWord ++ tailWord_812647) baseStart_812647 baseEnd_812647 := by
    simpa [prefixWord, tailWord_812647, baseEnd_812647] using wordTrace_append hprefix tailTrace_812647
  have hstable : (prefixWord ++ tailWord_812647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812647).length < 2 ^ (prefixWord ++ tailWord_812647).sum := by decide
  have hdescent : baseEnd_812647 < baseStart_812647 := by decide
  rcases family_descends (prefixWord ++ tailWord_812647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812650 : List Nat := [3, 1, 3, 2, 1, 4, 2, 5]
def baseStart_812650 : Nat := 118140960795 + 812650 * 2 ^ 59
def prefixEnd_812650 : Nat := 4983230072969 + 3 ^ 40 * 812650 * 2
def baseEnd_812650 : Nat := 61819267240940849901881

theorem tailTrace_812650 : CollatzResearch.WordTrace tailWord_812650 prefixEnd_812650 61819267240940849901881 := by
  unfold tailWord_812650
  simp only [CollatzResearch.WordTrace]
  refine ⟨7409945126478828603876851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19759853670610209610338269 7409945126478828603876851)
  ·
    refine ⟨11114917689718242905815277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7409945126478828603876851 11114917689718242905815277)
    ·
      refine ⟨4168094133644341089680729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11114917689718242905815277 4168094133644341089680729)
      ·
        refine ⟨3126070600233255817260547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4168094133644341089680729 3126070600233255817260547)
        ·
          refine ⟨4689105900349883725890821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3126070600233255817260547 4689105900349883725890821)
          ·
            refine ⟨879207356315603198604529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4689105900349883725890821 879207356315603198604529)
            ·
              refine ⟨659405517236702398953397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 879207356315603198604529 659405517236702398953397)
              ·
                refine ⟨61819267240940849901881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 659405517236702398953397 61819267240940849901881)
                ·
                  rfl

theorem cell21_812650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 5].length) (baseStart_812650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_812650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_812650 prefixEnd_812650 := by exact prefixLift 812650
  have htrace : WordTrace (prefixWord ++ tailWord_812650) baseStart_812650 baseEnd_812650 := by
    simpa [prefixWord, tailWord_812650, baseEnd_812650] using wordTrace_append hprefix tailTrace_812650
  have hstable : (prefixWord ++ tailWord_812650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812650).length < 2 ^ (prefixWord ++ tailWord_812650).sum := by decide
  have hdescent : baseEnd_812650 < baseStart_812650 := by decide
  rcases family_descends (prefixWord ++ tailWord_812650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812695 : List Nat := [1, 1, 3, 3, 2, 2, 4, 1, 4]
def baseStart_812695 : Nat := 118140960795 + 812695 * 2 ^ 59
def prefixEnd_812695 : Nat := 4983230072969 + 3 ^ 40 * 812695 * 2
def baseEnd_812695 : Nat := 185468071335912471455551

theorem tailTrace_812695 : CollatzResearch.WordTrace tailWord_812695 prefixEnd_812695 185468071335912471455551 := by
  unfold tailWord_812695
  simp only [CollatzResearch.WordTrace]
  refine ⟨29641421790752287100895539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19760947860501524733930359 29641421790752287100895539)
  ·
    refine ⟨44462132686128430651343309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29641421790752287100895539 44462132686128430651343309)
    ·
      refine ⟨16673299757298161494253741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44462132686128430651343309 16673299757298161494253741)
      ·
        refine ⟨6252487408986810560345153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16673299757298161494253741 6252487408986810560345153)
        ·
          refine ⟨4689365556740107920258865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6252487408986810560345153 4689365556740107920258865)
          ·
            refine ⟨3517024167555080940194149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4689365556740107920258865 3517024167555080940194149)
            ·
              refine ⟨659442031416577676286403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3517024167555080940194149 659442031416577676286403)
              ·
                refine ⟨989163047124866514429605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 659442031416577676286403 989163047124866514429605)
                ·
                  refine ⟨185468071335912471455551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 989163047124866514429605 185468071335912471455551)
                  ·
                    rfl

theorem cell21_812695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 1, 4].length) (baseStart_812695 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_812695 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_812695 prefixEnd_812695 := by exact prefixLift 812695
  have htrace : WordTrace (prefixWord ++ tailWord_812695) baseStart_812695 baseEnd_812695 := by
    simpa [prefixWord, tailWord_812695, baseEnd_812695] using wordTrace_append hprefix tailTrace_812695
  have hstable : (prefixWord ++ tailWord_812695).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812695).length < 2 ^ (prefixWord ++ tailWord_812695).sum := by decide
  have hdescent : baseEnd_812695 < baseStart_812695 := by decide
  rcases family_descends (prefixWord ++ tailWord_812695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812788 : List Nat := [2, 6, 1, 1, 1, 2, 1, 1, 6]
def baseStart_812788 : Nat := 118140960795 + 812788 * 2 ^ 59
def prefixEnd_812788 : Nat := 4983230072969 + 3 ^ 40 * 812788 * 2
def baseEnd_812788 : Nat := 185489295202964976405361

theorem tailTrace_812788 : CollatzResearch.WordTrace tailWord_812788 prefixEnd_812788 185489295202964976405361 := by
  unfold tailWord_812788
  simp only [CollatzResearch.WordTrace]
  refine ⟨14822406889707681992015509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19763209186276909322687345 14822406889707681992015509)
  ·
    refine ⟨694800322955047593375727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14822406889707681992015509 694800322955047593375727)
    ·
      refine ⟨1042200484432571390063591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 694800322955047593375727 1042200484432571390063591)
      ·
        refine ⟨1563300726648857085095387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1042200484432571390063591 1563300726648857085095387)
        ·
          refine ⟨2344951089973285627643081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1563300726648857085095387 2344951089973285627643081)
          ·
            refine ⟨1758713317479964220732311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2344951089973285627643081 1758713317479964220732311)
            ·
              refine ⟨2638069976219946331098467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1758713317479964220732311 2638069976219946331098467)
              ·
                refine ⟨3957104964329919496647701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2638069976219946331098467 3957104964329919496647701)
                ·
                  refine ⟨185489295202964976405361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3957104964329919496647701 185489295202964976405361)
                  ·
                    rfl

theorem cell21_812788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_812788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_812788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_812788 prefixEnd_812788 := by exact prefixLift 812788
  have htrace : WordTrace (prefixWord ++ tailWord_812788) baseStart_812788 baseEnd_812788 := by
    simpa [prefixWord, tailWord_812788, baseEnd_812788] using wordTrace_append hprefix tailTrace_812788
  have hstable : (prefixWord ++ tailWord_812788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812788).length < 2 ^ (prefixWord ++ tailWord_812788).sum := by decide
  have hdescent : baseEnd_812788 < baseStart_812788 := by decide
  rcases family_descends (prefixWord ++ tailWord_812788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812827 : List Nat := [1, 1, 1, 1, 1, 1, 4, 11]
def baseStart_812827 : Nat := 118140960795 + 812827 * 2 ^ 59
def prefixEnd_812827 : Nat := 4983230072969 + 3 ^ 40 * 812827 * 2
def baseEnd_812827 : Nat := 61832731844769858418427

theorem tailTrace_812827 : CollatzResearch.WordTrace tailWord_812827 prefixEnd_812827 61832731844769858418427 := by
  unfold tailWord_812827
  simp only [CollatzResearch.WordTrace]
  refine ⟨29646236226274073644700735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19764157484182715763133823 29646236226274073644700735)
  ·
    refine ⟨44469354339411110467051103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29646236226274073644700735 44469354339411110467051103)
    ·
      refine ⟨66704031509116665700576655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44469354339411110467051103 66704031509116665700576655)
      ·
        refine ⟨100056047263674998550864983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66704031509116665700576655 100056047263674998550864983)
        ·
          refine ⟨150084070895512497826297475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100056047263674998550864983 150084070895512497826297475)
          ·
            refine ⟨225126106343268746739446213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150084070895512497826297475 225126106343268746739446213)
            ·
              refine ⟨42211144939362890013646165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 225126106343268746739446213 42211144939362890013646165)
              ·
                refine ⟨61832731844769858418427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 42211144939362890013646165 61832731844769858418427)
                ·
                  rfl

theorem cell21_812827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 11].length) (baseStart_812827 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_812827 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_812827 prefixEnd_812827 := by exact prefixLift 812827
  have htrace : WordTrace (prefixWord ++ tailWord_812827) baseStart_812827 baseEnd_812827 := by
    simpa [prefixWord, tailWord_812827, baseEnd_812827] using wordTrace_append hprefix tailTrace_812827
  have hstable : (prefixWord ++ tailWord_812827).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812827).length < 2 ^ (prefixWord ++ tailWord_812827).sum := by decide
  have hdescent : baseEnd_812827 < baseStart_812827 := by decide
  rcases family_descends (prefixWord ++ tailWord_812827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812833 : List Nat := [1, 2, 3, 2, 1, 5, 1, 3, 3]
def baseStart_812833 : Nat := 118140960795 + 812833 * 2 ^ 59
def prefixEnd_812833 : Nat := 4983230072969 + 3 ^ 40 * 812833 * 2
def baseEnd_812833 : Nat := 185499564816054898155269

theorem tailTrace_812833 : CollatzResearch.WordTrace tailWord_812833 prefixEnd_812833 185499564816054898155269 := by
  unfold tailWord_812833
  simp only [CollatzResearch.WordTrace]
  refine ⟨29646455064252336669419153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19764303376168224446279435 29646455064252336669419153)
  ·
    refine ⟨22234841298189252502064365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29646455064252336669419153 22234841298189252502064365)
    ·
      refine ⟨8338065486820969688274137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22234841298189252502064365 8338065486820969688274137)
      ·
        refine ⟨6253549115115727266205603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8338065486820969688274137 6253549115115727266205603)
        ·
          refine ⟨9380323672673590899308405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6253549115115727266205603 9380323672673590899308405)
          ·
            refine ⟨879405344313149146810163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9380323672673590899308405 879405344313149146810163)
            ·
              refine ⟨1319108016469723720215245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 879405344313149146810163 1319108016469723720215245)
              ·
                refine ⟨494665506176146395080717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1319108016469723720215245 494665506176146395080717)
                ·
                  refine ⟨185499564816054898155269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 494665506176146395080717 185499564816054898155269)
                  ·
                    rfl

theorem cell21_812833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 3, 3].length) (baseStart_812833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_812833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_812833 prefixEnd_812833 := by exact prefixLift 812833
  have htrace : WordTrace (prefixWord ++ tailWord_812833) baseStart_812833 baseEnd_812833 := by
    simpa [prefixWord, tailWord_812833, baseEnd_812833] using wordTrace_append hprefix tailTrace_812833
  have hstable : (prefixWord ++ tailWord_812833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812833).length < 2 ^ (prefixWord ++ tailWord_812833).sum := by decide
  have hdescent : baseEnd_812833 < baseStart_812833 := by decide
  rcases family_descends (prefixWord ++ tailWord_812833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812844 : List Nat := [2, 2, 1, 1, 1, 7, 7]
def baseStart_812844 : Nat := 118140960795 + 812844 * 2 ^ 59
def prefixEnd_812844 : Nat := 4983230072969 + 3 ^ 40 * 812844 * 2
def baseEnd_812844 : Nat := 20611341685102369274657

theorem tailTrace_812844 : CollatzResearch.WordTrace tailWord_812844 prefixEnd_812844 20611341685102369274657 := by
  unfold tailWord_812844
  simp only [CollatzResearch.WordTrace]
  refine ⟨14823428133606242774034793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19764570844808323698713057 14823428133606242774034793)
  ·
    refine ⟨11117571100204682080526095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14823428133606242774034793 11117571100204682080526095)
    ·
      refine ⟨16676356650307023120789143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11117571100204682080526095 16676356650307023120789143)
      ·
        refine ⟨25014534975460534681183715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16676356650307023120789143 25014534975460534681183715)
        ·
          refine ⟨37521802463190802021775573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25014534975460534681183715 37521802463190802021775573)
          ·
            refine ⟨879417245231034422385365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 37521802463190802021775573 879417245231034422385365)
            ·
              refine ⟨20611341685102369274657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 879417245231034422385365 20611341685102369274657)
              ·
                rfl

theorem cell21_812844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 7].length) (baseStart_812844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_812844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_812844 prefixEnd_812844 := by exact prefixLift 812844
  have htrace : WordTrace (prefixWord ++ tailWord_812844) baseStart_812844 baseEnd_812844 := by
    simpa [prefixWord, tailWord_812844, baseEnd_812844] using wordTrace_append hprefix tailTrace_812844
  have hstable : (prefixWord ++ tailWord_812844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812844).length < 2 ^ (prefixWord ++ tailWord_812844).sum := by decide
  have hdescent : baseEnd_812844 < baseStart_812844 := by decide
  rcases family_descends (prefixWord ++ tailWord_812844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812861 : List Nat := [1, 4, 1, 4, 1, 2, 2, 6]
def baseStart_812861 : Nat := 118140960795 + 812861 * 2 ^ 59
def prefixEnd_812861 : Nat := 4983230072969 + 3 ^ 40 * 812861 * 2
def baseEnd_812861 : Nat := 61835318265844357229515

theorem tailTrace_812861 : CollatzResearch.WordTrace tailWord_812861 prefixEnd_812861 61835318265844357229515 := by
  unfold tailWord_812861
  simp only [CollatzResearch.WordTrace]
  refine ⟨29647476308150897451438437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19764984205433931634292291 29647476308150897451438437)
  ·
    refine ⟨5558901807778293272144707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29647476308150897451438437 5558901807778293272144707)
    ·
      refine ⟨8338352711667439908217061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5558901807778293272144707 8338352711667439908217061)
      ·
        refine ⟨1563441133437644982790699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8338352711667439908217061 1563441133437644982790699)
        ·
          refine ⟨2345161700156467474186049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1563441133437644982790699 2345161700156467474186049)
          ·
            refine ⟨1758871275117350605639537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2345161700156467474186049 1758871275117350605639537)
            ·
              refine ⟨1319153456338012954229653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1758871275117350605639537 1319153456338012954229653)
              ·
                refine ⟨61835318265844357229515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1319153456338012954229653 61835318265844357229515)
                ·
                  rfl

theorem cell21_812861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 6].length) (baseStart_812861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_812861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_812861 prefixEnd_812861 := by exact prefixLift 812861
  have htrace : WordTrace (prefixWord ++ tailWord_812861) baseStart_812861 baseEnd_812861 := by
    simpa [prefixWord, tailWord_812861, baseEnd_812861] using wordTrace_append hprefix tailTrace_812861
  have hstable : (prefixWord ++ tailWord_812861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812861).length < 2 ^ (prefixWord ++ tailWord_812861).sum := by decide
  have hdescent : baseEnd_812861 < baseStart_812861 := by decide
  rcases family_descends (prefixWord ++ tailWord_812861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812909 : List Nat := [1, 5, 1, 1, 1, 1, 6, 2, 3]
def baseStart_812909 : Nat := 118140960795 + 812909 * 2 ^ 59
def prefixEnd_812909 : Nat := 4983230072969 + 3 ^ 40 * 812909 * 2
def baseEnd_812909 : Nat := 185516909051495654888447

theorem tailTrace_812909 : CollatzResearch.WordTrace tailWord_812909 prefixEnd_812909 185516909051495654888447 := by
  unfold tailWord_812909
  simp only [CollatzResearch.WordTrace]
  refine ⟨29649227011977001649185781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19766151341318001099457187 29649227011977001649185781)
  ·
    refine ⟨2779615032372843904611167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29649227011977001649185781 2779615032372843904611167)
    ·
      refine ⟨4169422548559265856916751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2779615032372843904611167 4169422548559265856916751)
      ·
        refine ⟨6254133822838898785375127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4169422548559265856916751 6254133822838898785375127)
        ·
          refine ⟨9381200734258348178062691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6254133822838898785375127 9381200734258348178062691)
          ·
            refine ⟨14071801101387522267094037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9381200734258348178062691 14071801101387522267094037)
            ·
              refine ⟨659615676627540106270033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14071801101387522267094037 659615676627540106270033)
              ·
                refine ⟨494711757470655079702525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 659615676627540106270033 494711757470655079702525)
                ·
                  refine ⟨185516909051495654888447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 494711757470655079702525 185516909051495654888447)
                  ·
                    rfl

theorem cell21_812909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_812909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_812909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_812909 prefixEnd_812909 := by exact prefixLift 812909
  have htrace : WordTrace (prefixWord ++ tailWord_812909) baseStart_812909 baseEnd_812909 := by
    simpa [prefixWord, tailWord_812909, baseEnd_812909] using wordTrace_append hprefix tailTrace_812909
  have hstable : (prefixWord ++ tailWord_812909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812909).length < 2 ^ (prefixWord ++ tailWord_812909).sum := by decide
  have hdescent : baseEnd_812909 < baseStart_812909 := by decide
  rcases family_descends (prefixWord ++ tailWord_812909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812974 : List Nat := [4, 1, 5, 1, 1, 1, 3, 1, 4]
def baseStart_812974 : Nat := 118140960795 + 812974 * 2 ^ 59
def prefixEnd_812974 : Nat := 4983230072969 + 3 ^ 40 * 812974 * 2
def baseEnd_812974 : Nat := 185531742937069986304981

theorem tailTrace_812974 : CollatzResearch.WordTrace tailWord_812974 prefixEnd_812974 185531742937069986304981 := by
  unfold tailWord_812974
  simp only [CollatzResearch.WordTrace]
  refine ⟨3706449719592689718787747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19767731837827678500201317 3706449719592689718787747)
  ·
    refine ⟨5559674579389034578181621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3706449719592689718787747 5559674579389034578181621)
    ·
      refine ⟨521219491817721991704527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5559674579389034578181621 521219491817721991704527)
      ·
        refine ⟨781829237726582987556791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 521219491817721991704527 781829237726582987556791)
        ·
          refine ⟨1172743856589874481335187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 781829237726582987556791 1172743856589874481335187)
          ·
            refine ⟨1759115784884811722002781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1172743856589874481335187 1759115784884811722002781)
            ·
              refine ⟨659668419331804395751043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1759115784884811722002781 659668419331804395751043)
              ·
                refine ⟨989502628997706593626565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 659668419331804395751043 989502628997706593626565)
                ·
                  refine ⟨185531742937069986304981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 989502628997706593626565 185531742937069986304981)
                  ·
                    rfl

theorem cell21_812974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 1, 4].length) (baseStart_812974 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_812974 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_812974 prefixEnd_812974 := by exact prefixLift 812974
  have htrace : WordTrace (prefixWord ++ tailWord_812974) baseStart_812974 baseEnd_812974 := by
    simpa [prefixWord, tailWord_812974, baseEnd_812974] using wordTrace_append hprefix tailTrace_812974
  have hstable : (prefixWord ++ tailWord_812974).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812974).length < 2 ^ (prefixWord ++ tailWord_812974).sum := by decide
  have hdescent : baseEnd_812974 < baseStart_812974 := by decide
  rcases family_descends (prefixWord ++ tailWord_812974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812979 : List Nat := [1, 1, 1, 2, 3, 1, 4, 8]
def baseStart_812979 : Nat := 118140960795 + 812979 * 2 ^ 59
def prefixEnd_812979 : Nat := 4983230072969 + 3 ^ 40 * 812979 * 2
def baseEnd_812979 : Nat := 61844294668397029573879

theorem tailTrace_812979 : CollatzResearch.WordTrace tailWord_812979 prefixEnd_812979 61844294668397029573879 := by
  unfold tailWord_812979
  simp only [CollatzResearch.WordTrace]
  refine ⟨29651780121723403604233991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19767853414482269069489327 29651780121723403604233991)
  ·
    refine ⟨44477670182585105406350987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29651780121723403604233991 44477670182585105406350987)
    ·
      refine ⟨66716505273877658109526481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44477670182585105406350987 66716505273877658109526481)
      ·
        refine ⟨50037378955408243582144861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66716505273877658109526481 50037378955408243582144861)
        ·
          refine ⟨18764017108278091343304323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50037378955408243582144861 18764017108278091343304323)
          ·
            refine ⟨28146025662417137014956485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18764017108278091343304323 28146025662417137014956485)
            ·
              refine ⟨5277379811703213190304341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28146025662417137014956485 5277379811703213190304341)
              ·
                refine ⟨61844294668397029573879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5277379811703213190304341 61844294668397029573879)
                ·
                  rfl

theorem cell21_812979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 8].length) (baseStart_812979 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_812979 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_812979 prefixEnd_812979 := by exact prefixLift 812979
  have htrace : WordTrace (prefixWord ++ tailWord_812979) baseStart_812979 baseEnd_812979 := by
    simpa [prefixWord, tailWord_812979, baseEnd_812979] using wordTrace_append hprefix tailTrace_812979
  have hstable : (prefixWord ++ tailWord_812979).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812979).length < 2 ^ (prefixWord ++ tailWord_812979).sum := by decide
  have hdescent : baseEnd_812979 < baseStart_812979 := by decide
  rcases family_descends (prefixWord ++ tailWord_812979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813027 : List Nat := [1, 1, 1, 6, 1, 2, 3, 1, 5]
def baseStart_813027 : Nat := 118140960795 + 813027 * 2 ^ 59
def prefixEnd_813027 : Nat := 4983230072969 + 3 ^ 40 * 813027 * 2
def baseEnd_813027 : Nat := 185543838259153671921539

theorem tailTrace_813027 : CollatzResearch.WordTrace tailWord_813027 prefixEnd_813027 185543838259153671921539 := by
  unfold tailWord_813027
  simp only [CollatzResearch.WordTrace]
  refine ⟨29653530825549507801981335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19769020550366338534654223 29653530825549507801981335)
  ·
    refine ⟨44480296238324261702972003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29653530825549507801981335 44480296238324261702972003)
    ·
      refine ⟨66720444357486392554458005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44480296238324261702972003 66720444357486392554458005)
      ·
        refine ⟨3127520829257174650990219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 66720444357486392554458005 3127520829257174650990219)
        ·
          refine ⟨4691281243885761976485329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3127520829257174650990219 4691281243885761976485329)
          ·
            refine ⟨3518460932914321482363997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4691281243885761976485329 3518460932914321482363997)
            ·
              refine ⟨1319422849842870555886499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3518460932914321482363997 1319422849842870555886499)
              ·
                refine ⟨1979134274764305833829749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1319422849842870555886499 1979134274764305833829749)
                ·
                  refine ⟨185543838259153671921539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1979134274764305833829749 185543838259153671921539)
                  ·
                    rfl

theorem cell21_813027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 5].length) (baseStart_813027 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_813027 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_813027 prefixEnd_813027 := by exact prefixLift 813027
  have htrace : WordTrace (prefixWord ++ tailWord_813027) baseStart_813027 baseEnd_813027 := by
    simpa [prefixWord, tailWord_813027, baseEnd_813027] using wordTrace_append hprefix tailTrace_813027
  have hstable : (prefixWord ++ tailWord_813027).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813027).length < 2 ^ (prefixWord ++ tailWord_813027).sum := by decide
  have hdescent : baseEnd_813027 < baseStart_813027 := by decide
  rcases family_descends (prefixWord ++ tailWord_813027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813089 : List Nat := [1, 2, 3, 2, 4, 2, 1, 6]
def baseStart_813089 : Nat := 118140960795 + 813089 * 2 ^ 59
def prefixEnd_813089 : Nat := 4983230072969 + 3 ^ 40 * 813089 * 2
def baseEnd_813089 : Nat := 61852662501285113962693

theorem tailTrace_813089 : CollatzResearch.WordTrace tailWord_813089 prefixEnd_813089 61852662501285113962693 := by
  unfold tailWord_813089
  simp only [CollatzResearch.WordTrace]
  refine ⟨29655792151324892390738321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19770528100883261593825547 29655792151324892390738321)
  ·
    refine ⟨22241844113493669293053741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29655792151324892390738321 22241844113493669293053741)
    ·
      refine ⟨8340691542560125984895153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22241844113493669293053741 8340691542560125984895153)
      ·
        refine ⟨6255518656920094488671365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8340691542560125984895153 6255518656920094488671365)
        ·
          refine ⟨1172909748172517716625881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6255518656920094488671365 1172909748172517716625881)
          ·
            refine ⟨879682311129388287469411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1172909748172517716625881 879682311129388287469411)
            ·
              refine ⟨1319523466694082431204117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 879682311129388287469411 1319523466694082431204117)
              ·
                refine ⟨61852662501285113962693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1319523466694082431204117 61852662501285113962693)
                ·
                  rfl

theorem cell21_813089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 6].length) (baseStart_813089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_813089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_813089 prefixEnd_813089 := by exact prefixLift 813089
  have htrace : WordTrace (prefixWord ++ tailWord_813089) baseStart_813089 baseEnd_813089 := by
    simpa [prefixWord, tailWord_813089, baseEnd_813089] using wordTrace_append hprefix tailTrace_813089
  have hstable : (prefixWord ++ tailWord_813089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813089).length < 2 ^ (prefixWord ++ tailWord_813089).sum := by decide
  have hdescent : baseEnd_813089 < baseStart_813089 := by decide
  rcases family_descends (prefixWord ++ tailWord_813089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813117 : List Nat := [1, 4, 1, 3, 1, 1, 2, 2, 6]
def baseStart_813117 : Nat := 118140960795 + 813117 * 2 ^ 59
def prefixEnd_813117 : Nat := 4983230072969 + 3 ^ 40 * 813117 * 2
def baseEnd_813117 : Nat := 185564377485333515421355

theorem tailTrace_813117 : CollatzResearch.WordTrace tailWord_813117 prefixEnd_813117 185564377485333515421355 := by
  unfold tailWord_813117
  simp only [CollatzResearch.WordTrace]
  refine ⟨29656813395223453172757605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19771208930148968781838403 29656813395223453172757605)
  ·
    refine ⟨5560652511604397469892051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29656813395223453172757605 5560652511604397469892051)
    ·
      refine ⟨8340978767406596204838077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5560652511604397469892051 8340978767406596204838077)
      ·
        refine ⟨3127867037777473576814279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8340978767406596204838077 3127867037777473576814279)
        ·
          refine ⟨4691800556666210365221419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3127867037777473576814279 4691800556666210365221419)
          ·
            refine ⟨7037700834999315547832129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4691800556666210365221419 7037700834999315547832129)
            ·
              refine ⟨5278275626249486660874097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7037700834999315547832129 5278275626249486660874097)
              ·
                refine ⟨3958706719687114995655573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5278275626249486660874097 3958706719687114995655573)
                ·
                  refine ⟨185564377485333515421355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3958706719687114995655573 185564377485333515421355)
                  ·
                    rfl

theorem cell21_813117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_813117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_813117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_813117 prefixEnd_813117 := by exact prefixLift 813117
  have htrace : WordTrace (prefixWord ++ tailWord_813117) baseStart_813117 baseEnd_813117 := by
    simpa [prefixWord, tailWord_813117, baseEnd_813117] using wordTrace_append hprefix tailTrace_813117
  have hstable : (prefixWord ++ tailWord_813117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813117).length < 2 ^ (prefixWord ++ tailWord_813117).sum := by decide
  have hdescent : baseEnd_813117 < baseStart_813117 := by decide
  rcases family_descends (prefixWord ++ tailWord_813117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813120 : List Nat := [2, 1, 1, 2, 2, 5, 2, 3, 3]
def baseStart_813120 : Nat := 118140960795 + 813120 * 2 ^ 59
def prefixEnd_813120 : Nat := 4983230072969 + 3 ^ 40 * 813120 * 2
def baseEnd_813120 : Nat := 185565062126206176871349

theorem tailTrace_813120 : CollatzResearch.WordTrace tailWord_813120 prefixEnd_813120 185565062126206176871349 := by
  unfold tailWord_813120
  simp only [CollatzResearch.WordTrace]
  refine ⟨14828461407106292342558407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19771281876141723123411209 14828461407106292342558407)
  ·
    refine ⟨22242692110659438513837611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14828461407106292342558407 22242692110659438513837611)
    ·
      refine ⟨33364038165989157770756417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22242692110659438513837611 33364038165989157770756417)
      ·
        refine ⟨25023028624491868328067313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33364038165989157770756417 25023028624491868328067313)
        ·
          refine ⟨18767271468368901246050485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25023028624491868328067313 18767271468368901246050485)
          ·
            refine ⟨1759431700159584491817233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18767271468368901246050485 1759431700159584491817233)
            ·
              refine ⟨1319573775119688368862925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1759431700159584491817233 1319573775119688368862925)
              ·
                refine ⟨494840165669883138323597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1319573775119688368862925 494840165669883138323597)
                ·
                  refine ⟨185565062126206176871349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 494840165669883138323597 185565062126206176871349)
                  ·
                    rfl

theorem cell21_813120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 3, 3].length) (baseStart_813120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_813120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_813120 prefixEnd_813120 := by exact prefixLift 813120
  have htrace : WordTrace (prefixWord ++ tailWord_813120) baseStart_813120 baseEnd_813120 := by
    simpa [prefixWord, tailWord_813120, baseEnd_813120] using wordTrace_append hprefix tailTrace_813120
  have hstable : (prefixWord ++ tailWord_813120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813120).length < 2 ^ (prefixWord ++ tailWord_813120).sum := by decide
  have hdescent : baseEnd_813120 < baseStart_813120 := by decide
  rcases family_descends (prefixWord ++ tailWord_813120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813134 : List Nat := [4, 1, 1, 1, 1, 4, 3, 2, 4]
def baseStart_813134 : Nat := 118140960795 + 813134 * 2 ^ 59
def prefixEnd_813134 : Nat := 4983230072969 + 3 ^ 40 * 813134 * 2
def baseEnd_813134 : Nat := 185568257116945263637987

theorem tailTrace_813134 : CollatzResearch.WordTrace tailWord_813134 prefixEnd_813134 185568257116945263637987 := by
  unfold tailWord_813134
  simp only [CollatzResearch.WordTrace]
  refine ⟨3707179179520233134515807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19771622290774576717417637 3707179179520233134515807)
  ·
    refine ⟨5560768769280349701773711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3707179179520233134515807 5560768769280349701773711)
    ·
      refine ⟨8341153153920524552660567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5560768769280349701773711 8341153153920524552660567)
      ·
        refine ⟨12511729730880786828990851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8341153153920524552660567 12511729730880786828990851)
        ·
          refine ⟨18767594596321180243486277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12511729730880786828990851 18767594596321180243486277)
          ·
            refine ⟨3518923986810221295653677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18767594596321180243486277 3518923986810221295653677)
            ·
              refine ⟨1319596495053832985870129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3518923986810221295653677 1319596495053832985870129)
              ·
                refine ⟨989697371290374739402597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1319596495053832985870129 989697371290374739402597)
                ·
                  refine ⟨185568257116945263637987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 989697371290374739402597 185568257116945263637987)
                  ·
                    rfl

theorem cell21_813134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_813134 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_813134 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_813134 prefixEnd_813134 := by exact prefixLift 813134
  have htrace : WordTrace (prefixWord ++ tailWord_813134) baseStart_813134 baseEnd_813134 := by
    simpa [prefixWord, tailWord_813134, baseEnd_813134] using wordTrace_append hprefix tailTrace_813134
  have hstable : (prefixWord ++ tailWord_813134).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813134).length < 2 ^ (prefixWord ++ tailWord_813134).sum := by decide
  have hdescent : baseEnd_813134 < baseStart_813134 := by decide
  rcases family_descends (prefixWord ++ tailWord_813134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813193 : List Nat := [1, 2, 1, 1, 4, 2, 2, 4, 4]
def baseStart_813193 : Nat := 118140960795 + 813193 * 2 ^ 59
def prefixEnd_813193 : Nat := 4983230072969 + 3 ^ 40 * 813193 * 2
def baseEnd_813193 : Nat := 185581721720774272154533

theorem tailTrace_813193 : CollatzResearch.WordTrace tailWord_813193 prefixEnd_813193 185581721720774272154533 := by
  unfold tailWord_813193
  simp only [CollatzResearch.WordTrace]
  refine ⟨29659585342948118152524233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19773056895298745435016155 29659585342948118152524233)
  ·
    refine ⟨22244689007211088614393175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29659585342948118152524233 22244689007211088614393175)
    ·
      refine ⟨33367033510816632921589763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22244689007211088614393175 33367033510816632921589763)
      ·
        refine ⟨50050550266224949382384645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33367033510816632921589763 50050550266224949382384645)
        ·
          refine ⟨9384478174917178009197121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50050550266224949382384645 9384478174917178009197121)
          ·
            refine ⟨7038358631187883506897841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9384478174917178009197121 7038358631187883506897841)
            ·
              refine ⟨5278768973390912630173381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7038358631187883506897841 5278768973390912630173381)
              ·
                refine ⟨989769182510796118157509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5278768973390912630173381 989769182510796118157509)
                ·
                  refine ⟨185581721720774272154533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 989769182510796118157509 185581721720774272154533)
                  ·
                    rfl

theorem cell21_813193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4, 4].length) (baseStart_813193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_813193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_813193 prefixEnd_813193 := by exact prefixLift 813193
  have htrace : WordTrace (prefixWord ++ tailWord_813193) baseStart_813193 baseEnd_813193 := by
    simpa [prefixWord, tailWord_813193, baseEnd_813193] using wordTrace_append hprefix tailTrace_813193
  have hstable : (prefixWord ++ tailWord_813193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813193).length < 2 ^ (prefixWord ++ tailWord_813193).sum := by decide
  have hdescent : baseEnd_813193 < baseStart_813193 := by decide
  rcases family_descends (prefixWord ++ tailWord_813193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813348 : List Nat := [2, 3, 1, 3, 1, 2, 3, 3, 3]
def baseStart_813348 : Nat := 118140960795 + 813348 * 2 ^ 59
def prefixEnd_813348 : Nat := 4983230072969 + 3 ^ 40 * 813348 * 2
def baseEnd_813348 : Nat := 185617094832528447070883

theorem tailTrace_813348 : CollatzResearch.WordTrace tailWord_813348 prefixEnd_813348 185617094832528447070883 := by
  unfold tailWord_813348
  simp only [CollatzResearch.WordTrace]
  refine ⟨14832619328693289812208349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19776825771591053082944465 14832619328693289812208349)
  ·
    refine ⟨5562232248259983679578131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14832619328693289812208349 5562232248259983679578131)
    ·
      refine ⟨8343348372389975519367197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5562232248259983679578131 8343348372389975519367197)
      ·
        refine ⟨3128755639646240819762699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8343348372389975519367197 3128755639646240819762699)
        ·
          refine ⟨4693133459469361229644049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3128755639646240819762699 4693133459469361229644049)
          ·
            refine ⟨3519850094602020922233037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4693133459469361229644049 3519850094602020922233037)
            ·
              refine ⟨1319943785475757845837389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3519850094602020922233037 1319943785475757845837389)
              ·
                refine ⟨494978919553409192189021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1319943785475757845837389 494978919553409192189021)
                ·
                  refine ⟨185617094832528447070883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 494978919553409192189021 185617094832528447070883)
                  ·
                    rfl

theorem cell21_813348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 3, 3].length) (baseStart_813348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_813348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_813348 prefixEnd_813348 := by exact prefixLift 813348
  have htrace : WordTrace (prefixWord ++ tailWord_813348) baseStart_813348 baseEnd_813348 := by
    simpa [prefixWord, tailWord_813348, baseEnd_813348] using wordTrace_append hprefix tailTrace_813348
  have hstable : (prefixWord ++ tailWord_813348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813348).length < 2 ^ (prefixWord ++ tailWord_813348).sum := by decide
  have hdescent : baseEnd_813348 < baseStart_813348 := by decide
  rcases family_descends (prefixWord ++ tailWord_813348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813351 : List Nat := [1, 1, 8, 1, 2, 1, 7]
def baseStart_813351 : Nat := 118140960795 + 813351 * 2 ^ 59
def prefixEnd_813351 : Nat := 4983230072969 + 3 ^ 40 * 813351 * 2
def baseEnd_813351 : Nat := 20624197719266789835653

theorem tailTrace_813351 : CollatzResearch.WordTrace tailWord_813351 prefixEnd_813351 20624197719266789835653 := by
  unfold tailWord_813351
  simp only [CollatzResearch.WordTrace]
  refine ⟨29665348076375711136775907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19776898717583807424517271 29665348076375711136775907)
  ·
    refine ⟨44498022114563566705163861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29665348076375711136775907 44498022114563566705163861)
    ·
      refine ⟨521461196655041797326139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 44498022114563566705163861 521461196655041797326139)
      ·
        refine ⟨782191794982562695989209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 521461196655041797326139 782191794982562695989209)
        ·
          refine ⟨586643846236922021991907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 782191794982562695989209 586643846236922021991907)
          ·
            refine ⟨879965769355383032987861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 586643846236922021991907 879965769355383032987861)
            ·
              refine ⟨20624197719266789835653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 879965769355383032987861 20624197719266789835653)
              ·
                rfl

theorem cell21_813351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 7].length) (baseStart_813351 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_813351 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_813351 prefixEnd_813351 := by exact prefixLift 813351
  have htrace : WordTrace (prefixWord ++ tailWord_813351) baseStart_813351 baseEnd_813351 := by
    simpa [prefixWord, tailWord_813351, baseEnd_813351] using wordTrace_append hprefix tailTrace_813351
  have hstable : (prefixWord ++ tailWord_813351).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813351).length < 2 ^ (prefixWord ++ tailWord_813351).sum := by decide
  have hdescent : baseEnd_813351 < baseStart_813351 := by decide
  rcases family_descends (prefixWord ++ tailWord_813351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813424 : List Nat := [2, 1, 1, 1, 4, 3, 4, 2, 3]
def baseStart_813424 : Nat := 118140960795 + 813424 * 2 ^ 59
def prefixEnd_813424 : Nat := 4983230072969 + 3 ^ 40 * 813424 * 2
def baseEnd_813424 : Nat := 185634439067969203804061

theorem tailTrace_813424 : CollatzResearch.WordTrace tailWord_813424 prefixEnd_813424 185634439067969203804061 := by
  unfold tailWord_813424
  simp only [CollatzResearch.WordTrace]
  refine ⟨14834005302555622302091663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19778673736740829736122217 14834005302555622302091663)
  ·
    refine ⟨22251007953833433453137495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14834005302555622302091663 22251007953833433453137495)
    ·
      refine ⟨33376511930750150179706243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22251007953833433453137495 33376511930750150179706243)
      ·
        refine ⟨50064767896125225269559365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33376511930750150179706243 50064767896125225269559365)
        ·
          refine ⟨9387143980523479738042381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50064767896125225269559365 9387143980523479738042381)
          ·
            refine ⟨3520178992696304901765893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9387143980523479738042381 3520178992696304901765893)
            ·
              refine ⟨660033561130557169081105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3520178992696304901765893 660033561130557169081105)
              ·
                refine ⟨495025170847917876810829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 660033561130557169081105 495025170847917876810829)
                ·
                  refine ⟨185634439067969203804061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 495025170847917876810829 185634439067969203804061)
                  ·
                    rfl

theorem cell21_813424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 2, 3].length) (baseStart_813424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_813424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_813424 prefixEnd_813424 := by exact prefixLift 813424
  have htrace : WordTrace (prefixWord ++ tailWord_813424) baseStart_813424 baseEnd_813424 := by
    simpa [prefixWord, tailWord_813424, baseEnd_813424] using wordTrace_append hprefix tailTrace_813424
  have hstable : (prefixWord ++ tailWord_813424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813424).length < 2 ^ (prefixWord ++ tailWord_813424).sum := by decide
  have hdescent : baseEnd_813424 < baseStart_813424 := by decide
  rcases family_descends (prefixWord ++ tailWord_813424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813435 : List Nat := [1, 1, 1, 1, 1, 7, 3, 6]
def baseStart_813435 : Nat := 118140960795 + 813435 * 2 ^ 59
def prefixEnd_813435 : Nat := 4983230072969 + 3 ^ 40 * 813435 * 2
def baseEnd_813435 : Nat := 61878983139278543040235

theorem tailTrace_813435 : CollatzResearch.WordTrace tailWord_813435 prefixEnd_813435 61878983139278543040235 := by
  unfold tailWord_813435
  simp only [CollatzResearch.WordTrace]
  refine ⟨29668411808071393482833759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19778941205380928988555839 29668411808071393482833759)
  ·
    refine ⟨44502617712107090224250639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29668411808071393482833759 44502617712107090224250639)
    ·
      refine ⟨66753926568160635336375959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44502617712107090224250639 66753926568160635336375959)
      ·
        refine ⟨100130889852240953004563939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66753926568160635336375959 100130889852240953004563939)
        ·
          refine ⟨150196334778361429506845909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100130889852240953004563939 150196334778361429506845909)
          ·
            refine ⟨3520226596367846004066701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 150196334778361429506845909 3520226596367846004066701)
            ·
              refine ⟨1320084973637942251525013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3520226596367846004066701 1320084973637942251525013)
              ·
                refine ⟨61878983139278543040235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1320084973637942251525013 61878983139278543040235)
                ·
                  rfl

theorem cell21_813435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 6].length) (baseStart_813435 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_813435 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_813435 prefixEnd_813435 := by exact prefixLift 813435
  have htrace : WordTrace (prefixWord ++ tailWord_813435) baseStart_813435 baseEnd_813435 := by
    simpa [prefixWord, tailWord_813435, baseEnd_813435] using wordTrace_append hprefix tailTrace_813435
  have hstable : (prefixWord ++ tailWord_813435).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813435).length < 2 ^ (prefixWord ++ tailWord_813435).sum := by decide
  have hdescent : baseEnd_813435 < baseStart_813435 := by decide
  rcases family_descends (prefixWord ++ tailWord_813435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813452 : List Nat := [2, 2, 1, 2, 1, 5, 3, 5]
def baseStart_813452 : Nat := 118140960795 + 813452 * 2 ^ 59
def prefixEnd_813452 : Nat := 4983230072969 + 3 ^ 40 * 813452 * 2
def baseEnd_813452 : Nat := 61880276349815792445779

theorem tailTrace_813452 : CollatzResearch.WordTrace tailWord_813452 prefixEnd_813452 61880276349815792445779 := by
  unfold tailWord_813452
  simp only [CollatzResearch.WordTrace]
  refine ⟨14834515924504902693101305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19779354566006536924135073 14834515924504902693101305)
  ·
    refine ⟨11125886943378677019825979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14834515924504902693101305 11125886943378677019825979)
    ·
      refine ⟨16688830415068015529738969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11125886943378677019825979 16688830415068015529738969)
      ·
        refine ⟨12516622811301011647304227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16688830415068015529738969 12516622811301011647304227)
        ·
          refine ⟨18774934216951517470956341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12516622811301011647304227 18774934216951517470956341)
          ·
            refine ⟨1760150082839204762902157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18774934216951517470956341 1760150082839204762902157)
            ·
              refine ⟨660056281064701786088309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1760150082839204762902157 660056281064701786088309)
              ·
                refine ⟨61880276349815792445779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 660056281064701786088309 61880276349815792445779)
                ·
                  rfl

theorem cell21_813452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 5].length) (baseStart_813452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_813452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_813452 prefixEnd_813452 := by exact prefixLift 813452
  have htrace : WordTrace (prefixWord ++ tailWord_813452) baseStart_813452 baseEnd_813452 := by
    simpa [prefixWord, tailWord_813452, baseEnd_813452] using wordTrace_append hprefix tailTrace_813452
  have hstable : (prefixWord ++ tailWord_813452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813452).length < 2 ^ (prefixWord ++ tailWord_813452).sum := by decide
  have hdescent : baseEnd_813452 < baseStart_813452 := by decide
  rcases family_descends (prefixWord ++ tailWord_813452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813511 : List Nat := [1, 1, 4, 1, 1, 5, 1, 7]
def baseStart_813511 : Nat := 118140960795 + 813511 * 2 ^ 59
def prefixEnd_813511 : Nat := 4983230072969 + 3 ^ 40 * 813511 * 2
def baseEnd_813511 : Nat := 61884764551092128617961

theorem tailTrace_813511 : CollatzResearch.WordTrace tailWord_813511 prefixEnd_813511 61884764551092128617961 := by
  unfold tailWord_813511
  simp only [CollatzResearch.WordTrace]
  refine ⟨29671183755796058462600387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19780789170530705641733591 29671183755796058462600387)
  ·
    refine ⟨44506775633694087693900581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29671183755796058462600387 44506775633694087693900581)
    ·
      refine ⟨8345020431317641442606359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44506775633694087693900581 8345020431317641442606359)
      ·
        refine ⟨12517530646976462163909539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8345020431317641442606359 12517530646976462163909539)
        ·
          refine ⟨18776295970464693245864309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12517530646976462163909539 18776295970464693245864309)
          ·
            refine ⟨1760277747231064991799779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18776295970464693245864309 1760277747231064991799779)
            ·
              refine ⟨2640416620846597487699669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1760277747231064991799779 2640416620846597487699669)
              ·
                refine ⟨61884764551092128617961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2640416620846597487699669 61884764551092128617961)
                ·
                  rfl

theorem cell21_813511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 7].length) (baseStart_813511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_813511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_813511 prefixEnd_813511 := by exact prefixLift 813511
  have htrace : WordTrace (prefixWord ++ tailWord_813511) baseStart_813511 baseEnd_813511 := by
    simpa [prefixWord, tailWord_813511, baseEnd_813511] using wordTrace_append hprefix tailTrace_813511
  have hstable : (prefixWord ++ tailWord_813511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813511).length < 2 ^ (prefixWord ++ tailWord_813511).sum := by decide
  have hdescent : baseEnd_813511 < baseStart_813511 := by decide
  rcases family_descends (prefixWord ++ tailWord_813511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813649 : List Nat := [1, 2, 2, 1, 3, 3, 3, 2, 4]
def baseStart_813649 : Nat := 118140960795 + 813649 * 2 ^ 59
def prefixEnd_813649 : Nat := 4983230072969 + 3 ^ 40 * 813649 * 2
def baseEnd_813649 : Nat := 185685787133418812553601

theorem tailTrace_813649 : CollatzResearch.WordTrace tailWord_813649 prefixEnd_813649 185685787133418812553601 := by
  unfold tailWord_813649
  simp only [CollatzResearch.WordTrace]
  refine ⟨29676217029296108031124001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19784144686197405354082667 29676217029296108031124001)
  ·
    refine ⟨22257162771972081023343001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29676217029296108031124001 22257162771972081023343001)
    ·
      refine ⟨16692872078979060767507251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22257162771972081023343001 16692872078979060767507251)
      ·
        refine ⟨25039308118468591151260877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16692872078979060767507251 25039308118468591151260877)
        ·
          refine ⟨9389740544425721681722829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25039308118468591151260877 9389740544425721681722829)
          ·
            refine ⟨3521152704159645630646061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9389740544425721681722829 3521152704159645630646061)
            ·
              refine ⟨1320432264059867111492273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3521152704159645630646061 1320432264059867111492273)
              ·
                refine ⟨990324198044900333619205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1320432264059867111492273 990324198044900333619205)
                ·
                  refine ⟨185685787133418812553601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 990324198044900333619205 185685787133418812553601)
                  ·
                    rfl

theorem cell21_813649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 4].length) (baseStart_813649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_813649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_813649 prefixEnd_813649 := by exact prefixLift 813649
  have htrace : WordTrace (prefixWord ++ tailWord_813649) baseStart_813649 baseEnd_813649 := by
    simpa [prefixWord, tailWord_813649, baseEnd_813649] using wordTrace_append hprefix tailTrace_813649
  have hstable : (prefixWord ++ tailWord_813649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813649).length < 2 ^ (prefixWord ++ tailWord_813649).sum := by decide
  have hdescent : baseEnd_813649 < baseStart_813649 := by decide
  rcases family_descends (prefixWord ++ tailWord_813649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813686 : List Nat := [5, 1, 1, 2, 4, 1, 1, 3, 3]
def baseStart_813686 : Nat := 118140960795 + 813686 * 2 ^ 59
def prefixEnd_813686 : Nat := 4983230072969 + 3 ^ 40 * 813686 * 2
def baseEnd_813686 : Nat := 185694231037514970436859

theorem tailTrace_813686 : CollatzResearch.WordTrace tailWord_813686 prefixEnd_813686 185694231037514970436859 := by
  unfold tailWord_813686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1854847908135128959388807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19785044353441375566813941 1854847908135128959388807)
  ·
    refine ⟨2782271862202693439083211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1854847908135128959388807 2782271862202693439083211)
    ·
      refine ⟨4173407793304040158624817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2782271862202693439083211 4173407793304040158624817)
      ·
        refine ⟨3130055844978030118968613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4173407793304040158624817 3130055844978030118968613)
        ·
          refine ⟨586885470933380647306615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3130055844978030118968613 586885470933380647306615)
          ·
            refine ⟨880328206400070970959923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 586885470933380647306615 880328206400070970959923)
            ·
              refine ⟨1320492309600106456439885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 880328206400070970959923 1320492309600106456439885)
              ·
                refine ⟨495184616100039921164957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1320492309600106456439885 495184616100039921164957)
                ·
                  refine ⟨185694231037514970436859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 495184616100039921164957 185694231037514970436859)
                  ·
                    rfl

theorem cell21_813686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_813686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_813686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_813686 prefixEnd_813686 := by exact prefixLift 813686
  have htrace : WordTrace (prefixWord ++ tailWord_813686) baseStart_813686 baseEnd_813686 := by
    simpa [prefixWord, tailWord_813686, baseEnd_813686] using wordTrace_append hprefix tailTrace_813686
  have hstable : (prefixWord ++ tailWord_813686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813686).length < 2 ^ (prefixWord ++ tailWord_813686).sum := by decide
  have hdescent : baseEnd_813686 < baseStart_813686 := by decide
  rcases family_descends (prefixWord ++ tailWord_813686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813936 : List Nat := [2, 1, 1, 1, 4, 1, 3, 4, 4]
def baseStart_813936 : Nat := 118140960795 + 813936 * 2 ^ 59
def prefixEnd_813936 : Nat := 4983230072969 + 3 ^ 40 * 813936 * 2
def baseEnd_813936 : Nat := 185751284443570091269681

theorem tailTrace_813936 : CollatzResearch.WordTrace tailWord_813936 prefixEnd_813936 185751284443570091269681 := by
  unfold tailWord_813936
  simp only [CollatzResearch.WordTrace]
  refine ⟨14843342389628178023410831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19791123186170904031214441 14843342389628178023410831)
  ·
    refine ⟨22265013584442267035116247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14843342389628178023410831 22265013584442267035116247)
    ·
      refine ⟨33397520376663400552674371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22265013584442267035116247 33397520376663400552674371)
      ·
        refine ⟨50096280564995100829011557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33397520376663400552674371 50096280564995100829011557)
        ·
          refine ⟨9393052605936581405439667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50096280564995100829011557 9393052605936581405439667)
          ·
            refine ⟨14089578908904872108159501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9393052605936581405439667 14089578908904872108159501)
            ·
              refine ⟨5283592090839327040559813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14089578908904872108159501 5283592090839327040559813)
              ·
                refine ⟨990673517032373820104965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5283592090839327040559813 990673517032373820104965)
                ·
                  refine ⟨185751284443570091269681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 990673517032373820104965 185751284443570091269681)
                  ·
                    rfl

theorem cell21_813936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4, 4].length) (baseStart_813936 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_813936 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_813936 prefixEnd_813936 := by exact prefixLift 813936
  have htrace : WordTrace (prefixWord ++ tailWord_813936) baseStart_813936 baseEnd_813936 := by
    simpa [prefixWord, tailWord_813936, baseEnd_813936] using wordTrace_append hprefix tailTrace_813936
  have hstable : (prefixWord ++ tailWord_813936).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813936).length < 2 ^ (prefixWord ++ tailWord_813936).sum := by decide
  have hdescent : baseEnd_813936 < baseStart_813936 := by decide
  rcases family_descends (prefixWord ++ tailWord_813936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813939 : List Nat := [1, 1, 1, 2, 2, 1, 8, 2, 3]
def baseStart_813939 : Nat := 118140960795 + 813939 * 2 ^ 59
def prefixEnd_813939 : Nat := 4983230072969 + 3 ^ 40 * 813939 * 2
def baseEnd_813939 : Nat := 185751969084442752719675

theorem tailTrace_813939 : CollatzResearch.WordTrace tailWord_813939 prefixEnd_813939 185751969084442752719675 := by
  unfold tailWord_813939
  simp only [CollatzResearch.WordTrace]
  refine ⟨29686794198245487559180871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19791196132163658372787247 29686794198245487559180871)
  ·
    refine ⟨44530191297368231338771307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29686794198245487559180871 44530191297368231338771307)
    ·
      refine ⟨66795286946052347008156961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44530191297368231338771307 66795286946052347008156961)
      ·
        refine ⟨50096465209539260256117721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66795286946052347008156961 50096465209539260256117721)
        ·
          refine ⟨37572348907154445192088291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50096465209539260256117721 37572348907154445192088291)
          ·
            refine ⟨56358523360731667788132437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37572348907154445192088291 56358523360731667788132437)
            ·
              refine ⟨660451445633574231892177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 56358523360731667788132437 660451445633574231892177)
              ·
                refine ⟨495338584225180673919133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 660451445633574231892177 495338584225180673919133)
                ·
                  refine ⟨185751969084442752719675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 495338584225180673919133 185751969084442752719675)
                  ·
                    rfl

theorem cell21_813939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 2, 3].length) (baseStart_813939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_813939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_813939 prefixEnd_813939 := by exact prefixLift 813939
  have htrace : WordTrace (prefixWord ++ tailWord_813939) baseStart_813939 baseEnd_813939 := by
    simpa [prefixWord, tailWord_813939, baseEnd_813939] using wordTrace_append hprefix tailTrace_813939
  have hstable : (prefixWord ++ tailWord_813939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813939).length < 2 ^ (prefixWord ++ tailWord_813939).sum := by decide
  have hdescent : baseEnd_813939 < baseStart_813939 := by decide
  rcases family_descends (prefixWord ++ tailWord_813939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813981 : List Nat := [1, 4, 2, 1, 2, 1, 1, 2, 7]
def baseStart_813981 : Nat := 118140960795 + 813981 * 2 ^ 59
def prefixEnd_813981 : Nat := 4983230072969 + 3 ^ 40 * 813981 * 2
def baseEnd_813981 : Nat := 185761554056660013019589

theorem tailTrace_813981 : CollatzResearch.WordTrace tailWord_813981 prefixEnd_813981 185761554056660013019589 := by
  unfold tailWord_813981
  simp only [CollatzResearch.WordTrace]
  refine ⟨29688326064093328732209797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19792217376062219154806531 29688326064093328732209797)
  ·
    refine ⟨5566561137017499137289337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29688326064093328732209797 5566561137017499137289337)
    ·
      refine ⟨4174920852763124352967003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5566561137017499137289337 4174920852763124352967003)
      ·
        refine ⟨6262381279144686529450505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4174920852763124352967003 6262381279144686529450505)
        ·
          refine ⟨4696785959358514897087879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6262381279144686529450505 4696785959358514897087879)
          ·
            refine ⟨7045178939037772345631819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4696785959358514897087879 7045178939037772345631819)
            ·
              refine ⟨10567768408556658518447729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7045178939037772345631819 10567768408556658518447729)
              ·
                refine ⟨7925826306417493888835797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10567768408556658518447729 7925826306417493888835797)
                ·
                  refine ⟨185761554056660013019589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7925826306417493888835797 185761554056660013019589)
                  ·
                    rfl

theorem cell21_813981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_813981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_813981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_813981 prefixEnd_813981 := by exact prefixLift 813981
  have htrace : WordTrace (prefixWord ++ tailWord_813981) baseStart_813981 baseEnd_813981 := by
    simpa [prefixWord, tailWord_813981, baseEnd_813981] using wordTrace_append hprefix tailTrace_813981
  have hstable : (prefixWord ++ tailWord_813981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813981).length < 2 ^ (prefixWord ++ tailWord_813981).sum := by decide
  have hdescent : baseEnd_813981 < baseStart_813981 := by decide
  rcases family_descends (prefixWord ++ tailWord_813981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813995 : List Nat := [1, 1, 1, 1, 2, 1, 1, 7, 6]
def baseStart_813995 : Nat := 118140960795 + 813995 * 2 ^ 59
def prefixEnd_813995 : Nat := 4983230072969 + 3 ^ 40 * 813995 * 2
def baseEnd_813995 : Nat := 185764749047399099786227

theorem tailTrace_813995 : CollatzResearch.WordTrace tailWord_813995 prefixEnd_813995 185764749047399099786227 := by
  unfold tailWord_813995
  simp only [CollatzResearch.WordTrace]
  refine ⟨29688836686042609123219439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19792557790695072748812959 29688836686042609123219439)
  ·
    refine ⟨44533255029063913684829159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29688836686042609123219439 44533255029063913684829159)
    ·
      refine ⟨66799882543595870527243739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44533255029063913684829159 66799882543595870527243739)
      ·
        refine ⟨100199823815393805790865609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66799882543595870527243739 100199823815393805790865609)
        ·
          refine ⟨75149867861545354343149207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100199823815393805790865609 75149867861545354343149207)
          ·
            refine ⟨112724801792318031514723811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75149867861545354343149207 112724801792318031514723811)
            ·
              refine ⟨169087202688477047272085717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112724801792318031514723811 169087202688477047272085717)
              ·
                refine ⟨3962981313011180795439509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 169087202688477047272085717 3962981313011180795439509)
                ·
                  refine ⟨185764749047399099786227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3962981313011180795439509 185764749047399099786227)
                  ·
                    rfl

theorem cell21_813995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 6].length) (baseStart_813995 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_813995 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_813995 prefixEnd_813995 := by exact prefixLift 813995
  have htrace : WordTrace (prefixWord ++ tailWord_813995) baseStart_813995 baseEnd_813995 := by
    simpa [prefixWord, tailWord_813995, baseEnd_813995] using wordTrace_append hprefix tailTrace_813995
  have hstable : (prefixWord ++ tailWord_813995).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813995).length < 2 ^ (prefixWord ++ tailWord_813995).sum := by decide
  have hdescent : baseEnd_813995 < baseStart_813995 := by decide
  rcases family_descends (prefixWord ++ tailWord_813995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814147 : List Nat := [1, 1, 1, 3, 1, 2, 4, 2, 6]
def baseStart_814147 : Nat := 118140960795 + 814147 * 2 ^ 59
def prefixEnd_814147 : Nat := 4983230072969 + 3 ^ 40 * 814147 * 2
def baseEnd_814147 : Nat := 185799437518280613252583

theorem tailTrace_814147 : CollatzResearch.WordTrace tailWord_814147 prefixEnd_814147 185799437518280613252583 := by
  unfold tailWord_814147
  simp only [CollatzResearch.WordTrace]
  refine ⟨29694380581491939082752695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19796253720994626055168463 29694380581491939082752695)
  ·
    refine ⟨44541570872237908624129043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29694380581491939082752695 44541570872237908624129043)
    ·
      refine ⟨66812356308356862936193565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44541570872237908624129043 66812356308356862936193565)
      ·
        refine ⟨25054633615633823601072587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66812356308356862936193565 25054633615633823601072587)
        ·
          refine ⟨37581950423450735401608881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25054633615633823601072587 37581950423450735401608881)
          ·
            refine ⟨28186462817588051551206661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37581950423450735401608881 28186462817588051551206661)
            ·
              refine ⟨5284961778297759665851249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28186462817588051551206661 5284961778297759665851249)
              ·
                refine ⟨3963721333723319749388437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5284961778297759665851249 3963721333723319749388437)
                ·
                  refine ⟨185799437518280613252583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3963721333723319749388437 185799437518280613252583)
                  ·
                    rfl

theorem cell21_814147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 6].length) (baseStart_814147 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_814147 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_814147 prefixEnd_814147 := by exact prefixLift 814147
  have htrace : WordTrace (prefixWord ++ tailWord_814147) baseStart_814147 baseEnd_814147 := by
    simpa [prefixWord, tailWord_814147, baseEnd_814147] using wordTrace_append hprefix tailTrace_814147
  have hstable : (prefixWord ++ tailWord_814147).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814147).length < 2 ^ (prefixWord ++ tailWord_814147).sum := by decide
  have hdescent : baseEnd_814147 < baseStart_814147 := by decide
  rcases family_descends (prefixWord ++ tailWord_814147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814181 : List Nat := [1, 3, 1, 3, 2, 1, 5, 1, 4]
def baseStart_814181 : Nat := 118140960795 + 814181 * 2 ^ 59
def prefixEnd_814181 : Nat := 4983230072969 + 3 ^ 40 * 814181 * 2
def baseEnd_814181 : Nat := 185807196781504109685847

theorem tailTrace_814181 : CollatzResearch.WordTrace tailWord_814181 prefixEnd_814181 185807196781504109685847 := by
  unfold tailWord_814181
  simp only [CollatzResearch.WordTrace]
  refine ⟨29695620663368762889490397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19797080442245841926326931 29695620663368762889490397)
  ·
    refine ⟨11135857748763286083558899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29695620663368762889490397 11135857748763286083558899)
    ·
      refine ⟨16703786623144929125338349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11135857748763286083558899 16703786623144929125338349)
      ·
        refine ⟨6263919983679348422001881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16703786623144929125338349 6263919983679348422001881)
        ·
          refine ⟨4697939987759511316501411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6263919983679348422001881 4697939987759511316501411)
          ·
            refine ⟨7046909981639266974752117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4697939987759511316501411 7046909981639266974752117)
            ·
              refine ⟨660647810778681278883011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7046909981639266974752117 660647810778681278883011)
              ·
                refine ⟨990971716168021918324517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 660647810778681278883011 990971716168021918324517)
                ·
                  refine ⟨185807196781504109685847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 990971716168021918324517 185807196781504109685847)
                  ·
                    rfl

theorem cell21_814181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 1, 4].length) (baseStart_814181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_814181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_814181 prefixEnd_814181 := by exact prefixLift 814181
  have htrace : WordTrace (prefixWord ++ tailWord_814181) baseStart_814181 baseEnd_814181 := by
    simpa [prefixWord, tailWord_814181, baseEnd_814181] using wordTrace_append hprefix tailTrace_814181
  have hstable : (prefixWord ++ tailWord_814181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814181).length < 2 ^ (prefixWord ++ tailWord_814181).sum := by decide
  have hdescent : baseEnd_814181 < baseStart_814181 := by decide
  rcases family_descends (prefixWord ++ tailWord_814181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814226 : List Nat := [3, 2, 3, 1, 1, 2, 3, 1, 5]
def baseStart_814226 : Nat := 118140960795 + 814226 * 2 ^ 59
def prefixEnd_814226 : Nat := 4983230072969 + 3 ^ 40 * 814226 * 2
def baseEnd_814226 : Nat := 185817466394594031435755

theorem tailTrace_814226 : CollatzResearch.WordTrace tailWord_814226 prefixEnd_814226 185817466394594031435755 := by
  unfold tailWord_814226
  simp only [CollatzResearch.WordTrace]
  refine ⟨7424315487051433893719633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19798174632137157049919021 7424315487051433893719633)
  ·
    refine ⟨5568236615288575420289725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7424315487051433893719633 5568236615288575420289725)
    ·
      refine ⟨2088088730733215782608647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5568236615288575420289725 2088088730733215782608647)
      ·
        refine ⟨3132133096099823673912971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2088088730733215782608647 3132133096099823673912971)
        ·
          refine ⟨4698199644149735510869457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3132133096099823673912971 4698199644149735510869457)
          ·
            refine ⟨3523649733112301633152093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4698199644149735510869457 3523649733112301633152093)
            ·
              refine ⟨1321368649917113112432035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3523649733112301633152093 1321368649917113112432035)
              ·
                refine ⟨1982052974875669668648053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1321368649917113112432035 1982052974875669668648053)
                ·
                  refine ⟨185817466394594031435755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1982052974875669668648053 185817466394594031435755)
                  ·
                    rfl

theorem cell21_814226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_814226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_814226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_814226 prefixEnd_814226 := by exact prefixLift 814226
  have htrace : WordTrace (prefixWord ++ tailWord_814226) baseStart_814226 baseEnd_814226 := by
    simpa [prefixWord, tailWord_814226, baseEnd_814226] using wordTrace_append hprefix tailTrace_814226
  have hstable : (prefixWord ++ tailWord_814226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814226).length < 2 ^ (prefixWord ++ tailWord_814226).sum := by decide
  have hdescent : baseEnd_814226 < baseStart_814226 := by decide
  rcases family_descends (prefixWord ++ tailWord_814226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814240 : List Nat := [2, 1, 1, 4, 2, 1, 3, 3, 4]
def baseStart_814240 : Nat := 118140960795 + 814240 * 2 ^ 59
def prefixEnd_814240 : Nat := 4983230072969 + 3 ^ 40 * 814240 * 2
def baseEnd_814240 : Nat := 185820661385333118202393

theorem tailTrace_814240 : CollatzResearch.WordTrace tailWord_814240 prefixEnd_814240 185820661385333118202393 := by
  unfold tailWord_814240
  simp only [CollatzResearch.WordTrace]
  refine ⟨14848886285077507982944087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19798515046770010643925449 14848886285077507982944087)
  ·
    refine ⟨22273329427616261974416131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14848886285077507982944087 22273329427616261974416131)
    ·
      refine ⟨33409994141424392961624197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22273329427616261974416131 33409994141424392961624197)
      ·
        refine ⟨6264373901517073680304537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33409994141424392961624197 6264373901517073680304537)
        ·
          refine ⟨4698280426137805260228403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6264373901517073680304537 4698280426137805260228403)
          ·
            refine ⟨7047420639206707890342605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4698280426137805260228403 7047420639206707890342605)
            ·
              refine ⟨2642782739702515458878477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7047420639206707890342605 2642782739702515458878477)
              ·
                refine ⟨991043527388443297079429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2642782739702515458878477 991043527388443297079429)
                ·
                  refine ⟨185820661385333118202393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 991043527388443297079429 185820661385333118202393)
                  ·
                    rfl

theorem cell21_814240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3, 4].length) (baseStart_814240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_814240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_814240 prefixEnd_814240 := by exact prefixLift 814240
  have htrace : WordTrace (prefixWord ++ tailWord_814240) baseStart_814240 baseEnd_814240 := by
    simpa [prefixWord, tailWord_814240, baseEnd_814240] using wordTrace_append hprefix tailTrace_814240
  have hstable : (prefixWord ++ tailWord_814240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814240).length < 2 ^ (prefixWord ++ tailWord_814240).sum := by decide
  have hdescent : baseEnd_814240 < baseStart_814240 := by decide
  rcases family_descends (prefixWord ++ tailWord_814240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814319 : List Nat := [1, 1, 2, 1, 7, 1, 2, 3, 3]
def baseStart_814319 : Nat := 118140960795 + 814319 * 2 ^ 59
def prefixEnd_814319 : Nat := 4983230072969 + 3 ^ 40 * 814319 * 2
def baseEnd_814319 : Nat := 185838690261646536385565

theorem tailTrace_814319 : CollatzResearch.WordTrace tailWord_814319 prefixEnd_814319 185838690261646536385565 := by
  unfold tailWord_814319
  simp only [CollatzResearch.WordTrace]
  refine ⟨29700653936868812458014011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19800435957912541638676007 29700653936868812458014011)
  ·
    refine ⟨44550980905303218687021017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29700653936868812458014011 44550980905303218687021017)
    ·
      refine ⟨33413235678977414015265763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44550980905303218687021017 33413235678977414015265763)
      ·
        refine ⟨50119853518466121022898645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33413235678977414015265763 50119853518466121022898645)
        ·
          refine ⟨1174684066839049711474187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 50119853518466121022898645 1174684066839049711474187)
          ·
            refine ⟨1762026100258574567211281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1174684066839049711474187 1762026100258574567211281)
            ·
              refine ⟨1321519575193930925408461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1762026100258574567211281 1321519575193930925408461)
              ·
                refine ⟨495569840697724097028173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1321519575193930925408461 495569840697724097028173)
                ·
                  refine ⟨185838690261646536385565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 495569840697724097028173 185838690261646536385565)
                  ·
                    rfl

theorem cell21_814319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 3, 3].length) (baseStart_814319 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_814319 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_814319 prefixEnd_814319 := by exact prefixLift 814319
  have htrace : WordTrace (prefixWord ++ tailWord_814319) baseStart_814319 baseEnd_814319 := by
    simpa [prefixWord, tailWord_814319, baseEnd_814319] using wordTrace_append hprefix tailTrace_814319
  have hstable : (prefixWord ++ tailWord_814319).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814319).length < 2 ^ (prefixWord ++ tailWord_814319).sum := by decide
  have hdescent : baseEnd_814319 < baseStart_814319 := by decide
  rcases family_descends (prefixWord ++ tailWord_814319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814446 : List Nat := [4, 1, 2, 4, 2, 1, 2, 2, 3]
def baseStart_814446 : Nat := 118140960795 + 814446 * 2 ^ 59
def prefixEnd_814446 : Nat := 4983230072969 + 3 ^ 40 * 814446 * 2
def baseEnd_814446 : Nat := 185867673391922537768639

theorem tailTrace_814446 : CollatzResearch.WordTrace tailWord_814446 prefixEnd_814446 185867673391922537768639 := by
  unfold tailWord_814446
  simp only [CollatzResearch.WordTrace]
  refine ⟨3713160750926089143485899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19803524004939142098591461 3713160750926089143485899)
  ·
    refine ⟨5569741126389133715228849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3713160750926089143485899 5569741126389133715228849)
    ·
      refine ⟨4177305844791850286421637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5569741126389133715228849 4177305844791850286421637)
      ·
        refine ⟨783244845898471928704057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4177305844791850286421637 783244845898471928704057)
        ·
          refine ⟨587433634423853946528043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 783244845898471928704057 587433634423853946528043)
          ·
            refine ⟨881150451635780919792065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 587433634423853946528043 881150451635780919792065)
            ·
              refine ⟨660862838726835689844049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 881150451635780919792065 660862838726835689844049)
              ·
                refine ⟨495647129045126767383037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 660862838726835689844049 495647129045126767383037)
                ·
                  refine ⟨185867673391922537768639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 495647129045126767383037 185867673391922537768639)
                  ·
                    rfl

theorem cell21_814446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 2, 3].length) (baseStart_814446 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_814446 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_814446 prefixEnd_814446 := by exact prefixLift 814446
  have htrace : WordTrace (prefixWord ++ tailWord_814446) baseStart_814446 baseEnd_814446 := by
    simpa [prefixWord, tailWord_814446, baseEnd_814446] using wordTrace_append hprefix tailTrace_814446
  have hstable : (prefixWord ++ tailWord_814446).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814446).length < 2 ^ (prefixWord ++ tailWord_814446).sum := by decide
  have hdescent : baseEnd_814446 < baseStart_814446 := by decide
  rcases family_descends (prefixWord ++ tailWord_814446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814468 : List Nat := [2, 3, 2, 1, 1, 3, 2, 3, 4]
def baseStart_814468 : Nat := 118140960795 + 814468 * 2 ^ 59
def prefixEnd_814468 : Nat := 4983230072969 + 3 ^ 40 * 814468 * 2
def baseEnd_814468 : Nat := 185872694091655388401927

theorem tailTrace_814468 : CollatzResearch.WordTrace tailWord_814468 prefixEnd_814468 185872694091655388401927 := by
  unfold tailWord_814468
  simp only [CollatzResearch.WordTrace]
  refine ⟨14853044206664505452594029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19804058942219340603458705 14853044206664505452594029)
  ·
    refine ⟨5569891577499189544722761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14853044206664505452594029 5569891577499189544722761)
    ·
      refine ⟨4177418683124392158542071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5569891577499189544722761 4177418683124392158542071)
      ·
        refine ⟨6266128024686588237813107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4177418683124392158542071 6266128024686588237813107)
        ·
          refine ⟨9399192037029882356719661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6266128024686588237813107 9399192037029882356719661)
          ·
            refine ⟨3524697013886205883769873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9399192037029882356719661 3524697013886205883769873)
            ·
              refine ⟨2643522760414654412827405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3524697013886205883769873 2643522760414654412827405)
              ·
                refine ⟨991321035155495404810277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2643522760414654412827405 991321035155495404810277)
                ·
                  refine ⟨185872694091655388401927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 991321035155495404810277 185872694091655388401927)
                  ·
                    rfl

theorem cell21_814468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_814468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_814468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_814468 prefixEnd_814468 := by exact prefixLift 814468
  have htrace : WordTrace (prefixWord ++ tailWord_814468) baseStart_814468 baseEnd_814468 := by
    simpa [prefixWord, tailWord_814468, baseEnd_814468] using wordTrace_append hprefix tailTrace_814468
  have hstable : (prefixWord ++ tailWord_814468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814468).length < 2 ^ (prefixWord ++ tailWord_814468).sum := by decide
  have hdescent : baseEnd_814468 < baseStart_814468 := by decide
  rcases family_descends (prefixWord ++ tailWord_814468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814496 : List Nat := [2, 1, 1, 4, 1, 2, 1, 2, 7]
def baseStart_814496 : Nat := 118140960795 + 814496 * 2 ^ 59
def prefixEnd_814496 : Nat := 4983230072969 + 3 ^ 40 * 814496 * 2
def baseEnd_814496 : Nat := 185879084073133561935203

theorem tailTrace_814496 : CollatzResearch.WordTrace tailWord_814496 prefixEnd_814496 185879084073133561935203 := by
  unfold tailWord_814496
  simp only [CollatzResearch.WordTrace]
  refine ⟨14853554828613785843603671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19804739771485047791471561 14853554828613785843603671)
  ·
    refine ⟨22280332242920678765405507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14853554828613785843603671 22280332242920678765405507)
    ·
      refine ⟨33420498364381018148108261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22280332242920678765405507 33420498364381018148108261)
      ·
        refine ⟨6266343443321440902770299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33420498364381018148108261 6266343443321440902770299)
        ·
          refine ⟨9399515164982161354155449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6266343443321440902770299 9399515164982161354155449)
          ·
            refine ⟨7049636373736621015616587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9399515164982161354155449 7049636373736621015616587)
            ·
              refine ⟨10574454560604931523424881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7049636373736621015616587 10574454560604931523424881)
              ·
                refine ⟨7930840920453698642568661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10574454560604931523424881 7930840920453698642568661)
                ·
                  refine ⟨185879084073133561935203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7930840920453698642568661 185879084073133561935203)
                  ·
                    rfl

theorem cell21_814496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 7].length) (baseStart_814496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_814496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_814496 prefixEnd_814496 := by exact prefixLift 814496
  have htrace : WordTrace (prefixWord ++ tailWord_814496) baseStart_814496 baseEnd_814496 := by
    simpa [prefixWord, tailWord_814496, baseEnd_814496] using wordTrace_append hprefix tailTrace_814496
  have hstable : (prefixWord ++ tailWord_814496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814496).length < 2 ^ (prefixWord ++ tailWord_814496).sum := by decide
  have hdescent : baseEnd_814496 < baseStart_814496 := by decide
  rcases family_descends (prefixWord ++ tailWord_814496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814513 : List Nat := [1, 2, 2, 4, 1, 1, 4, 1, 5]
def baseStart_814513 : Nat := 118140960795 + 814513 * 2 ^ 59
def prefixEnd_814513 : Nat := 4983230072969 + 3 ^ 40 * 814513 * 2
def baseEnd_814513 : Nat := 185882963704745310151835

theorem tailTrace_814513 : CollatzResearch.WordTrace tailWord_814513 prefixEnd_814513 185882963704745310151835 := by
  unfold tailWord_814513
  simp only [CollatzResearch.WordTrace]
  refine ⟨29707729698165983590576193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19805153132110655727050795 29707729698165983590576193)
  ·
    refine ⟨22280797273624487692932145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29707729698165983590576193 22280797273624487692932145)
    ·
      refine ⟨16710597955218365769699109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22280797273624487692932145 16710597955218365769699109)
      ·
        refine ⟨3133237116603443581818583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16710597955218365769699109 3133237116603443581818583)
        ·
          refine ⟨4699855674905165372727875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3133237116603443581818583 4699855674905165372727875)
          ·
            refine ⟨7049783512357748059091813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4699855674905165372727875 7049783512357748059091813)
            ·
              refine ⟨1321834408567077761079715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7049783512357748059091813 1321834408567077761079715)
              ·
                refine ⟨1982751612850616641619573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1321834408567077761079715 1982751612850616641619573)
                ·
                  refine ⟨185882963704745310151835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1982751612850616641619573 185882963704745310151835)
                  ·
                    rfl

theorem cell21_814513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 5].length) (baseStart_814513 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_814513 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_814513 prefixEnd_814513 := by exact prefixLift 814513
  have htrace : WordTrace (prefixWord ++ tailWord_814513) baseStart_814513 baseEnd_814513 := by
    simpa [prefixWord, tailWord_814513, baseEnd_814513] using wordTrace_append hprefix tailTrace_814513
  have hstable : (prefixWord ++ tailWord_814513).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814513).length < 2 ^ (prefixWord ++ tailWord_814513).sum := by decide
  have hdescent : baseEnd_814513 < baseStart_814513 := by decide
  rcases family_descends (prefixWord ++ tailWord_814513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814527 : List Nat := [1, 1, 2, 2, 2, 1, 1, 7, 4]
def baseStart_814527 : Nat := 118140960795 + 814527 * 2 ^ 59
def prefixEnd_814527 : Nat := 4983230072969 + 3 ^ 40 * 814527 * 2
def baseEnd_814527 : Nat := 185886158695484396918473

theorem tailTrace_814527 : CollatzResearch.WordTrace tailWord_814527 prefixEnd_814527 185886158695484396918473 := by
  unfold tailWord_814527
  simp only [CollatzResearch.WordTrace]
  refine ⟨29708240320115263981585835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19805493546743509321057223 29708240320115263981585835)
  ·
    refine ⟨44562360480172895972378753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29708240320115263981585835 44562360480172895972378753)
    ·
      refine ⟨33421770360129671979284065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44562360480172895972378753 33421770360129671979284065)
      ·
        refine ⟨25066327770097253984463049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33421770360129671979284065 25066327770097253984463049)
        ·
          refine ⟨18799745827572940488347287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25066327770097253984463049 18799745827572940488347287)
          ·
            refine ⟨28199618741359410732520931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18799745827572940488347287 28199618741359410732520931)
            ·
              refine ⟨42299428112039116098781397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28199618741359410732520931 42299428112039116098781397)
              ·
                refine ⟨991392846375916783565189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 42299428112039116098781397 991392846375916783565189)
                ·
                  refine ⟨185886158695484396918473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 991392846375916783565189 185886158695484396918473)
                  ·
                    rfl

theorem cell21_814527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7, 4].length) (baseStart_814527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_814527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_814527 prefixEnd_814527 := by exact prefixLift 814527
  have htrace : WordTrace (prefixWord ++ tailWord_814527) baseStart_814527 baseEnd_814527 := by
    simpa [prefixWord, tailWord_814527, baseEnd_814527] using wordTrace_append hprefix tailTrace_814527
  have hstable : (prefixWord ++ tailWord_814527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814527).length < 2 ^ (prefixWord ++ tailWord_814527).sum := by decide
  have hdescent : baseEnd_814527 < baseStart_814527 := by decide
  rcases family_descends (prefixWord ++ tailWord_814527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814572 : List Nat := [2, 2, 1, 1, 2, 1, 2, 5, 5]
def baseStart_814572 : Nat := 118140960795 + 814572 * 2 ^ 59
def prefixEnd_814572 : Nat := 4983230072969 + 3 ^ 40 * 814572 * 2
def baseEnd_814572 : Nat := 185896428308574318668381

theorem tailTrace_814572 : CollatzResearch.WordTrace tailWord_814572 prefixEnd_814572 185896428308574318668381 := by
  unfold tailWord_814572
  simp only [CollatzResearch.WordTrace]
  refine ⟨14854940802476118333486985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19806587736634824444649313 14854940802476118333486985)
  ·
    refine ⟨11141205601857088750115239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14854940802476118333486985 11141205601857088750115239)
    ·
      refine ⟨16711808402785633125172859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11141205601857088750115239 16711808402785633125172859)
      ·
        refine ⟨25067712604178449687759289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16711808402785633125172859 25067712604178449687759289)
        ·
          refine ⟨18800784453133837265819467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25067712604178449687759289 18800784453133837265819467)
          ·
            refine ⟨28201176679700755898729201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18800784453133837265819467 28201176679700755898729201)
            ·
              refine ⟨21150882509775566924046901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28201176679700755898729201 21150882509775566924046901)
              ·
                refine ⟨1982895235291459399129397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21150882509775566924046901 1982895235291459399129397)
                ·
                  refine ⟨185896428308574318668381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1982895235291459399129397 185896428308574318668381)
                  ·
                    rfl

theorem cell21_814572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_814572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_814572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_814572 prefixEnd_814572 := by exact prefixLift 814572
  have htrace : WordTrace (prefixWord ++ tailWord_814572) baseStart_814572 baseEnd_814572 := by
    simpa [prefixWord, tailWord_814572, baseEnd_814572] using wordTrace_append hprefix tailTrace_814572
  have hstable : (prefixWord ++ tailWord_814572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814572).length < 2 ^ (prefixWord ++ tailWord_814572).sum := by decide
  have hdescent : baseEnd_814572 < baseStart_814572 := by decide
  rcases family_descends (prefixWord ++ tailWord_814572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814578 : List Nat := [3, 2, 1, 4, 1, 3, 2, 1, 4]
def baseStart_814578 : Nat := 118140960795 + 814578 * 2 ^ 59
def prefixEnd_814578 : Nat := 4983230072969 + 3 ^ 40 * 814578 * 2
def baseEnd_814578 : Nat := 185897797590319641568369

theorem tailTrace_814578 : CollatzResearch.WordTrace tailWord_814578 prefixEnd_814578 185897797590319641568369 := by
  unfold tailWord_814578
  simp only [CollatzResearch.WordTrace]
  refine ⟨7427525110732624922923097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19806733628620333127794925 7427525110732624922923097)
  ·
    refine ⟨5570643833049468692192323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7427525110732624922923097 5570643833049468692192323)
    ·
      refine ⟨8355965749574203038288485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5570643833049468692192323 8355965749574203038288485)
      ·
        refine ⟨1566743578045163069679091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8355965749574203038288485 1566743578045163069679091)
        ·
          refine ⟨2350115367067744604518637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1566743578045163069679091 2350115367067744604518637)
          ·
            refine ⟨881293262650404226694489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2350115367067744604518637 881293262650404226694489)
            ·
              refine ⟨660969946987803170020867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 881293262650404226694489 660969946987803170020867)
              ·
                refine ⟨991454920481704755031301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 660969946987803170020867 991454920481704755031301)
                ·
                  refine ⟨185897797590319641568369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 991454920481704755031301 185897797590319641568369)
                  ·
                    rfl

theorem cell21_814578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_814578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_814578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_814578 prefixEnd_814578 := by exact prefixLift 814578
  have htrace : WordTrace (prefixWord ++ tailWord_814578) baseStart_814578 baseEnd_814578 := by
    simpa [prefixWord, tailWord_814578, baseEnd_814578] using wordTrace_append hprefix tailTrace_814578
  have hstable : (prefixWord ++ tailWord_814578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814578).length < 2 ^ (prefixWord ++ tailWord_814578).sum := by decide
  have hdescent : baseEnd_814578 < baseStart_814578 := by decide
  rcases family_descends (prefixWord ++ tailWord_814578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814620 : List Nat := [2, 2, 3, 1, 2, 1, 4, 2, 4]
def baseStart_814620 : Nat := 118140960795 + 814620 * 2 ^ 59
def prefixEnd_814620 : Nat := 4983230072969 + 3 ^ 40 * 814620 * 2
def baseEnd_814620 : Nat := 185907382562536901868283

theorem tailTrace_814620 : CollatzResearch.WordTrace tailWord_814620 prefixEnd_814620 185907382562536901868283 := by
  unfold tailWord_814620
  simp only [CollatzResearch.WordTrace]
  refine ⟨14855816154389170432360657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19807754872518893909814209 14855816154389170432360657)
  ·
    refine ⟨11141862115791877824270493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14855816154389170432360657 11141862115791877824270493)
    ·
      refine ⟨4178198293421954184101435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11141862115791877824270493 4178198293421954184101435)
      ·
        refine ⟨6267297440132931276152153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4178198293421954184101435 6267297440132931276152153)
        ·
          refine ⟨4700473080099698457114115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6267297440132931276152153 4700473080099698457114115)
          ·
            refine ⟨7050709620149547685671173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4700473080099698457114115 7050709620149547685671173)
            ·
              refine ⟨1322008053778040191063345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7050709620149547685671173 1322008053778040191063345)
              ·
                refine ⟨991506040333530143297509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1322008053778040191063345 991506040333530143297509)
                ·
                  refine ⟨185907382562536901868283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 991506040333530143297509 185907382562536901868283)
                  ·
                    rfl

theorem cell21_814620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2, 4].length) (baseStart_814620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_814620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_814620 prefixEnd_814620 := by exact prefixLift 814620
  have htrace : WordTrace (prefixWord ++ tailWord_814620) baseStart_814620 baseEnd_814620 := by
    simpa [prefixWord, tailWord_814620, baseEnd_814620] using wordTrace_append hprefix tailTrace_814620
  have hstable : (prefixWord ++ tailWord_814620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814620).length < 2 ^ (prefixWord ++ tailWord_814620).sum := by decide
  have hdescent : baseEnd_814620 < baseStart_814620 := by decide
  rcases family_descends (prefixWord ++ tailWord_814620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814648 : List Nat := [2, 1, 2, 1, 4, 2, 1, 1, 7]
def baseStart_814648 : Nat := 118140960795 + 814648 * 2 ^ 59
def prefixEnd_814648 : Nat := 4983230072969 + 3 ^ 40 * 814648 * 2
def baseEnd_814648 : Nat := 185913772544015075401559

theorem tailTrace_814648 : CollatzResearch.WordTrace tailWord_814648 prefixEnd_814648 185913772544015075401559 := by
  unfold tailWord_814648
  simp only [CollatzResearch.WordTrace]
  refine ⟨14856326776338450823370299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19808435701784601097827065 14856326776338450823370299)
  ·
    refine ⟨22284490164507676235055449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14856326776338450823370299 22284490164507676235055449)
    ·
      refine ⟨16713367623380757176291587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22284490164507676235055449 16713367623380757176291587)
      ·
        refine ⟨25070051435071135764437381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16713367623380757176291587 25070051435071135764437381)
        ·
          refine ⟨4700634644075837955832009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25070051435071135764437381 4700634644075837955832009)
          ·
            refine ⟨3525475983056878466874007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4700634644075837955832009 3525475983056878466874007)
            ·
              refine ⟨5288213974585317700311011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3525475983056878466874007 5288213974585317700311011)
              ·
                refine ⟨7932320961877976550466517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5288213974585317700311011 7932320961877976550466517)
                ·
                  refine ⟨185913772544015075401559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7932320961877976550466517 185913772544015075401559)
                  ·
                    rfl

theorem cell21_814648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 7].length) (baseStart_814648 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_814648 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_814648 prefixEnd_814648 := by exact prefixLift 814648
  have htrace : WordTrace (prefixWord ++ tailWord_814648) baseStart_814648 baseEnd_814648 := by
    simpa [prefixWord, tailWord_814648, baseEnd_814648] using wordTrace_append hprefix tailTrace_814648
  have hstable : (prefixWord ++ tailWord_814648).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814648).length < 2 ^ (prefixWord ++ tailWord_814648).sum := by decide
  have hdescent : baseEnd_814648 < baseStart_814648 := by decide
  rcases family_descends (prefixWord ++ tailWord_814648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814679 : List Nat := [1, 1, 3, 2, 2, 4, 1, 1, 6]
def baseStart_814679 : Nat := 118140960795 + 814679 * 2 ^ 59
def prefixEnd_814679 : Nat := 4983230072969 + 3 ^ 40 * 814679 * 2
def baseEnd_814679 : Nat := 185920847166365910384829

theorem tailTrace_814679 : CollatzResearch.WordTrace tailWord_814679 prefixEnd_814679 185920847166365910384829 := by
  unfold tailWord_814679
  simp only [CollatzResearch.WordTrace]
  refine ⟨29713784215564593941119091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19809189477043062627412727 29713784215564593941119091)
  ·
    refine ⟨44570676323346890911678637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29713784215564593941119091 44570676323346890911678637)
    ·
      refine ⟨16714003621255084091879489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44570676323346890911678637 16714003621255084091879489)
      ·
        refine ⟨12535502715941313068909617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16714003621255084091879489 12535502715941313068909617)
        ·
          refine ⟨9401627036955984801682213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12535502715941313068909617 9401627036955984801682213)
          ·
            refine ⟨1762805069429247150315415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9401627036955984801682213 1762805069429247150315415)
            ·
              refine ⟨2644207604143870725473123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1762805069429247150315415 2644207604143870725473123)
              ·
                refine ⟨3966311406215806088209685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2644207604143870725473123 3966311406215806088209685)
                ·
                  refine ⟨185920847166365910384829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3966311406215806088209685 185920847166365910384829)
                  ·
                    rfl

theorem cell21_814679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 6].length) (baseStart_814679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_814679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_814679 prefixEnd_814679 := by exact prefixLift 814679
  have htrace : WordTrace (prefixWord ++ tailWord_814679) baseStart_814679 baseEnd_814679 := by
    simpa [prefixWord, tailWord_814679, baseEnd_814679] using wordTrace_append hprefix tailTrace_814679
  have hstable : (prefixWord ++ tailWord_814679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814679).length < 2 ^ (prefixWord ++ tailWord_814679).sum := by decide
  have hdescent : baseEnd_814679 < baseStart_814679 := by decide
  rcases family_descends (prefixWord ++ tailWord_814679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814741 : List Nat := [1, 3, 2, 1, 1, 1, 1, 8, 3]
def baseStart_814741 : Nat := 118140960795 + 814741 * 2 ^ 59
def prefixEnd_814741 : Nat := 4983230072969 + 3 ^ 40 * 814741 * 2
def baseEnd_814741 : Nat := 185934996411067580351369

theorem tailTrace_814741 : CollatzResearch.WordTrace tailWord_814741 prefixEnd_814741 185934996411067580351369 := by
  unfold tailWord_814741
  simp only [CollatzResearch.WordTrace]
  refine ⟨29716045541339978529876077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19810697027559985686584051 29716045541339978529876077)
  ·
    refine ⟨11143517078002491948703529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29716045541339978529876077 11143517078002491948703529)
    ·
      refine ⟨8357637808501868961527647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11143517078002491948703529 8357637808501868961527647)
      ·
        refine ⟨12536456712752803442291471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8357637808501868961527647 12536456712752803442291471)
        ·
          refine ⟨18804685069129205163437207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12536456712752803442291471 18804685069129205163437207)
          ·
            refine ⟨28207027603693807745155811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18804685069129205163437207 28207027603693807745155811)
            ·
              refine ⟨42310541405540711617733717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28207027603693807745155811 42310541405540711617733717)
              ·
                refine ⟨495826657096180214270317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 42310541405540711617733717 495826657096180214270317)
                ·
                  refine ⟨185934996411067580351369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 495826657096180214270317 185934996411067580351369)
                  ·
                    rfl

theorem cell21_814741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 8, 3].length) (baseStart_814741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_814741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_814741 prefixEnd_814741 := by exact prefixLift 814741
  have htrace : WordTrace (prefixWord ++ tailWord_814741) baseStart_814741 baseEnd_814741 := by
    simpa [prefixWord, tailWord_814741, baseEnd_814741] using wordTrace_append hprefix tailTrace_814741
  have hstable : (prefixWord ++ tailWord_814741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814741).length < 2 ^ (prefixWord ++ tailWord_814741).sum := by decide
  have hdescent : baseEnd_814741 < baseStart_814741 := by decide
  rcases family_descends (prefixWord ++ tailWord_814741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814755 : List Nat := [1, 1, 1, 4, 1, 1, 5, 3, 4]
def baseStart_814755 : Nat := 118140960795 + 814755 * 2 ^ 59
def prefixEnd_814755 : Nat := 4983230072969 + 3 ^ 40 * 814755 * 2
def baseEnd_814755 : Nat := 185938191401806667118007

theorem tailTrace_814755 : CollatzResearch.WordTrace tailWord_814755 prefixEnd_814755 185938191401806667118007 := by
  unfold tailWord_814755
  simp only [CollatzResearch.WordTrace]
  refine ⟨29716556163289258920885719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19811037442192839280590479 29716556163289258920885719)
  ·
    refine ⟨44574834244933888381328579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29716556163289258920885719 44574834244933888381328579)
    ·
      refine ⟨66862251367400832571992869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44574834244933888381328579 66862251367400832571992869)
      ·
        refine ⟨12536672131387656107248663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66862251367400832571992869 12536672131387656107248663)
        ·
          refine ⟨18805008197081484160872995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12536672131387656107248663 18805008197081484160872995)
          ·
            refine ⟨28207512295622226241309493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18805008197081484160872995 28207512295622226241309493)
            ·
              refine ⟨2644454277714583710122765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28207512295622226241309493 2644454277714583710122765)
              ·
                refine ⟨991670354142968891296037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2644454277714583710122765 991670354142968891296037)
                ·
                  refine ⟨185938191401806667118007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 991670354142968891296037 185938191401806667118007)
                  ·
                    rfl

theorem cell21_814755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3, 4].length) (baseStart_814755 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_814755 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_814755 prefixEnd_814755 := by exact prefixLift 814755
  have htrace : WordTrace (prefixWord ++ tailWord_814755) baseStart_814755 baseEnd_814755 := by
    simpa [prefixWord, tailWord_814755, baseEnd_814755] using wordTrace_append hprefix tailTrace_814755
  have hstable : (prefixWord ++ tailWord_814755).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814755).length < 2 ^ (prefixWord ++ tailWord_814755).sum := by decide
  have hdescent : baseEnd_814755 < baseStart_814755 := by decide
  rcases family_descends (prefixWord ++ tailWord_814755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814817 : List Nat := [1, 2, 3, 1, 5, 1, 1, 2, 5]
def baseStart_814817 : Nat := 118140960795 + 814817 * 2 ^ 59
def prefixEnd_814817 : Nat := 4983230072969 + 3 ^ 40 * 814817 * 2
def baseEnd_814817 : Nat := 185952340646508337084547

theorem tailTrace_814817 : CollatzResearch.WordTrace tailWord_814817 prefixEnd_814817 185952340646508337084547 := by
  unfold tailWord_814817
  simp only [CollatzResearch.WordTrace]
  refine ⟨29718817489064643509642705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19812544992709762339761803 29718817489064643509642705)
  ·
    refine ⟨22289113116798482632232029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29718817489064643509642705 22289113116798482632232029)
    ·
      refine ⟨8358417418799430987087011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22289113116798482632232029 8358417418799430987087011)
      ·
        refine ⟨12537626128199146480630517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8358417418799430987087011 12537626128199146480630517)
        ·
          refine ⟨1175402449518669982559111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12537626128199146480630517 1175402449518669982559111)
          ·
            refine ⟨1763103674278004973838667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1175402449518669982559111 1763103674278004973838667)
            ·
              refine ⟨2644655511417007460758001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1763103674278004973838667 2644655511417007460758001)
              ·
                refine ⟨1983491633562755595568501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2644655511417007460758001 1983491633562755595568501)
                ·
                  refine ⟨185952340646508337084547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1983491633562755595568501 185952340646508337084547)
                  ·
                    rfl

theorem cell21_814817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 5].length) (baseStart_814817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_814817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_814817 prefixEnd_814817 := by exact prefixLift 814817
  have htrace : WordTrace (prefixWord ++ tailWord_814817) baseStart_814817 baseEnd_814817 := by
    simpa [prefixWord, tailWord_814817, baseEnd_814817] using wordTrace_append hprefix tailTrace_814817
  have hstable : (prefixWord ++ tailWord_814817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814817).length < 2 ^ (prefixWord ++ tailWord_814817).sum := by decide
  have hdescent : baseEnd_814817 < baseStart_814817 := by decide
  rcases family_descends (prefixWord ++ tailWord_814817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814834 : List Nat := [3, 2, 1, 3, 1, 1, 4, 3, 3]
def baseStart_814834 : Nat := 118140960795 + 814834 * 2 ^ 59
def prefixEnd_814834 : Nat := 4983230072969 + 3 ^ 40 * 814834 * 2
def baseEnd_814834 : Nat := 185956220278120085301179

theorem tailTrace_814834 : CollatzResearch.WordTrace tailWord_814834 prefixEnd_814834 185956220278120085301179 := by
  unfold tailWord_814834
  simp only [CollatzResearch.WordTrace]
  refine ⟨7429859382500763853252889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19812958353335370275341037 7429859382500763853252889)
  ·
    refine ⟨5572394536875572889939667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7429859382500763853252889 5572394536875572889939667)
    ·
      refine ⟨8358591805313359334909501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5572394536875572889939667 8358591805313359334909501)
      ·
        refine ⟨3134471926992509750591063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8358591805313359334909501 3134471926992509750591063)
        ·
          refine ⟨4701707890488764625886595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3134471926992509750591063 4701707890488764625886595)
          ·
            refine ⟨7052561835733146938829893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4701707890488764625886595 7052561835733146938829893)
            ·
              refine ⟨1322355344199965051030605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7052561835733146938829893 1322355344199965051030605)
              ·
                refine ⟨495883254074986894136477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1322355344199965051030605 495883254074986894136477)
                ·
                  refine ⟨185956220278120085301179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 495883254074986894136477 185956220278120085301179)
                  ·
                    rfl

theorem cell21_814834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 3, 3].length) (baseStart_814834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_814834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_814834 prefixEnd_814834 := by exact prefixLift 814834
  have htrace : WordTrace (prefixWord ++ tailWord_814834) baseStart_814834 baseEnd_814834 := by
    simpa [prefixWord, tailWord_814834, baseEnd_814834] using wordTrace_append hprefix tailTrace_814834
  have hstable : (prefixWord ++ tailWord_814834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814834).length < 2 ^ (prefixWord ++ tailWord_814834).sum := by decide
  have hdescent : baseEnd_814834 < baseStart_814834 := by decide
  rcases family_descends (prefixWord ++ tailWord_814834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814876 : List Nat := [2, 2, 3, 1, 1, 2, 1, 4, 5]
def baseStart_814876 : Nat := 118140960795 + 814876 * 2 ^ 59
def prefixEnd_814876 : Nat := 4983230072969 + 3 ^ 40 * 814876 * 2
def baseEnd_814876 : Nat := 185965805250337345601093

theorem tailTrace_814876 : CollatzResearch.WordTrace tailWord_814876 prefixEnd_814876 185965805250337345601093 := by
  unfold tailWord_814876
  simp only [CollatzResearch.WordTrace]
  refine ⟨14860484697925448293020241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19813979597233931057360321 14860484697925448293020241)
  ·
    refine ⟨11145363523444086219765181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14860484697925448293020241 11145363523444086219765181)
    ·
      refine ⟨4179511321291532332411943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11145363523444086219765181 4179511321291532332411943)
      ·
        refine ⟨6269266981937298498617915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4179511321291532332411943 6269266981937298498617915)
        ·
          refine ⟨9403900472905947747926873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6269266981937298498617915 9403900472905947747926873)
          ·
            refine ⟨7052925354679460810945155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9403900472905947747926873 7052925354679460810945155)
            ·
              refine ⟨10579388032019191216417733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7052925354679460810945155 10579388032019191216417733)
              ·
                refine ⟨1983635256003598353078325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10579388032019191216417733 1983635256003598353078325)
                ·
                  refine ⟨185965805250337345601093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1983635256003598353078325 185965805250337345601093)
                  ·
                    rfl

theorem cell21_814876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_814876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_814876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_814876 prefixEnd_814876 := by exact prefixLift 814876
  have htrace : WordTrace (prefixWord ++ tailWord_814876) baseStart_814876 baseEnd_814876 := by
    simpa [prefixWord, tailWord_814876, baseEnd_814876] using wordTrace_append hprefix tailTrace_814876
  have hstable : (prefixWord ++ tailWord_814876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814876).length < 2 ^ (prefixWord ++ tailWord_814876).sum := by decide
  have hdescent : baseEnd_814876 < baseStart_814876 := by decide
  rcases family_descends (prefixWord ++ tailWord_814876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814910 : List Nat := [4, 2, 1, 2, 2, 3, 1, 1, 5]
def baseStart_814910 : Nat := 118140960795 + 814910 * 2 ^ 59
def prefixEnd_814910 : Nat := 4983230072969 + 3 ^ 40 * 814910 * 2
def baseEnd_814910 : Nat := 185973564513560842034357

theorem tailTrace_814910 : CollatzResearch.WordTrace tailWord_814910 prefixEnd_814910 185973564513560842034357 := by
  unfold tailWord_814910
  simp only [CollatzResearch.WordTrace]
  refine ⟨3715276184715965049097273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19814806318485146928518789 3715276184715965049097273)
  ·
    refine ⟨2786457138536973786822955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3715276184715965049097273 2786457138536973786822955)
    ·
      refine ⟨4179685707805460680234433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2786457138536973786822955 4179685707805460680234433)
      ·
        refine ⟨3134764280854095510175825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4179685707805460680234433 3134764280854095510175825)
        ·
          refine ⟨2351073210640571632631869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3134764280854095510175825 2351073210640571632631869)
          ·
            refine ⟨881652453990214362236951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2351073210640571632631869 881652453990214362236951)
            ·
              refine ⟨1322478680985321543355427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 881652453990214362236951 1322478680985321543355427)
              ·
                refine ⟨1983718021477982315033141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1322478680985321543355427 1983718021477982315033141)
                ·
                  refine ⟨185973564513560842034357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1983718021477982315033141 185973564513560842034357)
                  ·
                    rfl

theorem cell21_814910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_814910 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_814910 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_814910 prefixEnd_814910 := by exact prefixLift 814910
  have htrace : WordTrace (prefixWord ++ tailWord_814910) baseStart_814910 baseEnd_814910 := by
    simpa [prefixWord, tailWord_814910, baseEnd_814910] using wordTrace_append hprefix tailTrace_814910
  have hstable : (prefixWord ++ tailWord_814910).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814910).length < 2 ^ (prefixWord ++ tailWord_814910).sum := by decide
  have hdescent : baseEnd_814910 < baseStart_814910 := by decide
  rcases family_descends (prefixWord ++ tailWord_814910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814921 : List Nat := [1, 2, 1, 1, 2, 4, 4, 6]
def baseStart_814921 : Nat := 118140960795 + 814921 * 2 ^ 59
def prefixEnd_814921 : Nat := 4983230072969 + 3 ^ 40 * 814921 * 2
def baseEnd_814921 : Nat := 61992024954475755783667

theorem tailTrace_814921 : CollatzResearch.WordTrace tailWord_814921 prefixEnd_814921 61992024954475755783667 := by
  unfold tailWord_814921
  simp only [CollatzResearch.WordTrace]
  refine ⟨29722610680687869271428617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19815073787125246180952411 29722610680687869271428617)
  ·
    refine ⟨22291958010515901953571463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29722610680687869271428617 22291958010515901953571463)
    ·
      refine ⟨33437937015773852930357195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22291958010515901953571463 33437937015773852930357195)
      ·
        refine ⟨50156905523660779395535793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33437937015773852930357195 50156905523660779395535793)
        ·
          refine ⟨37617679142745584546651845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50156905523660779395535793 37617679142745584546651845)
          ·
            refine ⟨7053314839264797102497221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37617679142745584546651845 7053314839264797102497221)
            ·
              refine ⟨1322496532362149456718229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7053314839264797102497221 1322496532362149456718229)
              ·
                refine ⟨61992024954475755783667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1322496532362149456718229 61992024954475755783667)
                ·
                  rfl

theorem cell21_814921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 6].length) (baseStart_814921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_814921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_814921 prefixEnd_814921 := by exact prefixLift 814921
  have htrace : WordTrace (prefixWord ++ tailWord_814921) baseStart_814921 baseEnd_814921 := by
    simpa [prefixWord, tailWord_814921, baseEnd_814921] using wordTrace_append hprefix tailTrace_814921
  have hstable : (prefixWord ++ tailWord_814921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814921).length < 2 ^ (prefixWord ++ tailWord_814921).sum := by decide
  have hdescent : baseEnd_814921 < baseStart_814921 := by decide
  rcases family_descends (prefixWord ++ tailWord_814921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814924 : List Nat := [2, 2, 1, 3, 4, 1, 1, 3, 4]
def baseStart_814924 : Nat := 118140960795 + 814924 * 2 ^ 59
def prefixEnd_814924 : Nat := 4983230072969 + 3 ^ 40 * 814924 * 2
def baseEnd_814924 : Nat := 185976759504299928800995

theorem tailTrace_814924 : CollatzResearch.WordTrace tailWord_814924 prefixEnd_814924 185976759504299928800995 := by
  unfold tailWord_814924
  simp only [CollatzResearch.WordTrace]
  refine ⟨14861360049838500391893913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19815146733118000522525217 14861360049838500391893913)
  ·
    refine ⟨11146020037378875293920435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14861360049838500391893913 11146020037378875293920435)
    ·
      refine ⟨16719030056068312940880653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11146020037378875293920435 16719030056068312940880653)
      ·
        refine ⟨6269636271025617352830245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16719030056068312940880653 6269636271025617352830245)
        ·
          refine ⟨1175556800817303253655671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6269636271025617352830245 1175556800817303253655671)
          ·
            refine ⟨1763335201225954880483507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1175556800817303253655671 1763335201225954880483507)
            ·
              refine ⟨2645002801838932320725261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1763335201225954880483507 2645002801838932320725261)
              ·
                refine ⟨991876050689599620271973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2645002801838932320725261 991876050689599620271973)
                ·
                  refine ⟨185976759504299928800995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 991876050689599620271973 185976759504299928800995)
                  ·
                    rfl

theorem cell21_814924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3, 4].length) (baseStart_814924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_814924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_814924 prefixEnd_814924 := by exact prefixLift 814924
  have htrace : WordTrace (prefixWord ++ tailWord_814924) baseStart_814924 baseEnd_814924 := by
    simpa [prefixWord, tailWord_814924, baseEnd_814924] using wordTrace_append hprefix tailTrace_814924
  have hstable : (prefixWord ++ tailWord_814924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814924).length < 2 ^ (prefixWord ++ tailWord_814924).sum := by decide
  have hdescent : baseEnd_814924 < baseStart_814924 := by decide
  rcases family_descends (prefixWord ++ tailWord_814924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814969 : List Nat := [1, 2, 1, 3, 2, 2, 3, 4, 3]
def baseStart_814969 : Nat := 118140960795 + 814969 * 2 ^ 59
def prefixEnd_814969 : Nat := 4983230072969 + 3 ^ 40 * 814969 * 2
def baseEnd_814969 : Nat := 185987029117389850550903

theorem tailTrace_814969 : CollatzResearch.WordTrace tailWord_814969 prefixEnd_814969 185987029117389850550903 := by
  unfold tailWord_814969
  simp only [CollatzResearch.WordTrace]
  refine ⟨29724361384513973469175961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19816240923009315646117307 29724361384513973469175961)
  ·
    refine ⟨22293271038385480101881971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29724361384513973469175961 22293271038385480101881971)
    ·
      refine ⟨33439906557578220152822957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22293271038385480101881971 33439906557578220152822957)
      ·
        refine ⟨12539964959091832557308609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33439906557578220152822957 12539964959091832557308609)
        ·
          refine ⟨9404973719318874417981457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12539964959091832557308609 9404973719318874417981457)
          ·
            refine ⟨7053730289489155813486093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9404973719318874417981457 7053730289489155813486093)
            ·
              refine ⟨2645148858558433430057285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7053730289489155813486093 2645148858558433430057285)
              ·
                refine ⟨495965410979706268135741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2645148858558433430057285 495965410979706268135741)
                ·
                  refine ⟨185987029117389850550903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 495965410979706268135741 185987029117389850550903)
                  ·
                    rfl

theorem cell21_814969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 4, 3].length) (baseStart_814969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_814969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_814969 prefixEnd_814969 := by exact prefixLift 814969
  have htrace : WordTrace (prefixWord ++ tailWord_814969) baseStart_814969 baseEnd_814969 := by
    simpa [prefixWord, tailWord_814969, baseEnd_814969] using wordTrace_append hprefix tailTrace_814969
  have hstable : (prefixWord ++ tailWord_814969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814969).length < 2 ^ (prefixWord ++ tailWord_814969).sum := by decide
  have hdescent : baseEnd_814969 < baseStart_814969 := by decide
  rcases family_descends (prefixWord ++ tailWord_814969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815011 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 9]
def baseStart_815011 : Nat := 118140960795 + 815011 * 2 ^ 59
def prefixEnd_815011 : Nat := 4983230072969 + 3 ^ 40 * 815011 * 2
def baseEnd_815011 : Nat := 185996614089607110850817

theorem tailTrace_815011 : CollatzResearch.WordTrace tailWord_815011 prefixEnd_815011 185996614089607110850817 := by
  unfold tailWord_815011
  simp only [CollatzResearch.WordTrace]
  refine ⟨29725893250361814642204887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19817262166907876428136591 29725893250361814642204887)
  ·
    refine ⟨44588839875542721963307331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29725893250361814642204887 44588839875542721963307331)
    ·
      refine ⟨66883259813314082944960997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44588839875542721963307331 66883259813314082944960997)
      ·
        refine ⟨12540611214996390552180187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66883259813314082944960997 12540611214996390552180187)
        ·
          refine ⟨18810916822494585828270281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12540611214996390552180187 18810916822494585828270281)
          ·
            refine ⟨14108187616870939371202711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18810916822494585828270281 14108187616870939371202711)
            ·
              refine ⟨21162281425306409056804067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14108187616870939371202711 21162281425306409056804067)
              ·
                refine ⟨31743422137959613585206101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21162281425306409056804067 31743422137959613585206101)
                ·
                  refine ⟨185996614089607110850817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31743422137959613585206101 185996614089607110850817)
                  ·
                    rfl

theorem cell21_815011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 9].length) (baseStart_815011 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_815011 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_815011 prefixEnd_815011 := by exact prefixLift 815011
  have htrace : WordTrace (prefixWord ++ tailWord_815011) baseStart_815011 baseEnd_815011 := by
    simpa [prefixWord, tailWord_815011, baseEnd_815011] using wordTrace_append hprefix tailTrace_815011
  have hstable : (prefixWord ++ tailWord_815011).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815011).length < 2 ^ (prefixWord ++ tailWord_815011).sum := by decide
  have hdescent : baseEnd_815011 < baseStart_815011 := by decide
  rcases family_descends (prefixWord ++ tailWord_815011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815079 : List Nat := [1, 1, 5, 2, 3, 1, 3, 2, 3]
def baseStart_815079 : Nat := 118140960795 + 815079 * 2 ^ 59
def prefixEnd_815079 : Nat := 4983230072969 + 3 ^ 40 * 815079 * 2
def baseEnd_815079 : Nat := 186012132616054103717345

theorem tailTrace_815079 : CollatzResearch.WordTrace tailWord_815079 prefixEnd_815079 186012132616054103717345 := by
  unfold tailWord_815079
  simp only [CollatzResearch.WordTrace]
  refine ⟨29728373414115462255680291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19818915609410308170453527 29728373414115462255680291)
  ·
    refine ⟨44592560121173193383520437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29728373414115462255680291 44592560121173193383520437)
    ·
      refine ⟨4180552511359986879705041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44592560121173193383520437 4180552511359986879705041)
      ·
        refine ⟨3135414383519990159778781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4180552511359986879705041 3135414383519990159778781)
        ·
          refine ⟨1175780393819996309917043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3135414383519990159778781 1175780393819996309917043)
          ·
            refine ⟨1763670590729994464875565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1175780393819996309917043 1763670590729994464875565)
            ·
              refine ⟨661376471523747924328337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1763670590729994464875565 661376471523747924328337)
              ·
                refine ⟨496032353642810943246253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 661376471523747924328337 496032353642810943246253)
                ·
                  refine ⟨186012132616054103717345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 496032353642810943246253 186012132616054103717345)
                  ·
                    rfl

theorem cell21_815079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 2, 3].length) (baseStart_815079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_815079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_815079 prefixEnd_815079 := by exact prefixLift 815079
  have htrace : WordTrace (prefixWord ++ tailWord_815079) baseStart_815079 baseEnd_815079 := by
    simpa [prefixWord, tailWord_815079, baseEnd_815079] using wordTrace_append hprefix tailTrace_815079
  have hstable : (prefixWord ++ tailWord_815079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815079).length < 2 ^ (prefixWord ++ tailWord_815079).sum := by decide
  have hdescent : baseEnd_815079 < baseStart_815079 := by decide
  rcases family_descends (prefixWord ++ tailWord_815079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815135 : List Nat := [1, 1, 2, 4, 1, 2, 4, 2, 4]
def baseStart_815135 : Nat := 118140960795 + 815135 * 2 ^ 59
def prefixEnd_815135 : Nat := 4983230072969 + 3 ^ 40 * 815135 * 2
def baseEnd_815135 : Nat := 186024912579010450783897

theorem tailTrace_815135 : CollatzResearch.WordTrace tailWord_815135 prefixEnd_815135 186024912579010450783897 := by
  unfold tailWord_815135
  simp only [CollatzResearch.WordTrace]
  refine ⟨29730415901912583819718859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19820277267941722546479239 29730415901912583819718859)
  ·
    refine ⟨44595623852868875729578289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29730415901912583819718859 44595623852868875729578289)
    ·
      refine ⟨33446717889651656797183717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44595623852868875729578289 33446717889651656797183717)
      ·
        refine ⟨6271259604309685649471947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33446717889651656797183717 6271259604309685649471947)
        ·
          refine ⟨9406889406464528474207921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6271259604309685649471947 9406889406464528474207921)
          ·
            refine ⟨7055167054848396355655941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9406889406464528474207921 7055167054848396355655941)
            ·
              refine ⟨1322843822784074316685489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7055167054848396355655941 1322843822784074316685489)
              ·
                refine ⟨992132867088055737514117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1322843822784074316685489 992132867088055737514117)
                ·
                  refine ⟨186024912579010450783897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 992132867088055737514117 186024912579010450783897)
                  ·
                    rfl

theorem cell21_815135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2, 4].length) (baseStart_815135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_815135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_815135 prefixEnd_815135 := by exact prefixLift 815135
  have htrace : WordTrace (prefixWord ++ tailWord_815135) baseStart_815135 baseEnd_815135 := by
    simpa [prefixWord, tailWord_815135, baseEnd_815135] using wordTrace_append hprefix tailTrace_815135
  have hstable : (prefixWord ++ tailWord_815135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815135).length < 2 ^ (prefixWord ++ tailWord_815135).sum := by decide
  have hdescent : baseEnd_815135 < baseStart_815135 := by decide
  rcases family_descends (prefixWord ++ tailWord_815135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815163 : List Nat := [1, 1, 1, 1, 1, 2, 1, 8, 5]
def baseStart_815163 : Nat := 118140960795 + 815163 * 2 ^ 59
def prefixEnd_815163 : Nat := 4983230072969 + 3 ^ 40 * 815163 * 2
def baseEnd_815163 : Nat := 186031302560488624317173

theorem tailTrace_815163 : CollatzResearch.WordTrace tailWord_815163 prefixEnd_815163 186031302560488624317173 := by
  unfold tailWord_815163
  simp only [CollatzResearch.WordTrace]
  refine ⟨29731437145811144601738143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19820958097207429734492095 29731437145811144601738143)
  ·
    refine ⟨44597155718716716902607215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29731437145811144601738143 44597155718716716902607215)
    ·
      refine ⟨66895733578075075353910823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44597155718716716902607215 66895733578075075353910823)
      ·
        refine ⟨100343600367112613030866235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66895733578075075353910823 100343600367112613030866235)
        ·
          refine ⟨150515400550668919546299353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100343600367112613030866235 150515400550668919546299353)
          ·
            refine ⟨112886550413001689659724515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150515400550668919546299353 112886550413001689659724515)
            ·
              refine ⟨169329825619502534489586773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112886550413001689659724515 169329825619502534489586773)
              ·
                refine ⟨1984333893978545326049845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 169329825619502534489586773 1984333893978545326049845)
                ·
                  refine ⟨186031302560488624317173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1984333893978545326049845 186031302560488624317173)
                  ·
                    rfl

theorem cell21_815163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 5].length) (baseStart_815163 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_815163 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_815163 prefixEnd_815163 := by exact prefixLift 815163
  have htrace : WordTrace (prefixWord ++ tailWord_815163) baseStart_815163 baseEnd_815163 := by
    simpa [prefixWord, tailWord_815163, baseEnd_815163] using wordTrace_append hprefix tailTrace_815163
  have hstable : (prefixWord ++ tailWord_815163).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815163).length < 2 ^ (prefixWord ++ tailWord_815163).sum := by decide
  have hdescent : baseEnd_815163 < baseStart_815163 := by decide
  rcases family_descends (prefixWord ++ tailWord_815163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815194 : List Nat := [3, 1, 1, 2, 1, 1, 5, 1, 6]
def baseStart_815194 : Nat := 118140960795 + 815194 * 2 ^ 59
def prefixEnd_815194 : Nat := 4983230072969 + 3 ^ 40 * 815194 * 2
def baseEnd_815194 : Nat := 186038377182839459300443

theorem tailTrace_815194 : CollatzResearch.WordTrace tailWord_815194 prefixEnd_815194 186038377182839459300443 := by
  unfold tailWord_815194
  simp only [CollatzResearch.WordTrace]
  refine ⟨7433141952174709224029159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19821711872465891264077757 7433141952174709224029159)
  ·
    refine ⟨11149712928262063836043739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7433141952174709224029159 11149712928262063836043739)
    ·
      refine ⟨16724569392393095754065609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11149712928262063836043739 16724569392393095754065609)
      ·
        refine ⟨12543427044294821815549207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16724569392393095754065609 12543427044294821815549207)
        ·
          refine ⟨18815140566442232723323811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12543427044294821815549207 18815140566442232723323811)
          ·
            refine ⟨28222710849663349084985717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18815140566442232723323811 28222710849663349084985717)
            ·
              refine ⟨2645879142155938976717411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28222710849663349084985717 2645879142155938976717411)
              ·
                refine ⟨3968818713233908465076117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2645879142155938976717411 3968818713233908465076117)
                ·
                  refine ⟨186038377182839459300443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3968818713233908465076117 186038377182839459300443)
                  ·
                    rfl

theorem cell21_815194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_815194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_815194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_815194 prefixEnd_815194 := by exact prefixLift 815194
  have htrace : WordTrace (prefixWord ++ tailWord_815194) baseStart_815194 baseEnd_815194 := by
    simpa [prefixWord, tailWord_815194, baseEnd_815194] using wordTrace_append hprefix tailTrace_815194
  have hstable : (prefixWord ++ tailWord_815194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815194).length < 2 ^ (prefixWord ++ tailWord_815194).sum := by decide
  have hdescent : baseEnd_815194 < baseStart_815194 := by decide
  rcases family_descends (prefixWord ++ tailWord_815194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815197 : List Nat := [1, 4, 4, 1, 1, 1, 1, 3, 5]
def baseStart_815197 : Nat := 118140960795 + 815197 * 2 ^ 59
def prefixEnd_815197 : Nat := 4983230072969 + 3 ^ 40 * 815197 * 2
def baseEnd_815197 : Nat := 186039061823712120750437

theorem tailTrace_815197 : CollatzResearch.WordTrace tailWord_815197 prefixEnd_815197 186039061823712120750437 := by
  unfold tailWord_815197
  simp only [CollatzResearch.WordTrace]
  refine ⟨29732677227687968408475845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19821784818458645605650563 29732677227687968408475845)
  ·
    refine ⟨5574876980191494076589221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29732677227687968408475845 5574876980191494076589221)
    ·
      refine ⟨1045289433785905139360479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5574876980191494076589221 1045289433785905139360479)
      ·
        refine ⟨1567934150678857709040719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1045289433785905139360479 1567934150678857709040719)
        ·
          refine ⟨2351901226018286563561079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1567934150678857709040719 2351901226018286563561079)
          ·
            refine ⟨3527851839027429845341619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2351901226018286563561079 3527851839027429845341619)
            ·
              refine ⟨5291777758541144768012429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3527851839027429845341619 5291777758541144768012429)
              ·
                refine ⟨1984416659452929288004661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5291777758541144768012429 1984416659452929288004661)
                ·
                  refine ⟨186039061823712120750437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1984416659452929288004661 186039061823712120750437)
                  ·
                    rfl

theorem cell21_815197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_815197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_815197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_815197 prefixEnd_815197 := by exact prefixLift 815197
  have htrace : WordTrace (prefixWord ++ tailWord_815197) baseStart_815197 baseEnd_815197 := by
    simpa [prefixWord, tailWord_815197, baseEnd_815197] using wordTrace_append hprefix tailTrace_815197
  have hstable : (prefixWord ++ tailWord_815197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815197).length < 2 ^ (prefixWord ++ tailWord_815197).sum := by decide
  have hdescent : baseEnd_815197 < baseStart_815197 := by decide
  rcases family_descends (prefixWord ++ tailWord_815197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815225 : List Nat := [1, 2, 1, 3, 4, 2, 1, 7]
def baseStart_815225 : Nat := 118140960795 + 815225 * 2 ^ 59
def prefixEnd_815225 : Nat := 4983230072969 + 3 ^ 40 * 815225 * 2
def baseEnd_815225 : Nat := 62015150601730098094571

theorem tailTrace_815225 : CollatzResearch.WordTrace tailWord_815225 prefixEnd_815225 62015150601730098094571 := by
  unfold tailWord_815225
  simp only [CollatzResearch.WordTrace]
  refine ⟨29733698471586529190495129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19822465647724352793663419 29733698471586529190495129)
  ·
    refine ⟨22300273853689896892871347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29733698471586529190495129 22300273853689896892871347)
    ·
      refine ⟨33450410780534845339307021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22300273853689896892871347 33450410780534845339307021)
      ·
        refine ⟨12543904042700567002240133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33450410780534845339307021 12543904042700567002240133)
        ·
          refine ⟨2351982008006356312920025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12543904042700567002240133 2351982008006356312920025)
          ·
            refine ⟨1763986506004767234690019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2351982008006356312920025 1763986506004767234690019)
            ·
              refine ⟨2645979759007150852035029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1763986506004767234690019 2645979759007150852035029)
              ·
                refine ⟨62015150601730098094571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2645979759007150852035029 62015150601730098094571)
                ·
                  rfl

theorem cell21_815225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 7].length) (baseStart_815225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_815225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_815225 prefixEnd_815225 := by exact prefixLift 815225
  have htrace : WordTrace (prefixWord ++ tailWord_815225) baseStart_815225 baseEnd_815225 := by
    simpa [prefixWord, tailWord_815225, baseEnd_815225] using wordTrace_append hprefix tailTrace_815225
  have hstable : (prefixWord ++ tailWord_815225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815225).length < 2 ^ (prefixWord ++ tailWord_815225).sum := by decide
  have hdescent : baseEnd_815225 < baseStart_815225 := by decide
  rcases family_descends (prefixWord ++ tailWord_815225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815239 : List Nat := [1, 1, 4, 2, 1, 1, 2, 2, 7]
def baseStart_815239 : Nat := 118140960795 + 815239 * 2 ^ 59
def prefixEnd_815239 : Nat := 4983230072969 + 3 ^ 40 * 815239 * 2
def baseEnd_815239 : Nat := 186048646795929381050351

theorem tailTrace_815239 : CollatzResearch.WordTrace tailWord_815239 prefixEnd_815239 186048646795929381050351 := by
  unfold tailWord_815239
  simp only [CollatzResearch.WordTrace]
  refine ⟨29734209093535809581504771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19822806062357206387669847 29734209093535809581504771)
  ·
    refine ⟨44601313640303714372257157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29734209093535809581504771 44601313640303714372257157)
    ·
      refine ⟨8362746307556946444798217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44601313640303714372257157 8362746307556946444798217)
      ·
        refine ⟨6272059730667709833598663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8362746307556946444798217 6272059730667709833598663)
        ·
          refine ⟨9408089596001564750397995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6272059730667709833598663 9408089596001564750397995)
          ·
            refine ⟨14112134394002347125596993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9408089596001564750397995 14112134394002347125596993)
            ·
              refine ⟨10584100795501760344197745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14112134394002347125596993 10584100795501760344197745)
              ·
                refine ⟨7938075596626320258148309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10584100795501760344197745 7938075596626320258148309)
                ·
                  refine ⟨186048646795929381050351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7938075596626320258148309 186048646795929381050351)
                  ·
                    rfl

theorem cell21_815239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 7].length) (baseStart_815239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_815239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_815239 prefixEnd_815239 := by exact prefixLift 815239
  have htrace : WordTrace (prefixWord ++ tailWord_815239) baseStart_815239 baseEnd_815239 := by
    simpa [prefixWord, tailWord_815239, baseEnd_815239] using wordTrace_append hprefix tailTrace_815239
  have hstable : (prefixWord ++ tailWord_815239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815239).length < 2 ^ (prefixWord ++ tailWord_815239).sum := by decide
  have hdescent : baseEnd_815239 < baseStart_815239 := by decide
  rcases family_descends (prefixWord ++ tailWord_815239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815262 : List Nat := [4, 3, 1, 1, 3, 2, 2, 1, 4]
def baseStart_815262 : Nat := 118140960795 + 815262 * 2 ^ 59
def prefixEnd_815262 : Nat := 4983230072969 + 3 ^ 40 * 815262 * 2
def baseEnd_815262 : Nat := 186053895709286452166971

theorem tailTrace_815262 : CollatzResearch.WordTrace tailWord_815262 prefixEnd_815262 186053895709286452166971 := by
  unfold tailWord_815262
  simp only [CollatzResearch.WordTrace]
  refine ⟨3716880996556560563699005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19823365314968323006394693 3716880996556560563699005)
  ·
    refine ⟨1393830373708710211387127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3716880996556560563699005 1393830373708710211387127)
    ·
      refine ⟨2090745560563065317080691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1393830373708710211387127 2090745560563065317080691)
      ·
        refine ⟨3136118340844597975621037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2090745560563065317080691 3136118340844597975621037)
        ·
          refine ⟨1176044377816724240857889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3136118340844597975621037 1176044377816724240857889)
          ·
            refine ⟨882033283362543180643417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1176044377816724240857889 882033283362543180643417)
            ·
              refine ⟨661524962521907385482563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 882033283362543180643417 661524962521907385482563)
              ·
                refine ⟨992287443782861078223845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 661524962521907385482563 992287443782861078223845)
                ·
                  refine ⟨186053895709286452166971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 992287443782861078223845 186053895709286452166971)
                  ·
                    rfl

theorem cell21_815262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_815262 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_815262 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_815262 prefixEnd_815262 := by exact prefixLift 815262
  have htrace : WordTrace (prefixWord ++ tailWord_815262) baseStart_815262 baseEnd_815262 := by
    simpa [prefixWord, tailWord_815262, baseEnd_815262] using wordTrace_append hprefix tailTrace_815262
  have hstable : (prefixWord ++ tailWord_815262).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815262).length < 2 ^ (prefixWord ++ tailWord_815262).sum := by decide
  have hdescent : baseEnd_815262 < baseStart_815262 := by decide
  rcases family_descends (prefixWord ++ tailWord_815262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815394 : List Nat := [3, 3, 1, 1, 3, 1, 4, 5]
def baseStart_815394 : Nat := 118140960795 + 815394 * 2 ^ 59
def prefixEnd_815394 : Nat := 4983230072969 + 3 ^ 40 * 815394 * 2
def baseEnd_815394 : Nat := 62028006635894518655567

theorem tailTrace_815394 : CollatzResearch.WordTrace tailWord_815394 prefixEnd_815394 62028006635894518655567 := by
  unfold tailWord_815394
  simp only [CollatzResearch.WordTrace]
  refine ⟨7434965601993567763349309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19826574938649514035598157 7434965601993567763349309)
  ·
    refine ⟨2788112100747587911255991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7434965601993567763349309 2788112100747587911255991)
    ·
      refine ⟨4182168151121381866883987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2788112100747587911255991 4182168151121381866883987)
      ·
        refine ⟨6273252226682072800325981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4182168151121381866883987 6273252226682072800325981)
        ·
          refine ⟨2352469585005777300122243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6273252226682072800325981 2352469585005777300122243)
          ·
            refine ⟨3528704377508665950183365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2352469585005777300122243 3528704377508665950183365)
            ·
              refine ⟨661632070782874865659381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3528704377508665950183365 661632070782874865659381)
              ·
                refine ⟨62028006635894518655567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 661632070782874865659381 62028006635894518655567)
                ·
                  rfl

theorem cell21_815394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 5].length) (baseStart_815394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_815394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_815394 prefixEnd_815394 := by exact prefixLift 815394
  have htrace : WordTrace (prefixWord ++ tailWord_815394) baseStart_815394 baseEnd_815394 := by
    simpa [prefixWord, tailWord_815394, baseEnd_815394] using wordTrace_append hprefix tailTrace_815394
  have hstable : (prefixWord ++ tailWord_815394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815394).length < 2 ^ (prefixWord ++ tailWord_815394).sum := by decide
  have hdescent : baseEnd_815394 < baseStart_815394 := by decide
  rcases family_descends (prefixWord ++ tailWord_815394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815408 : List Nat := [2, 1, 1, 1, 2, 2, 2, 7, 3]
def baseStart_815408 : Nat := 118140960795 + 815408 * 2 ^ 59
def prefixEnd_815408 : Nat := 4983230072969 + 3 ^ 40 * 815408 * 2
def baseEnd_815408 : Nat := 186087214898422642733339

theorem tailTrace_815408 : CollatzResearch.WordTrace tailWord_815408 prefixEnd_815408 186087214898422642733339 := by
  unfold tailWord_815408
  simp only [CollatzResearch.WordTrace]
  refine ⟨14870186514961775722203439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19826915353282367629604585 14870186514961775722203439)
  ·
    refine ⟨22305279772442663583305159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14870186514961775722203439 22305279772442663583305159)
    ·
      refine ⟨33457919658663995374957739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22305279772442663583305159 33457919658663995374957739)
      ·
        refine ⟨50186879487995993062436609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33457919658663995374957739 50186879487995993062436609)
        ·
          refine ⟨37640159615996994796827457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50186879487995993062436609 37640159615996994796827457)
          ·
            refine ⟨28230119711997746097620593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37640159615996994796827457 28230119711997746097620593)
            ·
              refine ⟨21172589783998309573215445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28230119711997746097620593 21172589783998309573215445)
              ·
                refine ⟨496232573062460380622237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 21172589783998309573215445 496232573062460380622237)
                ·
                  refine ⟨186087214898422642733339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 496232573062460380622237 186087214898422642733339)
                  ·
                    rfl

theorem cell21_815408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 7, 3].length) (baseStart_815408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_815408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_815408 prefixEnd_815408 := by exact prefixLift 815408
  have htrace : WordTrace (prefixWord ++ tailWord_815408) baseStart_815408 baseEnd_815408 := by
    simpa [prefixWord, tailWord_815408, baseEnd_815408] using wordTrace_append hprefix tailTrace_815408
  have hstable : (prefixWord ++ tailWord_815408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815408).length < 2 ^ (prefixWord ++ tailWord_815408).sum := by decide
  have hdescent : baseEnd_815408 < baseStart_815408 := by decide
  rcases family_descends (prefixWord ++ tailWord_815408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815518 : List Nat := [4, 3, 1, 2, 1, 1, 1, 5, 3]
def baseStart_815518 : Nat := 118140960795 + 815518 * 2 ^ 59
def prefixEnd_815518 : Nat := 4983230072969 + 3 ^ 40 * 815518 * 2
def baseEnd_815518 : Nat := 186112318397086895899781

theorem tailTrace_815518 : CollatzResearch.WordTrace tailWord_815518 prefixEnd_815518 186112318397086895899781 := by
  unfold tailWord_815518
  simp only [CollatzResearch.WordTrace]
  refine ⟨3718048132440630028863901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19829590039683360153940805 3718048132440630028863901)
  ·
    refine ⟨1394268049665236260823963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3718048132440630028863901 1394268049665236260823963)
    ·
      refine ⟨2091402074497854391235945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1394268049665236260823963 2091402074497854391235945)
      ·
        refine ⟨1568551555873390793426959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2091402074497854391235945 1568551555873390793426959)
        ·
          refine ⟨2352827333810086190140439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1568551555873390793426959 2352827333810086190140439)
          ·
            refine ⟨3529241000715129285210659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2352827333810086190140439 3529241000715129285210659)
            ·
              refine ⟨5293861501072693927815989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3529241000715129285210659 5293861501072693927815989)
              ·
                refine ⟨496299515725565055732749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5293861501072693927815989 496299515725565055732749)
                ·
                  refine ⟨186112318397086895899781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 496299515725565055732749 186112318397086895899781)
                  ·
                    rfl

theorem cell21_815518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_815518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_815518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_815518 prefixEnd_815518 := by exact prefixLift 815518
  have htrace : WordTrace (prefixWord ++ tailWord_815518) baseStart_815518 baseEnd_815518 := by
    simpa [prefixWord, tailWord_815518, baseEnd_815518] using wordTrace_append hprefix tailTrace_815518
  have hstable : (prefixWord ++ tailWord_815518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815518).length < 2 ^ (prefixWord ++ tailWord_815518).sum := by decide
  have hdescent : baseEnd_815518 < baseStart_815518 := by decide
  rcases family_descends (prefixWord ++ tailWord_815518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815543 : List Nat := [1, 1, 3, 1, 3, 3, 1, 3, 5]
def baseStart_815543 : Nat := 118140960795 + 815543 * 2 ^ 59
def prefixEnd_815543 : Nat := 4983230072969 + 3 ^ 40 * 815543 * 2
def baseEnd_815543 : Nat := 186118023737692407983063

theorem tailTrace_815543 : CollatzResearch.WordTrace tailWord_815543 prefixEnd_815543 186118023737692407983063 := by
  unfold tailWord_815543
  simp only [CollatzResearch.WordTrace]
  refine ⟨29745296884434469500571283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19830197922956313000380855 29745296884434469500571283)
  ·
    refine ⟨44617945326651704250856925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29745296884434469500571283 44617945326651704250856925)
    ·
      refine ⟨16731729497494389094071347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44617945326651704250856925 16731729497494389094071347)
      ·
        refine ⟨25097594246241583641107021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16731729497494389094071347 25097594246241583641107021)
        ·
          refine ⟨9411597842340593865415133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25097594246241583641107021 9411597842340593865415133)
          ·
            refine ⟨3529349190877722699530675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9411597842340593865415133 3529349190877722699530675)
            ·
              refine ⟨5294023786316584049296013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3529349190877722699530675 5294023786316584049296013)
              ·
                refine ⟨1985258919868719018486005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5294023786316584049296013 1985258919868719018486005)
                ·
                  refine ⟨186118023737692407983063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1985258919868719018486005 186118023737692407983063)
                  ·
                    rfl

theorem cell21_815543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 5].length) (baseStart_815543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_815543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_815543 prefixEnd_815543 := by exact prefixLift 815543
  have htrace : WordTrace (prefixWord ++ tailWord_815543) baseStart_815543 baseEnd_815543 := by
    simpa [prefixWord, tailWord_815543, baseEnd_815543] using wordTrace_append hprefix tailTrace_815543
  have hstable : (prefixWord ++ tailWord_815543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815543).length < 2 ^ (prefixWord ++ tailWord_815543).sum := by decide
  have hdescent : baseEnd_815543 < baseStart_815543 := by decide
  rcases family_descends (prefixWord ++ tailWord_815543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815594 : List Nat := [3, 1, 3, 1, 3, 2, 3, 2, 3]
def baseStart_815594 : Nat := 118140960795 + 815594 * 2 ^ 59
def prefixEnd_815594 : Nat := 4983230072969 + 3 ^ 40 * 815594 * 2
def baseEnd_815594 : Nat := 186129662632527652632959

theorem tailTrace_815594 : CollatzResearch.WordTrace tailWord_815594 prefixEnd_815594 186129662632527652632959 := by
  unfold tailWord_815594
  simp only [CollatzResearch.WordTrace]
  refine ⟨7436789251812426302669459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19831438004833136807118557 7436789251812426302669459)
  ·
    refine ⟨11155183877718639454004189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7436789251812426302669459 11155183877718639454004189)
    ·
      refine ⟨4183193954144489795251571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11155183877718639454004189 4183193954144489795251571)
      ·
        refine ⟨6274790931216734692877357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4183193954144489795251571 6274790931216734692877357)
        ·
          refine ⟨2353046599206275509829009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6274790931216734692877357 2353046599206275509829009)
          ·
            refine ⟨1764784949404706632371757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2353046599206275509829009 1764784949404706632371757)
            ·
              refine ⟨661794356026764987139409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1764784949404706632371757 661794356026764987139409)
              ·
                refine ⟨496345767020073740354557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 661794356026764987139409 496345767020073740354557)
                ·
                  refine ⟨186129662632527652632959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 496345767020073740354557 186129662632527652632959)
                  ·
                    rfl

theorem cell21_815594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 2, 3].length) (baseStart_815594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_815594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_815594 prefixEnd_815594 := by exact prefixLift 815594
  have htrace : WordTrace (prefixWord ++ tailWord_815594) baseStart_815594 baseEnd_815594 := by
    simpa [prefixWord, tailWord_815594, baseEnd_815594] using wordTrace_append hprefix tailTrace_815594
  have hstable : (prefixWord ++ tailWord_815594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815594).length < 2 ^ (prefixWord ++ tailWord_815594).sum := by decide
  have hdescent : baseEnd_815594 < baseStart_815594 := by decide
  rcases family_descends (prefixWord ++ tailWord_815594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815633 : List Nat := [1, 2, 2, 1, 1, 2, 2, 4, 6]
def baseStart_815633 : Nat := 118140960795 + 815633 * 2 ^ 59
def prefixEnd_815633 : Nat := 4983230072969 + 3 ^ 40 * 815633 * 2
def baseEnd_815633 : Nat := 186138562963872251482879

theorem tailTrace_815633 : CollatzResearch.WordTrace tailWord_815633 prefixEnd_815633 186138562963872251482879 := by
  unfold tailWord_815633
  simp only [CollatzResearch.WordTrace]
  refine ⟨29748579454108414871347553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19832386302738943247565035 29748579454108414871347553)
  ·
    refine ⟨22311434590581311153510665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29748579454108414871347553 22311434590581311153510665)
    ·
      refine ⟨16733575942935983365132999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22311434590581311153510665 16733575942935983365132999)
      ·
        refine ⟨25100363914403975047699499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16733575942935983365132999 25100363914403975047699499)
        ·
          refine ⟨37650545871605962571549249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25100363914403975047699499 37650545871605962571549249)
          ·
            refine ⟨28237909403704471928661937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37650545871605962571549249 28237909403704471928661937)
            ·
              refine ⟨21178432052778353946496453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28237909403704471928661937 21178432052778353946496453)
              ·
                refine ⟨3970956009895941364968085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21178432052778353946496453 3970956009895941364968085)
                ·
                  refine ⟨186138562963872251482879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3970956009895941364968085 186138562963872251482879)
                  ·
                    rfl

theorem cell21_815633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 6].length) (baseStart_815633 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_815633 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_815633 prefixEnd_815633 := by exact prefixLift 815633
  have htrace : WordTrace (prefixWord ++ tailWord_815633) baseStart_815633 baseEnd_815633 := by
    simpa [prefixWord, tailWord_815633, baseEnd_815633] using wordTrace_append hprefix tailTrace_815633
  have hstable : (prefixWord ++ tailWord_815633).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815633).length < 2 ^ (prefixWord ++ tailWord_815633).sum := by decide
  have hdescent : baseEnd_815633 < baseStart_815633 := by decide
  rcases family_descends (prefixWord ++ tailWord_815633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815653 : List Nat := [1, 3, 1, 2, 2, 1, 6, 2, 3]
def baseStart_815653 : Nat := 118140960795 + 815653 * 2 ^ 59
def prefixEnd_815653 : Nat := 4983230072969 + 3 ^ 40 * 815653 * 2
def baseEnd_815653 : Nat := 186143127236356661149505

theorem tailTrace_815653 : CollatzResearch.WordTrace tailWord_815653 prefixEnd_815653 186143127236356661149505 := by
  unfold tailWord_815653
  simp only [CollatzResearch.WordTrace]
  refine ⟨29749308914035958287075613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19832872609357305524717075 29749308914035958287075613)
  ·
    refine ⟨11155990842763484357653355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29749308914035958287075613 11155990842763484357653355)
    ·
      refine ⟨16733986264145226536480033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11155990842763484357653355 16733986264145226536480033)
      ·
        refine ⟨12550489698108919902360025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16733986264145226536480033 12550489698108919902360025)
        ·
          refine ⟨9412867273581689926770019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12550489698108919902360025 9412867273581689926770019)
          ·
            refine ⟨14119300910372534890155029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9412867273581689926770019 14119300910372534890155029)
            ·
              refine ⟨661842230173712572976017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14119300910372534890155029 661842230173712572976017)
              ·
                refine ⟨496381672630284429732013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 661842230173712572976017 496381672630284429732013)
                ·
                  refine ⟨186143127236356661149505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 496381672630284429732013 186143127236356661149505)
                  ·
                    rfl

theorem cell21_815653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 2, 3].length) (baseStart_815653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_815653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_815653 prefixEnd_815653 := by exact prefixLift 815653
  have htrace : WordTrace (prefixWord ++ tailWord_815653) baseStart_815653 baseEnd_815653 := by
    simpa [prefixWord, tailWord_815653, baseEnd_815653] using wordTrace_append hprefix tailTrace_815653
  have hstable : (prefixWord ++ tailWord_815653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815653).length < 2 ^ (prefixWord ++ tailWord_815653).sum := by decide
  have hdescent : baseEnd_815653 < baseStart_815653 := by decide
  rcases family_descends (prefixWord ++ tailWord_815653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815664 : List Nat := [2, 1, 1, 1, 2, 3, 5, 6]
def baseStart_815664 : Nat := 118140960795 + 815664 * 2 ^ 59
def prefixEnd_815664 : Nat := 4983230072969 + 3 ^ 40 * 815664 * 2
def baseEnd_815664 : Nat := 62048545862074362155383

theorem tailTrace_815664 : CollatzResearch.WordTrace tailWord_815664 prefixEnd_815664 62048545862074362155383 := by
  unfold tailWord_815664
  simp only [CollatzResearch.WordTrace]
  refine ⟨14874855058498053582863023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19833140077997404777150697 14874855058498053582863023)
  ·
    refine ⟨22312282587747080374294535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14874855058498053582863023 22312282587747080374294535)
    ·
      refine ⟨33468423881620620561441803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22312282587747080374294535 33468423881620620561441803)
      ·
        refine ⟨50202635822430930842162705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33468423881620620561441803 50202635822430930842162705)
        ·
          refine ⟨37651976866823198131622029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50202635822430930842162705 37651976866823198131622029)
          ·
            refine ⟨14119491325058699299358261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37651976866823198131622029 14119491325058699299358261)
            ·
              refine ⟨1323702311724253059314837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14119491325058699299358261 1323702311724253059314837)
              ·
                refine ⟨62048545862074362155383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1323702311724253059314837 62048545862074362155383)
                ·
                  rfl

theorem cell21_815664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 6].length) (baseStart_815664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_815664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_815664 prefixEnd_815664 := by exact prefixLift 815664
  have htrace : WordTrace (prefixWord ++ tailWord_815664) baseStart_815664 baseEnd_815664 := by
    simpa [prefixWord, tailWord_815664, baseEnd_815664] using wordTrace_append hprefix tailTrace_815664
  have hstable : (prefixWord ++ tailWord_815664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815664).length < 2 ^ (prefixWord ++ tailWord_815664).sum := by decide
  have hdescent : baseEnd_815664 < baseStart_815664 := by decide
  rcases family_descends (prefixWord ++ tailWord_815664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815712 : List Nat := [2, 1, 1, 3, 2, 1, 4, 4, 3]
def baseStart_815712 : Nat := 118140960795 + 815712 * 2 ^ 59
def prefixEnd_815712 : Nat := 4983230072969 + 3 ^ 40 * 815712 * 2
def baseEnd_815712 : Nat := 186156591840185669666051

theorem tailTrace_815712 : CollatzResearch.WordTrace tailWord_815712 prefixEnd_815712 186156591840185669666051 := by
  unfold tailWord_815712
  simp only [CollatzResearch.WordTrace]
  refine ⟨14875730410411105681736695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19834307213881474242315593 14875730410411105681736695)
  ·
    refine ⟨22313595615616658522605043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14875730410411105681736695 22313595615616658522605043)
    ·
      refine ⟨33470393423424987783907565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22313595615616658522605043 33470393423424987783907565)
      ·
        refine ⟨12551397533784370418965337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33470393423424987783907565 12551397533784370418965337)
        ·
          refine ⟨9413548150338277814224003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12551397533784370418965337 9413548150338277814224003)
          ·
            refine ⟨14120322225507416721336005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9413548150338277814224003 14120322225507416721336005)
            ·
              refine ⟨2647560417282640635250501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14120322225507416721336005 2647560417282640635250501)
              ·
                refine ⟨496417578240495119109469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2647560417282640635250501 496417578240495119109469)
                ·
                  refine ⟨186156591840185669666051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 496417578240495119109469 186156591840185669666051)
                  ·
                    rfl

theorem cell21_815712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 4, 3].length) (baseStart_815712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_815712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_815712 prefixEnd_815712 := by exact prefixLift 815712
  have htrace : WordTrace (prefixWord ++ tailWord_815712) baseStart_815712 baseEnd_815712 := by
    simpa [prefixWord, tailWord_815712, baseEnd_815712] using wordTrace_append hprefix tailTrace_815712
  have hstable : (prefixWord ++ tailWord_815712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815712).length < 2 ^ (prefixWord ++ tailWord_815712).sum := by decide
  have hdescent : baseEnd_815712 < baseStart_815712 := by decide
  rcases family_descends (prefixWord ++ tailWord_815712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815777 : List Nat := [1, 2, 3, 3, 4, 1, 2, 1, 4]
def baseStart_815777 : Nat := 118140960795 + 815777 * 2 ^ 59
def prefixEnd_815777 : Nat := 4983230072969 + 3 ^ 40 * 815777 * 2
def baseEnd_815777 : Nat := 186171425725760001082585

theorem tailTrace_815777 : CollatzResearch.WordTrace tailWord_815777 prefixEnd_815777 186171425725760001082585 := by
  unfold tailWord_815777
  simp only [CollatzResearch.WordTrace]
  refine ⟨29753831565586727464589585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19835887710391151643059723 29753831565586727464589585)
  ·
    refine ⟨22315373674190045598442189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29753831565586727464589585 22315373674190045598442189)
    ·
      refine ⟨8368265127821267099415821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22315373674190045598442189 8368265127821267099415821)
      ·
        refine ⟨3138099422932975162280933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8368265127821267099415821 3138099422932975162280933)
        ·
          refine ⟨588393641799932842927675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3138099422932975162280933 588393641799932842927675)
          ·
            refine ⟨882590462699899264391513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 588393641799932842927675 882590462699899264391513)
            ·
              refine ⟨661942847024924448293635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 882590462699899264391513 661942847024924448293635)
              ·
                refine ⟨992914270537386672440453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 661942847024924448293635 992914270537386672440453)
                ·
                  refine ⟨186171425725760001082585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 992914270537386672440453 186171425725760001082585)
                  ·
                    rfl

theorem cell21_815777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 1, 4].length) (baseStart_815777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_815777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_815777 prefixEnd_815777 := by exact prefixLift 815777
  have htrace : WordTrace (prefixWord ++ tailWord_815777) baseStart_815777 baseEnd_815777 := by
    simpa [prefixWord, tailWord_815777, baseEnd_815777] using wordTrace_append hprefix tailTrace_815777
  have hstable : (prefixWord ++ tailWord_815777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815777).length < 2 ^ (prefixWord ++ tailWord_815777).sum := by decide
  have hdescent : baseEnd_815777 < baseStart_815777 := by decide
  rcases family_descends (prefixWord ++ tailWord_815777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815822 : List Nat := [4, 1, 1, 1, 3, 4, 2, 2, 3]
def baseStart_815822 : Nat := 118140960795 + 815822 * 2 ^ 59
def prefixEnd_815822 : Nat := 4983230072969 + 3 ^ 40 * 815822 * 2
def baseEnd_815822 : Nat := 186181695338849922832493

theorem tailTrace_815822 : CollatzResearch.WordTrace tailWord_815822 prefixEnd_815822 186181695338849922832493 := by
  unfold tailWord_815822
  simp only [CollatzResearch.WordTrace]
  refine ⟨3719434106302962518747215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19836981900282466766651813 3719434106302962518747215)
  ·
    refine ⟨5579151159454443778120823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3719434106302962518747215 5579151159454443778120823)
    ·
      refine ⟨8368726739181665667181235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5579151159454443778120823 8368726739181665667181235)
      ·
        refine ⟨12553090108772498500771853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8368726739181665667181235 12553090108772498500771853)
        ·
          refine ⟨4707408790789686937789445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12553090108772498500771853 4707408790789686937789445)
          ·
            refine ⟨882639148273066300835521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4707408790789686937789445 882639148273066300835521)
            ·
              refine ⟨661979361204799725626641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 882639148273066300835521 661979361204799725626641)
              ·
                refine ⟨496484520903599794219981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 661979361204799725626641 496484520903599794219981)
                ·
                  refine ⟨186181695338849922832493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 496484520903599794219981 186181695338849922832493)
                  ·
                    rfl

theorem cell21_815822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 2, 3].length) (baseStart_815822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_815822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_815822 prefixEnd_815822 := by exact prefixLift 815822
  have htrace : WordTrace (prefixWord ++ tailWord_815822) baseStart_815822 baseEnd_815822 := by
    simpa [prefixWord, tailWord_815822, baseEnd_815822] using wordTrace_append hprefix tailTrace_815822
  have hstable : (prefixWord ++ tailWord_815822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815822).length < 2 ^ (prefixWord ++ tailWord_815822).sum := by decide
  have hdescent : baseEnd_815822 < baseStart_815822 := by decide
  rcases family_descends (prefixWord ++ tailWord_815822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815864 : List Nat := [2, 1, 2, 1, 1, 2, 6, 3, 3]
def baseStart_815864 : Nat := 118140960795 + 815864 * 2 ^ 59
def prefixEnd_815864 : Nat := 4983230072969 + 3 ^ 40 * 815864 * 2
def baseEnd_815864 : Nat := 186191280311067183132407

theorem tailTrace_815864 : CollatzResearch.WordTrace tailWord_815864 prefixEnd_815864 186191280311067183132407 := by
  unfold tailWord_815864
  simp only [CollatzResearch.WordTrace]
  refine ⟨14878502358135770661503323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19838003144181027548671097 14878502358135770661503323)
  ·
    refine ⟨22317753537203655992254985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14878502358135770661503323 22317753537203655992254985)
    ·
      refine ⟨16738315152902741994191239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22317753537203655992254985 16738315152902741994191239)
      ·
        refine ⟨25107472729354112991286859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16738315152902741994191239 25107472729354112991286859)
        ·
          refine ⟨37661209094031169486930289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25107472729354112991286859 37661209094031169486930289)
          ·
            refine ⟨28245906820523377115197717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37661209094031169486930289 28245906820523377115197717)
            ·
              refine ⟨1324026882212033302274893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28245906820523377115197717 1324026882212033302274893)
              ·
                refine ⟨496510080829512488353085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1324026882212033302274893 496510080829512488353085)
                ·
                  refine ⟨186191280311067183132407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 496510080829512488353085 186191280311067183132407)
                  ·
                    rfl

theorem cell21_815864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 3, 3].length) (baseStart_815864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_815864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_815864 prefixEnd_815864 := by exact prefixLift 815864
  have htrace : WordTrace (prefixWord ++ tailWord_815864) baseStart_815864 baseEnd_815864 := by
    simpa [prefixWord, tailWord_815864, baseEnd_815864] using wordTrace_append hprefix tailTrace_815864
  have hstable : (prefixWord ++ tailWord_815864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815864).length < 2 ^ (prefixWord ++ tailWord_815864).sum := by decide
  have hdescent : baseEnd_815864 < baseStart_815864 := by decide
  rcases family_descends (prefixWord ++ tailWord_815864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815926 : List Nat := [5, 1, 2, 2, 2, 2, 7]
def baseStart_815926 : Nat := 118140960795 + 815926 * 2 ^ 59
def prefixEnd_815926 : Nat := 4983230072969 + 3 ^ 40 * 815926 * 2
def baseEnd_815926 : Nat := 20689492172863205899883

theorem tailTrace_815926 : CollatzResearch.WordTrace tailWord_815926 prefixEnd_815926 20689492172863205899883 := by
  unfold tailWord_815926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1859954127627932869485227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19839510694697950607842421 1859954127627932869485227)
  ·
    refine ⟨2789931191441899304227841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1859954127627932869485227 2789931191441899304227841)
    ·
      refine ⟨2092448393581424478170881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2789931191441899304227841 2092448393581424478170881)
      ·
        refine ⟨1569336295186068358628161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2092448393581424478170881 1569336295186068358628161)
        ·
          refine ⟨1177002221389551268971121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1569336295186068358628161 1177002221389551268971121)
          ·
            refine ⟨882751666042163451728341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1177002221389551268971121 882751666042163451728341)
            ·
              refine ⟨20689492172863205899883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 882751666042163451728341 20689492172863205899883)
              ·
                rfl

theorem cell21_815926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 7].length) (baseStart_815926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_815926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_815926 prefixEnd_815926 := by exact prefixLift 815926
  have htrace : WordTrace (prefixWord ++ tailWord_815926) baseStart_815926 baseEnd_815926 := by
    simpa [prefixWord, tailWord_815926, baseEnd_815926] using wordTrace_append hprefix tailTrace_815926
  have hstable : (prefixWord ++ tailWord_815926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815926).length < 2 ^ (prefixWord ++ tailWord_815926).sum := by decide
  have hdescent : baseEnd_815926 < baseStart_815926 := by decide
  rcases family_descends (prefixWord ++ tailWord_815926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815954 : List Nat := [3, 2, 2, 1, 1, 2, 3, 3, 4]
def baseStart_815954 : Nat := 118140960795 + 815954 * 2 ^ 59
def prefixEnd_815954 : Nat := 4983230072969 + 3 ^ 40 * 815954 * 2
def baseEnd_815954 : Nat := 186211819537247026632223

theorem tailTrace_815954 : CollatzResearch.WordTrace tailWord_815954 prefixEnd_815954 186211819537247026632223 := by
  unfold tailWord_815954
  simp only [CollatzResearch.WordTrace]
  refine ⟨7440071821486371673445729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19840191523963657795855277 7440071821486371673445729)
  ·
    refine ⟨5580053866114778755084297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7440071821486371673445729 5580053866114778755084297)
    ·
      refine ⟨4185040399586084066313223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5580053866114778755084297 4185040399586084066313223)
      ·
        refine ⟨6277560599379126099469835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4185040399586084066313223 6277560599379126099469835)
        ·
          refine ⟨9416340899068689149204753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6277560599379126099469835 9416340899068689149204753)
          ·
            refine ⟨7062255674301516861903565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9416340899068689149204753 7062255674301516861903565)
            ·
              refine ⟨2648345877863068823213837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7062255674301516861903565 2648345877863068823213837)
              ·
                refine ⟨993129704198650808705189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2648345877863068823213837 993129704198650808705189)
                ·
                  refine ⟨186211819537247026632223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 993129704198650808705189 186211819537247026632223)
                  ·
                    rfl

theorem cell21_815954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_815954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_815954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_815954 prefixEnd_815954 := by exact prefixLift 815954
  have htrace : WordTrace (prefixWord ++ tailWord_815954) baseStart_815954 baseEnd_815954 := by
    simpa [prefixWord, tailWord_815954, baseEnd_815954] using wordTrace_append hprefix tailTrace_815954
  have hstable : (prefixWord ++ tailWord_815954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815954).length < 2 ^ (prefixWord ++ tailWord_815954).sum := by decide
  have hdescent : baseEnd_815954 < baseStart_815954 := by decide
  rcases family_descends (prefixWord ++ tailWord_815954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816033 : List Nat := [1, 2, 3, 4, 1, 2, 2, 3, 3]
def baseStart_816033 : Nat := 118140960795 + 816033 * 2 ^ 59
def prefixEnd_816033 : Nat := 4983230072969 + 3 ^ 40 * 816033 * 2
def baseEnd_816033 : Nat := 186229848413560444815395

theorem tailTrace_816033 : CollatzResearch.WordTrace tailWord_816033 prefixEnd_816033 186229848413560444815395 := by
  unfold tailWord_816033
  simp only [CollatzResearch.WordTrace]
  refine ⟨29763168652659283185908753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19842112435106188790605835 29763168652659283185908753)
  ·
    refine ⟨22322376489494462389431565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29763168652659283185908753 22322376489494462389431565)
    ·
      refine ⟨8370891183560423396036837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22322376489494462389431565 8370891183560423396036837)
      ·
        refine ⟨1569542096917579386756907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8370891183560423396036837 1569542096917579386756907)
        ·
          refine ⟨2354313145376369080135361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1569542096917579386756907 2354313145376369080135361)
          ·
            refine ⟨1765734859032276810101521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2354313145376369080135361 1765734859032276810101521)
            ·
              refine ⟨1324301144274207607576141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1765734859032276810101521 1324301144274207607576141)
              ·
                refine ⟨496612929102827852841053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1324301144274207607576141 496612929102827852841053)
                ·
                  refine ⟨186229848413560444815395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 496612929102827852841053 186229848413560444815395)
                  ·
                    rfl

theorem cell21_816033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 3, 3].length) (baseStart_816033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_816033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_816033 prefixEnd_816033 := by exact prefixLift 816033
  have htrace : WordTrace (prefixWord ++ tailWord_816033) baseStart_816033 baseEnd_816033 := by
    simpa [prefixWord, tailWord_816033, baseEnd_816033] using wordTrace_append hprefix tailTrace_816033
  have hstable : (prefixWord ++ tailWord_816033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816033).length < 2 ^ (prefixWord ++ tailWord_816033).sum := by decide
  have hdescent : baseEnd_816033 < baseStart_816033 := by decide
  rcases family_descends (prefixWord ++ tailWord_816033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816070 : List Nat := [6, 1, 3, 1, 2, 1, 2, 5]
def baseStart_816070 : Nat := 118140960795 + 816070 * 2 ^ 59
def prefixEnd_816070 : Nat := 4983230072969 + 3 ^ 40 * 816070 * 2
def baseEnd_816070 : Nat := 62079430772552200899551

theorem tailTrace_816070 : CollatzResearch.WordTrace tailWord_816070 prefixEnd_816070 62079430772552200899551 := by
  unfold tailWord_816070
  simp only [CollatzResearch.WordTrace]
  refine ⟨930141192297663703281427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19843012102350159003337109 930141192297663703281427)
  ·
    refine ⟨1395211788446495554922141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 930141192297663703281427 1395211788446495554922141)
    ·
      refine ⟨523204420667435833095803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1395211788446495554922141 523204420667435833095803)
      ·
        refine ⟨784806631001153749643705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 523204420667435833095803 784806631001153749643705)
        ·
          refine ⟨588604973250865312232779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 784806631001153749643705 588604973250865312232779)
          ·
            refine ⟨882907459876297968349169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 588604973250865312232779 882907459876297968349169)
            ·
              refine ⟨662180594907223476261877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 882907459876297968349169 662180594907223476261877)
              ·
                refine ⟨62079430772552200899551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 662180594907223476261877 62079430772552200899551)
                ·
                  rfl

theorem cell21_816070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_816070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_816070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_816070 prefixEnd_816070 := by exact prefixLift 816070
  have htrace : WordTrace (prefixWord ++ tailWord_816070) baseStart_816070 baseEnd_816070 := by
    simpa [prefixWord, tailWord_816070, baseEnd_816070] using wordTrace_append hprefix tailTrace_816070
  have hstable : (prefixWord ++ tailWord_816070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816070).length < 2 ^ (prefixWord ++ tailWord_816070).sum := by decide
  have hdescent : baseEnd_816070 < baseStart_816070 := by decide
  rcases family_descends (prefixWord ++ tailWord_816070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816089 : List Nat := [1, 2, 1, 2, 5, 1, 1, 2, 6]
def baseStart_816089 : Nat := 118140960795 + 816089 * 2 ^ 59
def prefixEnd_816089 : Nat := 4983230072969 + 3 ^ 40 * 816089 * 2
def baseEnd_816089 : Nat := 186242628376516791881947

theorem tailTrace_816089 : CollatzResearch.WordTrace tailWord_816089 prefixEnd_816089 186242628376516791881947 := by
  unfold tailWord_816089
  simp only [CollatzResearch.WordTrace]
  refine ⟨29765211140456404749947321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19843474093637603166631547 29765211140456404749947321)
  ·
    refine ⟨22323908355342303562460491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29765211140456404749947321 22323908355342303562460491)
    ·
      refine ⟨33485862533013455343690737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22323908355342303562460491 33485862533013455343690737)
      ·
        refine ⟨25114396899760091507768053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33485862533013455343690737 25114396899760091507768053)
        ·
          refine ⟨2354474709352508578853255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25114396899760091507768053 2354474709352508578853255)
          ·
            refine ⟨3531712064028762868279883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2354474709352508578853255 3531712064028762868279883)
            ·
              refine ⟨5297568096043144302419825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3531712064028762868279883 5297568096043144302419825)
              ·
                refine ⟨3973176072032358226814869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5297568096043144302419825 3973176072032358226814869)
                ·
                  refine ⟨186242628376516791881947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3973176072032358226814869 186242628376516791881947)
                  ·
                    rfl

theorem cell21_816089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 6].length) (baseStart_816089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_816089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_816089 prefixEnd_816089 := by exact prefixLift 816089
  have htrace : WordTrace (prefixWord ++ tailWord_816089) baseStart_816089 baseEnd_816089 := by
    simpa [prefixWord, tailWord_816089, baseEnd_816089] using wordTrace_append hprefix tailTrace_816089
  have hstable : (prefixWord ++ tailWord_816089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816089).length < 2 ^ (prefixWord ++ tailWord_816089).sum := by decide
  have hdescent : baseEnd_816089 < baseStart_816089 := by decide
  rcases family_descends (prefixWord ++ tailWord_816089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816261 : List Nat := [1, 3, 1, 1, 6, 2, 1, 3, 3]
def baseStart_816261 : Nat := 118140960795 + 816261 * 2 ^ 59
def prefixEnd_816261 : Nat := 4983230072969 + 3 ^ 40 * 816261 * 2
def baseEnd_816261 : Nat := 186281881119882715014929

theorem tailTrace_816261 : CollatzResearch.WordTrace tailWord_816261 prefixEnd_816261 186281881119882715014929 := by
  unfold tailWord_816261
  simp only [CollatzResearch.WordTrace]
  refine ⟨29771484495833278125208637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19847656330555518750139091 29771484495833278125208637)
  ·
    refine ⟨11164306685937479296953239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29771484495833278125208637 11164306685937479296953239)
    ·
      refine ⟨16746460028906218945429859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11164306685937479296953239 16746460028906218945429859)
      ·
        refine ⟨25119690043359328418144789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16746460028906218945429859 25119690043359328418144789)
        ·
          refine ⟨1177485470782468519600537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25119690043359328418144789 1177485470782468519600537)
          ·
            refine ⟨883114103086851389700403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1177485470782468519600537 883114103086851389700403)
            ·
              refine ⟨1324671154630277084550605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 883114103086851389700403 1324671154630277084550605)
              ·
                refine ⟨496751682986353906706477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1324671154630277084550605 496751682986353906706477)
                ·
                  refine ⟨186281881119882715014929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 496751682986353906706477 186281881119882715014929)
                  ·
                    rfl

theorem cell21_816261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 3, 3].length) (baseStart_816261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_816261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_816261 prefixEnd_816261 := by exact prefixLift 816261
  have htrace : WordTrace (prefixWord ++ tailWord_816261) baseStart_816261 baseEnd_816261 := by
    simpa [prefixWord, tailWord_816261, baseEnd_816261] using wordTrace_append hprefix tailTrace_816261
  have hstable : (prefixWord ++ tailWord_816261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816261).length < 2 ^ (prefixWord ++ tailWord_816261).sum := by decide
  have hdescent : baseEnd_816261 < baseStart_816261 := by decide
  rcases family_descends (prefixWord ++ tailWord_816261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816300 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 8]
def baseStart_816300 : Nat := 118140960795 + 816300 * 2 ^ 59
def prefixEnd_816300 : Nat := 4983230072969 + 3 ^ 40 * 816300 * 2
def baseEnd_816300 : Nat := 186290781451227313864849

theorem tailTrace_816300 : CollatzResearch.WordTrace tailWord_816300 prefixEnd_816300 186290781451227313864849 := by
  unfold tailWord_816300
  simp only [CollatzResearch.WordTrace]
  refine ⟨14886453471345993892939177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19848604628461325190585569 14886453471345993892939177)
  ·
    refine ⟨11164840103509495419704383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14886453471345993892939177 11164840103509495419704383)
    ·
      refine ⟨16747260155264243129556575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11164840103509495419704383 16747260155264243129556575)
      ·
        refine ⟨25120890232896364694334863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16747260155264243129556575 25120890232896364694334863)
        ·
          refine ⟨37681335349344547041502295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25120890232896364694334863 37681335349344547041502295)
          ·
            refine ⟨56522003024016820562253443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37681335349344547041502295 56522003024016820562253443)
            ·
              refine ⟨84783004536025230843380165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56522003024016820562253443 84783004536025230843380165)
              ·
                refine ⟨15896813350504730783133781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84783004536025230843380165 15896813350504730783133781)
                ·
                  refine ⟨186290781451227313864849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15896813350504730783133781 186290781451227313864849)
                  ·
                    rfl

theorem cell21_816300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_816300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_816300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_816300 prefixEnd_816300 := by exact prefixLift 816300
  have htrace : WordTrace (prefixWord ++ tailWord_816300) baseStart_816300 baseEnd_816300 := by
    simpa [prefixWord, tailWord_816300, baseEnd_816300] using wordTrace_append hprefix tailTrace_816300
  have hstable : (prefixWord ++ tailWord_816300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816300).length < 2 ^ (prefixWord ++ tailWord_816300).sum := by decide
  have hdescent : baseEnd_816300 < baseStart_816300 := by decide
  rcases family_descends (prefixWord ++ tailWord_816300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816362 : List Nat := [3, 1, 3, 1, 1, 3, 1, 1, 7]
def baseStart_816362 : Nat := 118140960795 + 816362 * 2 ^ 59
def prefixEnd_816362 : Nat := 4983230072969 + 3 ^ 40 * 816362 * 2
def baseEnd_816362 : Nat := 186304930695928983831389

theorem tailTrace_816362 : CollatzResearch.WordTrace tailWord_816362 prefixEnd_816362 186304930695928983831389 := by
  unfold tailWord_816362
  simp only [CollatzResearch.WordTrace]
  refine ⟨7443792067116843093658835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19850112178978248249756893 7443792067116843093658835)
  ·
    refine ⟨11165688100675264640488253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7443792067116843093658835 11165688100675264640488253)
    ·
      refine ⟨4187133037753224240183095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11165688100675264640488253 4187133037753224240183095)
      ·
        refine ⟨6280699556629836360274643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4187133037753224240183095 6280699556629836360274643)
        ·
          refine ⟨9421049334944754540411965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6280699556629836360274643 9421049334944754540411965)
          ·
            refine ⟨3532893500604282952654487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9421049334944754540411965 3532893500604282952654487)
            ·
              refine ⟨5299340250906424428981731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3532893500604282952654487 5299340250906424428981731)
              ·
                refine ⟨7949010376359636643472597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5299340250906424428981731 7949010376359636643472597)
                ·
                  refine ⟨186304930695928983831389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7949010376359636643472597 186304930695928983831389)
                  ·
                    rfl

theorem cell21_816362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_816362 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_816362 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_816362 prefixEnd_816362 := by exact prefixLift 816362
  have htrace : WordTrace (prefixWord ++ tailWord_816362) baseStart_816362 baseEnd_816362 := by
    simpa [prefixWord, tailWord_816362, baseEnd_816362] using wordTrace_append hprefix tailTrace_816362
  have hstable : (prefixWord ++ tailWord_816362).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816362).length < 2 ^ (prefixWord ++ tailWord_816362).sum := by decide
  have hdescent : baseEnd_816362 < baseStart_816362 := by decide
  rcases family_descends (prefixWord ++ tailWord_816362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816365 : List Nat := [1, 5, 1, 2, 2, 2, 3, 5]
def baseStart_816365 : Nat := 118140960795 + 816365 * 2 ^ 59
def prefixEnd_816365 : Nat := 4983230072969 + 3 ^ 40 * 816365 * 2
def baseEnd_816365 : Nat := 62101871778933881760461

theorem tailTrace_816365 : CollatzResearch.WordTrace tailWord_816365 prefixEnd_816365 62101871778933881760461 := by
  unfold tailWord_816365
  simp only [CollatzResearch.WordTrace]
  refine ⟨29775277687456503886994549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19850185124971002591329699 29775277687456503886994549)
  ·
    refine ⟨2791432283199047239405739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29775277687456503886994549 2791432283199047239405739)
    ·
      refine ⟨4187148424798570859108609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2791432283199047239405739 4187148424798570859108609)
      ·
        refine ⟨3140361318598928144331457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4187148424798570859108609 3140361318598928144331457)
        ·
          refine ⟨2355270988949196108248593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3140361318598928144331457 2355270988949196108248593)
          ·
            refine ⟨1766453241711897081186445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2355270988949196108248593 1766453241711897081186445)
            ·
              refine ⟨662419965641961405444917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1766453241711897081186445 662419965641961405444917)
              ·
                refine ⟨62101871778933881760461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 662419965641961405444917 62101871778933881760461)
                ·
                  rfl

theorem cell21_816365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 5].length) (baseStart_816365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_816365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_816365 prefixEnd_816365 := by exact prefixLift 816365
  have htrace : WordTrace (prefixWord ++ tailWord_816365) baseStart_816365 baseEnd_816365 := by
    simpa [prefixWord, tailWord_816365, baseEnd_816365] using wordTrace_append hprefix tailTrace_816365
  have hstable : (prefixWord ++ tailWord_816365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816365).length < 2 ^ (prefixWord ++ tailWord_816365).sum := by decide
  have hdescent : baseEnd_816365 < baseStart_816365 := by decide
  rcases family_descends (prefixWord ++ tailWord_816365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816407 : List Nat := [1, 1, 3, 4, 1, 1, 2, 8]
def baseStart_816407 : Nat := 118140960795 + 816407 * 2 ^ 59
def prefixEnd_816407 : Nat := 4983230072969 + 3 ^ 40 * 816407 * 2
def baseEnd_816407 : Nat := 62105066769672968527099

theorem tailTrace_816407 : CollatzResearch.WordTrace tailWord_816407 prefixEnd_816407 62105066769672968527099 := by
  unfold tailWord_816407
  simp only [CollatzResearch.WordTrace]
  refine ⟨29776809553304345060023475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19851206368869563373348983 29776809553304345060023475)
  ·
    refine ⟨44665214329956517590035213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29776809553304345060023475 44665214329956517590035213)
    ·
      refine ⟨16749455373733694096263205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44665214329956517590035213 16749455373733694096263205)
      ·
        refine ⟨3140522882575067643049351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16749455373733694096263205 3140522882575067643049351)
        ·
          refine ⟨4710784323862601464574027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3140522882575067643049351 4710784323862601464574027)
          ·
            refine ⟨7066176485793902196861041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4710784323862601464574027 7066176485793902196861041)
            ·
              refine ⟨5299632364345426647645781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7066176485793902196861041 5299632364345426647645781)
              ·
                refine ⟨62105066769672968527099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5299632364345426647645781 62105066769672968527099)
                ·
                  rfl

theorem cell21_816407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 8].length) (baseStart_816407 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_816407 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_816407 prefixEnd_816407 := by exact prefixLift 816407
  have htrace : WordTrace (prefixWord ++ tailWord_816407) baseStart_816407 baseEnd_816407 := by
    simpa [prefixWord, tailWord_816407, baseEnd_816407] using wordTrace_append hprefix tailTrace_816407
  have hstable : (prefixWord ++ tailWord_816407).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816407).length < 2 ^ (prefixWord ++ tailWord_816407).sum := by decide
  have hdescent : baseEnd_816407 < baseStart_816407 := by decide
  rcases family_descends (prefixWord ++ tailWord_816407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816424 : List Nat := [2, 1, 5, 1, 2, 2, 1, 7]
def baseStart_816424 : Nat := 118140960795 + 816424 * 2 ^ 59
def prefixEnd_816424 : Nat := 4983230072969 + 3 ^ 40 * 816424 * 2
def baseEnd_816424 : Nat := 62106359980210217932643

theorem tailTrace_816424 : CollatzResearch.WordTrace tailWord_816424 prefixEnd_816424 62106359980210217932643 := by
  unfold tailWord_816424
  simp only [CollatzResearch.WordTrace]
  refine ⟨14888714797121378481696163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19851619729495171308928217 14888714797121378481696163)
  ·
    refine ⟨22333072195682067722544245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14888714797121378481696163 22333072195682067722544245)
    ·
      refine ⟨2093725518345193848988523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22333072195682067722544245 2093725518345193848988523)
      ·
        refine ⟨3140588277517790773482785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2093725518345193848988523 3140588277517790773482785)
        ·
          refine ⟨2355441208138343080112089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3140588277517790773482785 2355441208138343080112089)
          ·
            refine ⟨1766580906103757310084067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2355441208138343080112089 1766580906103757310084067)
            ·
              refine ⟨2649871359155635965126101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1766580906103757310084067 2649871359155635965126101)
              ·
                refine ⟨62106359980210217932643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2649871359155635965126101 62106359980210217932643)
                ·
                  rfl

theorem cell21_816424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 7].length) (baseStart_816424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_816424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_816424 prefixEnd_816424 := by exact prefixLift 816424
  have htrace : WordTrace (prefixWord ++ tailWord_816424) baseStart_816424 baseEnd_816424 := by
    simpa [prefixWord, tailWord_816424, baseEnd_816424] using wordTrace_append hprefix tailTrace_816424
  have hstable : (prefixWord ++ tailWord_816424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816424).length < 2 ^ (prefixWord ++ tailWord_816424).sum := by decide
  have hdescent : baseEnd_816424 < baseStart_816424 := by decide
  rcases family_descends (prefixWord ++ tailWord_816424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816441 : List Nat := [1, 2, 1, 6, 3, 1, 7]
def baseStart_816441 : Nat := 118140960795 + 816441 * 2 ^ 59
def prefixEnd_816441 : Nat := 4983230072969 + 3 ^ 40 * 816441 * 2
def baseEnd_816441 : Nat := 20702551063582489112729

theorem tailTrace_816441 : CollatzResearch.WordTrace tailWord_816441 prefixEnd_816441 20702551063582489112729 := by
  unfold tailWord_816441
  simp only [CollatzResearch.WordTrace]
  refine ⟨29778049635181168866761177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19852033090120779244507451 29778049635181168866761177)
  ·
    refine ⟨22333537226385876650070883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29778049635181168866761177 22333537226385876650070883)
    ·
      refine ⟨33500305839578814975106325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22333537226385876650070883 33500305839578814975106325)
      ·
        refine ⟨1570326836230256951958109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33500305839578814975106325 1570326836230256951958109)
        ·
          refine ⟨588872563586346356984291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1570326836230256951958109 588872563586346356984291)
          ·
            refine ⟨883308845379519535476437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 588872563586346356984291 883308845379519535476437)
            ·
              refine ⟨20702551063582489112729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 883308845379519535476437 20702551063582489112729)
              ·
                rfl

theorem cell21_816441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 7].length) (baseStart_816441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_816441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_816441 prefixEnd_816441 := by exact prefixLift 816441
  have htrace : WordTrace (prefixWord ++ tailWord_816441) baseStart_816441 baseEnd_816441 := by
    simpa [prefixWord, tailWord_816441, baseEnd_816441] using wordTrace_append hprefix tailTrace_816441
  have hstable : (prefixWord ++ tailWord_816441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816441).length < 2 ^ (prefixWord ++ tailWord_816441).sum := by decide
  have hdescent : baseEnd_816441 < baseStart_816441 := by decide
  rcases family_descends (prefixWord ++ tailWord_816441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816455 : List Nat := [1, 1, 4, 1, 2, 5, 1, 1, 5]
def baseStart_816455 : Nat := 118140960795 + 816455 * 2 ^ 59
def prefixEnd_816455 : Nat := 4983230072969 + 3 ^ 40 * 816455 * 2
def baseEnd_816455 : Nat := 186326154562981488781199

theorem tailTrace_816455 : CollatzResearch.WordTrace tailWord_816455 prefixEnd_816455 186326154562981488781199 := by
  unfold tailWord_816455
  simp only [CollatzResearch.WordTrace]
  refine ⟨29778560257130449257770819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19852373504753632838513879 29778560257130449257770819)
  ·
    refine ⟨44667840385695673886656229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29778560257130449257770819 44667840385695673886656229)
    ·
      refine ⟨8375220072317938853748043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44667840385695673886656229 8375220072317938853748043)
      ·
        refine ⟨12562830108476908280622065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8375220072317938853748043 12562830108476908280622065)
        ·
          refine ⟨9422122581357681210466549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12562830108476908280622065 9422122581357681210466549)
          ·
            refine ⟨883323992002282613481239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9422122581357681210466549 883323992002282613481239)
            ·
              refine ⟨1324985988003423920221859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 883323992002282613481239 1324985988003423920221859)
              ·
                refine ⟨1987478982005135880332789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1324985988003423920221859 1987478982005135880332789)
                ·
                  refine ⟨186326154562981488781199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1987478982005135880332789 186326154562981488781199)
                  ·
                    rfl

theorem cell21_816455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 5].length) (baseStart_816455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_816455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_816455 prefixEnd_816455 := by exact prefixLift 816455
  have htrace : WordTrace (prefixWord ++ tailWord_816455) baseStart_816455 baseEnd_816455 := by
    simpa [prefixWord, tailWord_816455, baseEnd_816455] using wordTrace_append hprefix tailTrace_816455
  have hstable : (prefixWord ++ tailWord_816455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816455).length < 2 ^ (prefixWord ++ tailWord_816455).sum := by decide
  have hdescent : baseEnd_816455 < baseStart_816455 := by decide
  rcases family_descends (prefixWord ++ tailWord_816455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816461 : List Nat := [1, 6, 1, 3, 1, 2, 2, 1, 4]
def baseStart_816461 : Nat := 118140960795 + 816461 * 2 ^ 59
def prefixEnd_816461 : Nat := 4983230072969 + 3 ^ 40 * 816461 * 2
def baseEnd_816461 : Nat := 186327523844726811681187

theorem tailTrace_816461 : CollatzResearch.WordTrace tailWord_816461 prefixEnd_816461 186327523844726811681187 := by
  unfold tailWord_816461
  simp only [CollatzResearch.WordTrace]
  refine ⟨29778779095108712282489237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19852519396739141521659491 29778779095108712282489237)
  ·
    refine ⟨1395880270083220888241683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 29778779095108712282489237 1395880270083220888241683)
    ·
      refine ⟨2093820405124831332362525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1395880270083220888241683 2093820405124831332362525)
      ·
        refine ⟨785182651921811749635947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2093820405124831332362525 785182651921811749635947)
        ·
          refine ⟨1177773977882717624453921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 785182651921811749635947 1177773977882717624453921)
          ·
            refine ⟨883330483412038218340441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1177773977882717624453921 883330483412038218340441)
            ·
              refine ⟨662497862559028663755331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 883330483412038218340441 662497862559028663755331)
              ·
                refine ⟨993746793838542995632997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 662497862559028663755331 993746793838542995632997)
                ·
                  refine ⟨186327523844726811681187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 993746793838542995632997 186327523844726811681187)
                  ·
                    rfl

theorem cell21_816461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_816461 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_816461 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_816461 prefixEnd_816461 := by exact prefixLift 816461
  have htrace : WordTrace (prefixWord ++ tailWord_816461) baseStart_816461 baseEnd_816461 := by
    simpa [prefixWord, tailWord_816461, baseEnd_816461] using wordTrace_append hprefix tailTrace_816461
  have hstable : (prefixWord ++ tailWord_816461).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816461).length < 2 ^ (prefixWord ++ tailWord_816461).sum := by decide
  have hdescent : baseEnd_816461 < baseStart_816461 := by decide
  rcases family_descends (prefixWord ++ tailWord_816461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816483 : List Nat := [1, 1, 1, 5, 2, 2, 2, 7]
def baseStart_816483 : Nat := 118140960795 + 816483 * 2 ^ 59
def prefixEnd_816483 : Nat := 4983230072969 + 3 ^ 40 * 816483 * 2
def baseEnd_816483 : Nat := 62110848181486554104825

theorem tailTrace_816483 : CollatzResearch.WordTrace tailWord_816483 prefixEnd_816483 62110848181486554104825 := by
  unfold tailWord_816483
  simp only [CollatzResearch.WordTrace]
  refine ⟨29779581501029010039790103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19853054334019340026526735 29779581501029010039790103)
  ·
    refine ⟨44669372251543515059685155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29779581501029010039790103 44669372251543515059685155)
    ·
      refine ⟨67004058377315272589527733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44669372251543515059685155 67004058377315272589527733)
      ·
        refine ⟨6281630472873306805268225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67004058377315272589527733 6281630472873306805268225)
        ·
          refine ⟨4711222854654980103951169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6281630472873306805268225 4711222854654980103951169)
          ·
            refine ⟨3533417140991235077963377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4711222854654980103951169 3533417140991235077963377)
            ·
              refine ⟨2650062855743426308472533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3533417140991235077963377 2650062855743426308472533)
              ·
                refine ⟨62110848181486554104825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2650062855743426308472533 62110848181486554104825)
                ·
                  rfl

theorem cell21_816483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 7].length) (baseStart_816483 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_816483 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_816483 prefixEnd_816483 := by exact prefixLift 816483
  have htrace : WordTrace (prefixWord ++ tailWord_816483) baseStart_816483 baseEnd_816483 := by
    simpa [prefixWord, tailWord_816483, baseEnd_816483] using wordTrace_append hprefix tailTrace_816483
  have hstable : (prefixWord ++ tailWord_816483).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816483).length < 2 ^ (prefixWord ++ tailWord_816483).sum := by decide
  have hdescent : baseEnd_816483 < baseStart_816483 := by decide
  rcases family_descends (prefixWord ++ tailWord_816483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816590 : List Nat := [4, 1, 1, 1, 2, 1, 4, 2, 5]
def baseStart_816590 : Nat := 118140960795 + 816590 * 2 ^ 59
def prefixEnd_816590 : Nat := 4983230072969 + 3 ^ 40 * 816590 * 2
def baseEnd_816590 : Nat := 186356963402251254030923

theorem tailTrace_816590 : CollatzResearch.WordTrace tailWord_816590 prefixEnd_816590 186356963402251254030923 := by
  unfold tailWord_816590
  simp only [CollatzResearch.WordTrace]
  refine ⟨3722935513955170914241903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19855656074427578209290149 3722935513955170914241903)
  ·
    refine ⟨5584403270932756371362855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3722935513955170914241903 5584403270932756371362855)
    ·
      refine ⟨8376604906399134557044283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5584403270932756371362855 8376604906399134557044283)
      ·
        refine ⟨12564907359598701835566425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8376604906399134557044283 12564907359598701835566425)
        ·
          refine ⟨9423680519699026376674819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12564907359598701835566425 9423680519699026376674819)
          ·
            refine ⟨14135520779548539565012229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9423680519699026376674819 14135520779548539565012229)
            ·
              refine ⟨2650410146165351168439793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14135520779548539565012229 2650410146165351168439793)
              ·
                refine ⟨1987807609624013376329845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2650410146165351168439793 1987807609624013376329845)
                ·
                  refine ⟨186356963402251254030923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1987807609624013376329845 186356963402251254030923)
                  ·
                    rfl

theorem cell21_816590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_816590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_816590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_816590 prefixEnd_816590 := by exact prefixLift 816590
  have htrace : WordTrace (prefixWord ++ tailWord_816590) baseStart_816590 baseEnd_816590 := by
    simpa [prefixWord, tailWord_816590, baseEnd_816590] using wordTrace_append hprefix tailTrace_816590
  have hstable : (prefixWord ++ tailWord_816590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816590).length < 2 ^ (prefixWord ++ tailWord_816590).sum := by decide
  have hdescent : baseEnd_816590 < baseStart_816590 := by decide
  rcases family_descends (prefixWord ++ tailWord_816590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816624 : List Nat := [2, 1, 1, 1, 3, 5, 3, 2, 3]
def baseStart_816624 : Nat := 118140960795 + 816624 * 2 ^ 59
def prefixEnd_816624 : Nat := 4983230072969 + 3 ^ 40 * 816624 * 2
def baseEnd_816624 : Nat := 186364722665474750464187

theorem tailTrace_816624 : CollatzResearch.WordTrace tailWord_816624 prefixEnd_816624 186364722665474750464187 := by
  unfold tailWord_816624
  simp only [CollatzResearch.WordTrace]
  refine ⟨14892362096759095560336463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19856482795678794080448617 14892362096759095560336463)
  ·
    refine ⟨22338543145138643340504695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14892362096759095560336463 22338543145138643340504695)
    ·
      refine ⟨33507814717707965010757043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22338543145138643340504695 33507814717707965010757043)
      ·
        refine ⟨50261722076561947516135565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33507814717707965010757043 50261722076561947516135565)
        ·
          refine ⟨18848145778710730318550837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50261722076561947516135565 18848145778710730318550837)
          ·
            refine ⟨1767013666754130967364141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18848145778710730318550837 1767013666754130967364141)
            ·
              refine ⟨662630125032799112761553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1767013666754130967364141 662630125032799112761553)
              ·
                refine ⟨496972593774599334571165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 662630125032799112761553 496972593774599334571165)
                ·
                  refine ⟨186364722665474750464187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 496972593774599334571165 186364722665474750464187)
                  ·
                    rfl

theorem cell21_816624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 2, 3].length) (baseStart_816624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_816624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_816624 prefixEnd_816624 := by exact prefixLift 816624
  have htrace : WordTrace (prefixWord ++ tailWord_816624) baseStart_816624 baseEnd_816624 := by
    simpa [prefixWord, tailWord_816624, baseEnd_816624] using wordTrace_append hprefix tailTrace_816624
  have hstable : (prefixWord ++ tailWord_816624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816624).length < 2 ^ (prefixWord ++ tailWord_816624).sum := by decide
  have hdescent : baseEnd_816624 < baseStart_816624 := by decide
  rcases family_descends (prefixWord ++ tailWord_816624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816649 : List Nat := [1, 2, 1, 1, 3, 1, 4, 1, 7]
def baseStart_816649 : Nat := 118140960795 + 816649 * 2 ^ 59
def prefixEnd_816649 : Nat := 4983230072969 + 3 ^ 40 * 816649 * 2
def baseEnd_816649 : Nat := 186370428006080262547469

theorem tailTrace_816649 : CollatzResearch.WordTrace tailWord_816649 prefixEnd_816649 186370428006080262547469 := by
  unfold tailWord_816649
  simp only [CollatzResearch.WordTrace]
  refine ⟨29785636018427620390333001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19857090678951746926888667 29785636018427620390333001)
  ·
    refine ⟨22339227013820715292749751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29785636018427620390333001 22339227013820715292749751)
    ·
      refine ⟨33508840520731072939124627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22339227013820715292749751 33508840520731072939124627)
      ·
        refine ⟨50263260781096609408686941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33508840520731072939124627 50263260781096609408686941)
        ·
          refine ⟨18848722792911228528257603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50263260781096609408686941 18848722792911228528257603)
          ·
            refine ⟨28273084189366842792386405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18848722792911228528257603 28273084189366842792386405)
            ·
              refine ⟨5301203285506283023572451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28273084189366842792386405 5301203285506283023572451)
              ·
                refine ⟨7951804928259424535358677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5301203285506283023572451 7951804928259424535358677)
                ·
                  refine ⟨186370428006080262547469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7951804928259424535358677 186370428006080262547469)
                  ·
                    rfl

theorem cell21_816649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 7].length) (baseStart_816649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_816649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_816649 prefixEnd_816649 := by exact prefixLift 816649
  have htrace : WordTrace (prefixWord ++ tailWord_816649) baseStart_816649 baseEnd_816649 := by
    simpa [prefixWord, tailWord_816649, baseEnd_816649] using wordTrace_append hprefix tailTrace_816649
  have hstable : (prefixWord ++ tailWord_816649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816649).length < 2 ^ (prefixWord ++ tailWord_816649).sum := by decide
  have hdescent : baseEnd_816649 < baseStart_816649 := by decide
  rcases family_descends (prefixWord ++ tailWord_816649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816697 : List Nat := [1, 2, 1, 5, 1, 2, 2, 3, 4]
def baseStart_816697 : Nat := 118140960795 + 816697 * 2 ^ 59
def prefixEnd_816697 : Nat := 4983230072969 + 3 ^ 40 * 816697 * 2
def baseEnd_816697 : Nat := 186381382260042845747371

theorem tailTrace_816697 : CollatzResearch.WordTrace tailWord_816697 prefixEnd_816697 186381382260042845747371 := by
  unfold tailWord_816697
  simp only [CollatzResearch.WordTrace]
  refine ⟨29787386722253724588080345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19858257814835816392053563 29787386722253724588080345)
  ·
    refine ⟨22340540041690293441060259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29787386722253724588080345 22340540041690293441060259)
    ·
      refine ⟨33510810062535440161590389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22340540041690293441060259 33510810062535440161590389)
      ·
        refine ⟨3141638443362697515149099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33510810062535440161590389 3141638443362697515149099)
        ·
          refine ⟨4712457665044046272723649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3141638443362697515149099 4712457665044046272723649)
          ·
            refine ⟨3534343248783034704542737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4712457665044046272723649 3534343248783034704542737)
            ·
              refine ⟨2650757436587276028407053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3534343248783034704542737 2650757436587276028407053)
              ·
                refine ⟨994034038720228510652645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2650757436587276028407053 994034038720228510652645)
                ·
                  refine ⟨186381382260042845747371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 994034038720228510652645 186381382260042845747371)
                  ·
                    rfl

theorem cell21_816697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3, 4].length) (baseStart_816697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_816697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_816697 prefixEnd_816697 := by exact prefixLift 816697
  have htrace : WordTrace (prefixWord ++ tailWord_816697) baseStart_816697 baseEnd_816697 := by
    simpa [prefixWord, tailWord_816697, baseEnd_816697] using wordTrace_append hprefix tailTrace_816697
  have hstable : (prefixWord ++ tailWord_816697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816697).length < 2 ^ (prefixWord ++ tailWord_816697).sum := by decide
  have hdescent : baseEnd_816697 < baseStart_816697 := by decide
  rcases family_descends (prefixWord ++ tailWord_816697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816717 : List Nat := [1, 6, 1, 1, 3, 1, 2, 3, 3]
def baseStart_816717 : Nat := 118140960795 + 816717 * 2 ^ 59
def prefixEnd_816717 : Nat := 4983230072969 + 3 ^ 40 * 816717 * 2
def baseEnd_816717 : Nat := 186385946532527255413997

theorem tailTrace_816717 : CollatzResearch.WordTrace tailWord_816717 prefixEnd_816717 186385946532527255413997 := by
  unfold tailWord_816717
  simp only [CollatzResearch.WordTrace]
  refine ⟨29788116182181268003808405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19858744121454178669205603 29788116182181268003808405)
  ·
    refine ⟨1396317946039746937678519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 29788116182181268003808405 1396317946039746937678519)
    ·
      refine ⟨2094476919059620406517779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1396317946039746937678519 2094476919059620406517779)
      ·
        refine ⟨3141715378589430609776669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2094476919059620406517779 3141715378589430609776669)
        ·
          refine ⟨1178143266971036478666251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3141715378589430609776669 1178143266971036478666251)
          ·
            refine ⟨1767214900456554717999377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1178143266971036478666251 1767214900456554717999377)
            ·
              refine ⟨1325411175342416038499533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1767214900456554717999377 1325411175342416038499533)
              ·
                refine ⟨497029190753406014437325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1325411175342416038499533 497029190753406014437325)
                ·
                  refine ⟨186385946532527255413997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 497029190753406014437325 186385946532527255413997)
                  ·
                    rfl

theorem cell21_816717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_816717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_816717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_816717 prefixEnd_816717 := by exact prefixLift 816717
  have htrace : WordTrace (prefixWord ++ tailWord_816717) baseStart_816717 baseEnd_816717 := by
    simpa [prefixWord, tailWord_816717, baseEnd_816717] using wordTrace_append hprefix tailTrace_816717
  have hstable : (prefixWord ++ tailWord_816717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816717).length < 2 ^ (prefixWord ++ tailWord_816717).sum := by decide
  have hdescent : baseEnd_816717 < baseStart_816717 := by decide
  rcases family_descends (prefixWord ++ tailWord_816717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816725 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 9]
def baseStart_816725 : Nat := 118140960795 + 816725 * 2 ^ 59
def prefixEnd_816725 : Nat := 4983230072969 + 3 ^ 40 * 816725 * 2
def baseEnd_816725 : Nat := 186387772241521019280647

theorem tailTrace_816725 : CollatzResearch.WordTrace tailWord_816725 prefixEnd_816725 186387772241521019280647 := by
  unfold tailWord_816725
  simp only [CollatzResearch.WordTrace]
  refine ⟨29788407966152285370099629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19858938644101523580066419 29788407966152285370099629)
  ·
    refine ⟨11170652987307107013787361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29788407966152285370099629 11170652987307107013787361)
    ·
      refine ⟨8377989740480330260340521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11170652987307107013787361 8377989740480330260340521)
      ·
        refine ⟨6283492305360247695255391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8377989740480330260340521 6283492305360247695255391)
        ·
          refine ⟨9425238458040371542883087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6283492305360247695255391 9425238458040371542883087)
          ·
            refine ⟨14137857687060557314324631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9425238458040371542883087 14137857687060557314324631)
            ·
              refine ⟨21206786530590835971486947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14137857687060557314324631 21206786530590835971486947)
              ·
                refine ⟨31810179795886253957230421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21206786530590835971486947 31810179795886253957230421)
                ·
                  refine ⟨186387772241521019280647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31810179795886253957230421 186387772241521019280647)
                  ·
                    rfl

theorem cell21_816725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_816725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_816725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_816725 prefixEnd_816725 := by exact prefixLift 816725
  have htrace : WordTrace (prefixWord ++ tailWord_816725) baseStart_816725 baseEnd_816725 := by
    simpa [prefixWord, tailWord_816725, baseEnd_816725] using wordTrace_append hprefix tailTrace_816725
  have hstable : (prefixWord ++ tailWord_816725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816725).length < 2 ^ (prefixWord ++ tailWord_816725).sum := by decide
  have hdescent : baseEnd_816725 < baseStart_816725 := by decide
  rcases family_descends (prefixWord ++ tailWord_816725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816849 : List Nat := [1, 2, 2, 1, 2, 5, 2, 2, 4]
def baseStart_816849 : Nat := 118140960795 + 816849 * 2 ^ 59
def prefixEnd_816849 : Nat := 4983230072969 + 3 ^ 40 * 816849 * 2
def baseEnd_816849 : Nat := 186416070730924359213727

theorem tailTrace_816849 : CollatzResearch.WordTrace tailWord_816849 prefixEnd_816849 186416070730924359213727 := by
  unfold tailWord_816849
  simp only [CollatzResearch.WordTrace]
  refine ⟨29792930617703054547613601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19861953745135369698409067 29792930617703054547613601)
  ·
    refine ⟨22344697963277290910710201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29792930617703054547613601 22344697963277290910710201)
    ·
      refine ⟨16758523472457968183032651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22344697963277290910710201 16758523472457968183032651)
      ·
        refine ⟨25137785208686952274548977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16758523472457968183032651 25137785208686952274548977)
        ·
          refine ⟨18853338906515214205911733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25137785208686952274548977 18853338906515214205911733)
          ·
            refine ⟨1767500522485801331804225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18853338906515214205911733 1767500522485801331804225)
            ·
              refine ⟨1325625391864350998853169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1767500522485801331804225 1325625391864350998853169)
              ·
                refine ⟨994219043898263249139877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1325625391864350998853169 994219043898263249139877)
                ·
                  refine ⟨186416070730924359213727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 994219043898263249139877 186416070730924359213727)
                  ·
                    rfl

theorem cell21_816849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2, 4].length) (baseStart_816849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_816849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_816849 prefixEnd_816849 := by exact prefixLift 816849
  have htrace : WordTrace (prefixWord ++ tailWord_816849) baseStart_816849 baseEnd_816849 := by
    simpa [prefixWord, tailWord_816849, baseEnd_816849] using wordTrace_append hprefix tailTrace_816849
  have hstable : (prefixWord ++ tailWord_816849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816849).length < 2 ^ (prefixWord ++ tailWord_816849).sum := by decide
  have hdescent : baseEnd_816849 < baseStart_816849 := by decide
  rcases family_descends (prefixWord ++ tailWord_816849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816852 : List Nat := [2, 4, 1, 3, 1, 2, 1, 4, 3]
def baseStart_816852 : Nat := 118140960795 + 816852 * 2 ^ 59
def prefixEnd_816852 : Nat := 4983230072969 + 3 ^ 40 * 816852 * 2
def baseEnd_816852 : Nat := 186416755371797020663721

theorem tailTrace_816852 : CollatzResearch.WordTrace tailWord_816852 prefixEnd_816852 186416755371797020663721 := by
  unfold tailWord_816852
  simp only [CollatzResearch.WordTrace]
  refine ⟨14896520018346093029986405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19862026691128124039981873 14896520018346093029986405)
  ·
    refine ⟨2793097503439892443122451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14896520018346093029986405 2793097503439892443122451)
    ·
      refine ⟨4189646255159838664683677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2793097503439892443122451 4189646255159838664683677)
      ·
        refine ⟨1571117345684939499256379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4189646255159838664683677 1571117345684939499256379)
        ·
          refine ⟨2356676018527409248884569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1571117345684939499256379 2356676018527409248884569)
          ·
            refine ⟨1767507013895556936663427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2356676018527409248884569 1767507013895556936663427)
            ·
              refine ⟨2651260520843335404995141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1767507013895556936663427 2651260520843335404995141)
              ·
                refine ⟨497111347658125388436589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2651260520843335404995141 497111347658125388436589)
                ·
                  refine ⟨186416755371797020663721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 497111347658125388436589 186416755371797020663721)
                  ·
                    rfl

theorem cell21_816852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_816852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_816852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_816852 prefixEnd_816852 := by exact prefixLift 816852
  have htrace : WordTrace (prefixWord ++ tailWord_816852) baseStart_816852 baseEnd_816852 := by
    simpa [prefixWord, tailWord_816852, baseEnd_816852] using wordTrace_append hprefix tailTrace_816852
  have hstable : (prefixWord ++ tailWord_816852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816852).length < 2 ^ (prefixWord ++ tailWord_816852).sum := by decide
  have hdescent : baseEnd_816852 < baseStart_816852 := by decide
  rcases family_descends (prefixWord ++ tailWord_816852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817029 : List Nat := [1, 3, 1, 1, 3, 2, 2, 3, 5]
def baseStart_817029 : Nat := 118140960795 + 817029 * 2 ^ 59
def prefixEnd_817029 : Nat := 4983230072969 + 3 ^ 40 * 817029 * 2
def baseEnd_817029 : Nat := 186457149183284046213359

theorem tailTrace_817029 : CollatzResearch.WordTrace tailWord_817029 prefixEnd_817029 186457149183284046213359 := by
  unfold tailWord_817029
  simp only [CollatzResearch.WordTrace]
  refine ⟨29799495757050945289166141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19866330504700630192777427 29799495757050945289166141)
  ·
    refine ⟨11174810908894104483437303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29799495757050945289166141 11174810908894104483437303)
    ·
      refine ⟨16762216363341156725155955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11174810908894104483437303 16762216363341156725155955)
      ·
        refine ⟨25143324545011735087733933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16762216363341156725155955 25143324545011735087733933)
        ·
          refine ⟨9428746704379400657900225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25143324545011735087733933 9428746704379400657900225)
          ·
            refine ⟨7071560028284550493425169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9428746704379400657900225 7071560028284550493425169)
            ·
              refine ⟨5303670021213412870068877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7071560028284550493425169 5303670021213412870068877)
              ·
                refine ⟨1988876257955029826275829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5303670021213412870068877 1988876257955029826275829)
                ·
                  refine ⟨186457149183284046213359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1988876257955029826275829 186457149183284046213359)
                  ·
                    rfl

theorem cell21_817029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_817029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_817029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_817029 prefixEnd_817029 := by exact prefixLift 817029
  have htrace : WordTrace (prefixWord ++ tailWord_817029) baseStart_817029 baseEnd_817029 := by
    simpa [prefixWord, tailWord_817029, baseEnd_817029] using wordTrace_append hprefix tailTrace_817029
  have hstable : (prefixWord ++ tailWord_817029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817029).length < 2 ^ (prefixWord ++ tailWord_817029).sum := by decide
  have hdescent : baseEnd_817029 < baseStart_817029 := by decide
  rcases family_descends (prefixWord ++ tailWord_817029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817032 : List Nat := [2, 1, 3, 3, 3, 2, 1, 6]
def baseStart_817032 : Nat := 118140960795 + 817032 * 2 ^ 59
def prefixEnd_817032 : Nat := 4983230072969 + 3 ^ 40 * 817032 * 2
def baseEnd_817032 : Nat := 62152611274718902554451

theorem tailTrace_817032 : CollatzResearch.WordTrace tailWord_817032 prefixEnd_817032 62152611274718902554451 := by
  unfold tailWord_817032
  simp only [CollatzResearch.WordTrace]
  refine ⟨14899802588020038400762675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19866403450693384534350233 14899802588020038400762675)
  ·
    refine ⟨22349703882030057601144013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14899802588020038400762675 22349703882030057601144013)
    ·
      refine ⟨8381138955761271600429005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22349703882030057601144013 8381138955761271600429005)
      ·
        refine ⟨3142927108410476850160877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8381138955761271600429005 3142927108410476850160877)
        ·
          refine ⟨1178597665653928818810329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3142927108410476850160877 1178597665653928818810329)
          ·
            refine ⟨883948249240446614107747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1178597665653928818810329 883948249240446614107747)
            ·
              refine ⟨1325922373860669921161621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 883948249240446614107747 1325922373860669921161621)
              ·
                refine ⟨62152611274718902554451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1325922373860669921161621 62152611274718902554451)
                ·
                  rfl

theorem cell21_817032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 6].length) (baseStart_817032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_817032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_817032 prefixEnd_817032 := by exact prefixLift 817032
  have htrace : WordTrace (prefixWord ++ tailWord_817032) baseStart_817032 baseEnd_817032 := by
    simpa [prefixWord, tailWord_817032, baseEnd_817032] using wordTrace_append hprefix tailTrace_817032
  have hstable : (prefixWord ++ tailWord_817032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817032).length < 2 ^ (prefixWord ++ tailWord_817032).sum := by decide
  have hdescent : baseEnd_817032 < baseStart_817032 := by decide
  rcases family_descends (prefixWord ++ tailWord_817032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817063 : List Nat := [1, 1, 6, 1, 2, 1, 1, 5, 3]
def baseStart_817063 : Nat := 118140960795 + 817063 * 2 ^ 59
def prefixEnd_817063 : Nat := 4983230072969 + 3 ^ 40 * 817063 * 2
def baseEnd_817063 : Nat := 186464908446507542646623

theorem tailTrace_817063 : CollatzResearch.WordTrace tailWord_817063 prefixEnd_817063 186464908446507542646623 := by
  unfold tailWord_817063
  simp only [CollatzResearch.WordTrace]
  refine ⟨29800735838927769095903843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19867157225951846063935895 29800735838927769095903843)
  ·
    refine ⟨44701103758391653643855765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29800735838927769095903843 44701103758391653643855765)
    ·
      refine ⟨2095364238674608764555739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44701103758391653643855765 2095364238674608764555739)
      ·
        refine ⟨3143046358011913146833609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2095364238674608764555739 3143046358011913146833609)
        ·
          refine ⟨2357284768508934860125207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3143046358011913146833609 2357284768508934860125207)
          ·
            refine ⟨3535927152763402290187811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2357284768508934860125207 3535927152763402290187811)
            ·
              refine ⟨5303890729145103435281717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3535927152763402290187811 5303890729145103435281717)
              ·
                refine ⟨497239755857353447057661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5303890729145103435281717 497239755857353447057661)
                ·
                  refine ⟨186464908446507542646623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 497239755857353447057661 186464908446507542646623)
                  ·
                    rfl

theorem cell21_817063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 5, 3].length) (baseStart_817063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_817063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_817063 prefixEnd_817063 := by exact prefixLift 817063
  have htrace : WordTrace (prefixWord ++ tailWord_817063) baseStart_817063 baseEnd_817063 := by
    simpa [prefixWord, tailWord_817063, baseEnd_817063] using wordTrace_append hprefix tailTrace_817063
  have hstable : (prefixWord ++ tailWord_817063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817063).length < 2 ^ (prefixWord ++ tailWord_817063).sum := by decide
  have hdescent : baseEnd_817063 < baseStart_817063 := by decide
  rcases family_descends (prefixWord ++ tailWord_817063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817077 : List Nat := [1, 3, 3, 2, 1, 2, 3, 2, 4]
def baseStart_817077 : Nat := 118140960795 + 817077 * 2 ^ 59
def prefixEnd_817077 : Nat := 4983230072969 + 3 ^ 40 * 817077 * 2
def baseEnd_817077 : Nat := 186468103437246629413261

theorem tailTrace_817077 : CollatzResearch.WordTrace tailWord_817077 prefixEnd_817077 186468103437246629413261 := by
  unfold tailWord_817077
  simp only [CollatzResearch.WordTrace]
  refine ⟨29801246460877049486913485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19867497640584699657942323 29801246460877049486913485)
  ·
    refine ⟨11175467422828893557592557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29801246460877049486913485 11175467422828893557592557)
    ·
      refine ⟨4190800283560835084097209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11175467422828893557592557 4190800283560835084097209)
      ·
        refine ⟨3143100212670626313072907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4190800283560835084097209 3143100212670626313072907)
        ·
          refine ⟨4714650319005939469609361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3143100212670626313072907 4714650319005939469609361)
          ·
            refine ⟨3535987739254454602207021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4714650319005939469609361 3535987739254454602207021)
            ·
              refine ⟨1325995402220420475827633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3535987739254454602207021 1325995402220420475827633)
              ·
                refine ⟨994496551665315356870725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1325995402220420475827633 994496551665315356870725)
                ·
                  refine ⟨186468103437246629413261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 994496551665315356870725 186468103437246629413261)
                  ·
                    rfl

theorem cell21_817077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2, 4].length) (baseStart_817077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_817077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_817077 prefixEnd_817077 := by exact prefixLift 817077
  have htrace : WordTrace (prefixWord ++ tailWord_817077) baseStart_817077 baseEnd_817077 := by
    simpa [prefixWord, tailWord_817077, baseEnd_817077] using wordTrace_append hprefix tailTrace_817077
  have hstable : (prefixWord ++ tailWord_817077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817077).length < 2 ^ (prefixWord ++ tailWord_817077).sum := by decide
  have hdescent : baseEnd_817077 < baseStart_817077 := by decide
  rcases family_descends (prefixWord ++ tailWord_817077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817212 : List Nat := [2, 2, 2, 2, 2, 1, 1, 5, 4]
def baseStart_817212 : Nat := 118140960795 + 817212 * 2 ^ 59
def prefixEnd_817212 : Nat := 4983230072969 + 3 ^ 40 * 817212 * 2
def baseEnd_817212 : Nat := 186498912276516394662985

theorem tailTrace_817212 : CollatzResearch.WordTrace tailWord_817212 prefixEnd_817212 186498912276516394662985 := by
  unfold tailWord_817212
  simp only [CollatzResearch.WordTrace]
  refine ⟨14903085157693983771538945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19870780210258645028718593 14903085157693983771538945)
  ·
    refine ⟨11177313868270487828654209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14903085157693983771538945 11177313868270487828654209)
    ·
      refine ⟨8382985401202865871490657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11177313868270487828654209 8382985401202865871490657)
      ·
        refine ⟨6287239050902149403617993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8382985401202865871490657 6287239050902149403617993)
        ·
          refine ⟨4715429288176612052713495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6287239050902149403617993 4715429288176612052713495)
          ·
            refine ⟨7073143932264918079070243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4715429288176612052713495 7073143932264918079070243)
            ·
              refine ⟨10609715898397377118605365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7073143932264918079070243 10609715898397377118605365)
              ·
                refine ⟨994660865474754104869253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10609715898397377118605365 994660865474754104869253)
                ·
                  refine ⟨186498912276516394662985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 994660865474754104869253 186498912276516394662985)
                  ·
                    rfl

theorem cell21_817212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5, 4].length) (baseStart_817212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_817212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_817212 prefixEnd_817212 := by exact prefixLift 817212
  have htrace : WordTrace (prefixWord ++ tailWord_817212) baseStart_817212 baseEnd_817212 := by
    simpa [prefixWord, tailWord_817212, baseEnd_817212] using wordTrace_append hprefix tailTrace_817212
  have hstable : (prefixWord ++ tailWord_817212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817212).length < 2 ^ (prefixWord ++ tailWord_817212).sum := by decide
  have hdescent : baseEnd_817212 < baseStart_817212 := by decide
  rcases family_descends (prefixWord ++ tailWord_817212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817257 : List Nat := [1, 2, 1, 1, 1, 5, 4, 1, 5]
def baseStart_817257 : Nat := 118140960795 + 817257 * 2 ^ 59
def prefixEnd_817257 : Nat := 4983230072969 + 3 ^ 40 * 817257 * 2
def baseEnd_817257 : Nat := 186509181889606316412893

theorem tailTrace_817257 : CollatzResearch.WordTrace tailWord_817257 prefixEnd_817257 186509181889606316412893 := by
  unfold tailWord_817257
  simp only [CollatzResearch.WordTrace]
  refine ⟨29807811600224940228466025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19871874400149960152310683 29807811600224940228466025)
  ·
    refine ⟨22355858700168705171349519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29807811600224940228466025 22355858700168705171349519)
    ·
      refine ⟨33533788050253057757024279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22355858700168705171349519 33533788050253057757024279)
      ·
        refine ⟨50300682075379586635536419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33533788050253057757024279 50300682075379586635536419)
        ·
          refine ⟨75451023113069379953304629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50300682075379586635536419 75451023113069379953304629)
          ·
            refine ⟨7073533416850254370622309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75451023113069379953304629 7073533416850254370622309)
            ·
              refine ⟨1326287515659422694491683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7073533416850254370622309 1326287515659422694491683)
              ·
                refine ⟨1989431273489134041737525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1326287515659422694491683 1989431273489134041737525)
                ·
                  refine ⟨186509181889606316412893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1989431273489134041737525 186509181889606316412893)
                  ·
                    rfl

theorem cell21_817257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 5].length) (baseStart_817257 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_817257 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_817257 prefixEnd_817257 := by exact prefixLift 817257
  have htrace : WordTrace (prefixWord ++ tailWord_817257) baseStart_817257 baseEnd_817257 := by
    simpa [prefixWord, tailWord_817257, baseEnd_817257] using wordTrace_append hprefix tailTrace_817257
  have hstable : (prefixWord ++ tailWord_817257).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817257).length < 2 ^ (prefixWord ++ tailWord_817257).sum := by decide
  have hdescent : baseEnd_817257 < baseStart_817257 := by decide
  rcases family_descends (prefixWord ++ tailWord_817257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817288 : List Nat := [2, 1, 3, 4, 1, 1, 1, 2, 6]
def baseStart_817288 : Nat := 118140960795 + 817288 * 2 ^ 59
def prefixEnd_817288 : Nat := 4983230072969 + 3 ^ 40 * 817288 * 2
def baseEnd_817288 : Nat := 186516256511957151396163

theorem tailTrace_817288 : CollatzResearch.WordTrace tailWord_817288 prefixEnd_817288 186516256511957151396163 := by
  unfold tailWord_817288
  simp only [CollatzResearch.WordTrace]
  refine ⟨14904471131556316261422259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19872628175408421681896345 14904471131556316261422259)
  ·
    refine ⟨22356706697334474392133389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14904471131556316261422259 22356706697334474392133389)
    ·
      refine ⟨8383765011500427897050021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22356706697334474392133389 8383765011500427897050021)
      ·
        refine ⟨1571955939656330230696879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8383765011500427897050021 1571955939656330230696879)
        ·
          refine ⟨2357933909484495346045319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1571955939656330230696879 2357933909484495346045319)
          ·
            refine ⟨3536900864226743019067979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2357933909484495346045319 3536900864226743019067979)
            ·
              refine ⟨5305351296340114528601969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3536900864226743019067979 5305351296340114528601969)
              ·
                refine ⟨3979013472255085896451477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5305351296340114528601969 3979013472255085896451477)
                ·
                  refine ⟨186516256511957151396163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3979013472255085896451477 186516256511957151396163)
                  ·
                    rfl

theorem cell21_817288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 6].length) (baseStart_817288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_817288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_817288 prefixEnd_817288 := by exact prefixLift 817288
  have htrace : WordTrace (prefixWord ++ tailWord_817288) baseStart_817288 baseEnd_817288 := by
    simpa [prefixWord, tailWord_817288, baseEnd_817288] using wordTrace_append hprefix tailTrace_817288
  have hstable : (prefixWord ++ tailWord_817288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817288).length < 2 ^ (prefixWord ++ tailWord_817288).sum := by decide
  have hdescent : baseEnd_817288 < baseStart_817288 := by decide
  rcases family_descends (prefixWord ++ tailWord_817288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817322 : List Nat := [3, 1, 5, 1, 2, 1, 1, 3, 4]
def baseStart_817322 : Nat := 118140960795 + 817322 * 2 ^ 59
def prefixEnd_817322 : Nat := 4983230072969 + 3 ^ 40 * 817322 * 2
def baseEnd_817322 : Nat := 186524015775180647829427

theorem tailTrace_817322 : CollatzResearch.WordTrace tailWord_817322 prefixEnd_817322 186524015775180647829427 := by
  unfold tailWord_817322
  simp only [CollatzResearch.WordTrace]
  refine ⟨7452545586247364082395555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19873454896659637553054813 7452545586247364082395555)
  ·
    refine ⟨11178818379371046123593333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7452545586247364082395555 11178818379371046123593333)
    ·
      refine ⟨1048014223066035574086875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11178818379371046123593333 1048014223066035574086875)
      ·
        refine ⟨1572021334599053361130313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1048014223066035574086875 1572021334599053361130313)
        ·
          refine ⟨1179016000949290020847735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1572021334599053361130313 1179016000949290020847735)
          ·
            refine ⟨1768524001423935031271603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1179016000949290020847735 1768524001423935031271603)
            ·
              refine ⟨2652786002135902546907405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1768524001423935031271603 2652786002135902546907405)
              ·
                refine ⟨994794750800963455090277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2652786002135902546907405 994794750800963455090277)
                ·
                  refine ⟨186524015775180647829427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 994794750800963455090277 186524015775180647829427)
                  ·
                    rfl

theorem cell21_817322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 3, 4].length) (baseStart_817322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_817322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_817322 prefixEnd_817322 := by exact prefixLift 817322
  have htrace : WordTrace (prefixWord ++ tailWord_817322) baseStart_817322 baseEnd_817322 := by
    simpa [prefixWord, tailWord_817322, baseEnd_817322] using wordTrace_append hprefix tailTrace_817322
  have hstable : (prefixWord ++ tailWord_817322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817322).length < 2 ^ (prefixWord ++ tailWord_817322).sum := by decide
  have hdescent : baseEnd_817322 < baseStart_817322 := by decide
  rcases family_descends (prefixWord ++ tailWord_817322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817415 : List Nat := [1, 1, 4, 5, 2, 1, 1, 2, 4]
def baseStart_817415 : Nat := 118140960795 + 817415 * 2 ^ 59
def prefixEnd_817415 : Nat := 4983230072969 + 3 ^ 40 * 817415 * 2
def baseEnd_817415 : Nat := 186545239642233152779237

theorem tailTrace_817415 : CollatzResearch.WordTrace tailWord_817415 prefixEnd_817415 186545239642233152779237 := by
  unfold tailWord_817415
  simp only [CollatzResearch.WordTrace]
  refine ⟨29813574333652533212717699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19875716222435022141811799 29813574333652533212717699)
  ·
    refine ⟨44720361500478799819076549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29813574333652533212717699 44720361500478799819076549)
    ·
      refine ⟨8385067781339774966076853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44720361500478799819076549 8385067781339774966076853)
      ·
        refine ⟨786100104500603903069705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8385067781339774966076853 786100104500603903069705)
        ·
          refine ⟨589575078375452927302279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 786100104500603903069705 589575078375452927302279)
          ·
            refine ⟨884362617563179390953419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589575078375452927302279 884362617563179390953419)
            ·
              refine ⟨1326543926344769086430129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 884362617563179390953419 1326543926344769086430129)
              ·
                refine ⟨994907944758576814822597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1326543926344769086430129 994907944758576814822597)
                ·
                  refine ⟨186545239642233152779237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 994907944758576814822597 186545239642233152779237)
                  ·
                    rfl

theorem cell21_817415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 2, 4].length) (baseStart_817415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_817415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_817415 prefixEnd_817415 := by exact prefixLift 817415
  have htrace : WordTrace (prefixWord ++ tailWord_817415) baseStart_817415 baseEnd_817415 := by
    simpa [prefixWord, tailWord_817415, baseEnd_817415] using wordTrace_append hprefix tailTrace_817415
  have hstable : (prefixWord ++ tailWord_817415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817415).length < 2 ^ (prefixWord ++ tailWord_817415).sum := by decide
  have hdescent : baseEnd_817415 < baseStart_817415 := by decide
  rcases family_descends (prefixWord ++ tailWord_817415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817460 : List Nat := [2, 5, 1, 1, 1, 4, 1, 3, 3]
def baseStart_817460 : Nat := 118140960795 + 817460 * 2 ^ 59
def prefixEnd_817460 : Nat := 4983230072969 + 3 ^ 40 * 817460 * 2
def baseEnd_817460 : Nat := 186555509255323074529145

theorem tailTrace_817460 : CollatzResearch.WordTrace tailWord_817460 prefixEnd_817460 186555509255323074529145 := by
  unfold tailWord_817460
  simp only [CollatzResearch.WordTrace]
  refine ⟨14907607809244752949052917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19876810412326337265403889 14907607809244752949052917)
  ·
    refine ⟨1397588232116695588973711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14907607809244752949052917 1397588232116695588973711)
    ·
      refine ⟨2096382348175043383460567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1397588232116695588973711 2096382348175043383460567)
      ·
        refine ⟨3144573522262565075190851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2096382348175043383460567 3144573522262565075190851)
        ·
          refine ⟨4716860283393847612786277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3144573522262565075190851 4716860283393847612786277)
          ·
            refine ⟨884411303136346427397427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4716860283393847612786277 884411303136346427397427)
            ·
              refine ⟨1326616954704519641096141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 884411303136346427397427 1326616954704519641096141)
              ·
                refine ⟨497481358014194865411053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1326616954704519641096141 497481358014194865411053)
                ·
                  refine ⟨186555509255323074529145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 497481358014194865411053 186555509255323074529145)
                  ·
                    rfl

theorem cell21_817460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_817460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_817460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_817460 prefixEnd_817460 := by exact prefixLift 817460
  have htrace : WordTrace (prefixWord ++ tailWord_817460) baseStart_817460 baseEnd_817460 := by
    simpa [prefixWord, tailWord_817460, baseEnd_817460] using wordTrace_append hprefix tailTrace_817460
  have hstable : (prefixWord ++ tailWord_817460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817460).length < 2 ^ (prefixWord ++ tailWord_817460).sum := by decide
  have hdescent : baseEnd_817460 < baseStart_817460 := by decide
  rcases family_descends (prefixWord ++ tailWord_817460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817513 : List Nat := [1, 2, 1, 1, 1, 3, 3, 9]
def baseStart_817513 : Nat := 118140960795 + 817513 * 2 ^ 59
def prefixEnd_817513 : Nat := 4983230072969 + 3 ^ 40 * 817513 * 2
def baseEnd_817513 : Nat := 62189201525802253381901

theorem tailTrace_817513 : CollatzResearch.WordTrace tailWord_817513 prefixEnd_817513 62189201525802253381901 := by
  unfold tailWord_817513
  simp only [CollatzResearch.WordTrace]
  refine ⟨29817148687297495949785193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19878099124864997299856795 29817148687297495949785193)
  ·
    refine ⟨22362861515473121962338895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29817148687297495949785193 22362861515473121962338895)
    ·
      refine ⟨33544292273209682943508343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22362861515473121962338895 33544292273209682943508343)
      ·
        refine ⟨50316438409814524415262515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33544292273209682943508343 50316438409814524415262515)
        ·
          refine ⟨75474657614721786622893773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50316438409814524415262515 75474657614721786622893773)
          ·
            refine ⟨28302996605520669983585165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75474657614721786622893773 28302996605520669983585165)
            ·
              refine ⟨10613623727070251243844437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28302996605520669983585165 10613623727070251243844437)
              ·
                refine ⟨62189201525802253381901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10613623727070251243844437 62189201525802253381901)
                ·
                  rfl

theorem cell21_817513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 9].length) (baseStart_817513 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_817513 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_817513 prefixEnd_817513 := by exact prefixLift 817513
  have htrace : WordTrace (prefixWord ++ tailWord_817513) baseStart_817513 baseEnd_817513 := by
    simpa [prefixWord, tailWord_817513, baseEnd_817513] using wordTrace_append hprefix tailTrace_817513
  have hstable : (prefixWord ++ tailWord_817513).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817513).length < 2 ^ (prefixWord ++ tailWord_817513).sum := by decide
  have hdescent : baseEnd_817513 < baseStart_817513 := by decide
  rcases family_descends (prefixWord ++ tailWord_817513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817651 : List Nat := [1, 1, 1, 2, 2, 2, 4, 4, 4]
def baseStart_817651 : Nat := 118140960795 + 817651 * 2 ^ 59
def prefixEnd_817651 : Nat := 4983230072969 + 3 ^ 40 * 817651 * 2
def baseEnd_817651 : Nat := 186599098057549186845421

theorem tailTrace_817651 : CollatzResearch.WordTrace tailWord_817651 prefixEnd_817651 186599098057549186845421 := by
  unfold tailWord_817651
  simp only [CollatzResearch.WordTrace]
  refine ⟨29822181960797545518308807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19881454640531697012205871 29822181960797545518308807)
  ·
    refine ⟨44733272941196318277463211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29822181960797545518308807 44733272941196318277463211)
    ·
      refine ⟨67099909411794477416194817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44733272941196318277463211 67099909411794477416194817)
      ·
        refine ⟨50324932058845858062146113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67099909411794477416194817 50324932058845858062146113)
        ·
          refine ⟨37743699044134393546609585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50324932058845858062146113 37743699044134393546609585)
          ·
            refine ⟨28307774283100795159957189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37743699044134393546609585 28307774283100795159957189)
            ·
              refine ⟨5307707678081399092491973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28307774283100795159957189 5307707678081399092491973)
              ·
                refine ⟨995195189640262329842245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5307707678081399092491973 995195189640262329842245)
                ·
                  refine ⟨186599098057549186845421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 995195189640262329842245 186599098057549186845421)
                  ·
                    rfl

theorem cell21_817651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 4].length) (baseStart_817651 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_817651 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_817651 prefixEnd_817651 := by exact prefixLift 817651
  have htrace : WordTrace (prefixWord ++ tailWord_817651) baseStart_817651 baseEnd_817651 := by
    simpa [prefixWord, tailWord_817651, baseEnd_817651] using wordTrace_append hprefix tailTrace_817651
  have hstable : (prefixWord ++ tailWord_817651).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817651).length < 2 ^ (prefixWord ++ tailWord_817651).sum := by decide
  have hdescent : baseEnd_817651 < baseStart_817651 := by decide
  rcases family_descends (prefixWord ++ tailWord_817651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817727 : List Nat := [1, 1, 2, 2, 3, 2, 1, 5, 4]
def baseStart_817727 : Nat := 118140960795 + 817727 * 2 ^ 59
def prefixEnd_817727 : Nat := 4983230072969 + 3 ^ 40 * 817727 * 2
def baseEnd_817727 : Nat := 186616442292989943578599

theorem tailTrace_817727 : CollatzResearch.WordTrace tailWord_817727 prefixEnd_817727 186616442292989943578599 := by
  unfold tailWord_817727
  simp only [CollatzResearch.WordTrace]
  refine ⟨29824953908522210498075435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19883302605681473665383623 29824953908522210498075435)
  ·
    refine ⟨44737430862783315747113153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29824953908522210498075435 44737430862783315747113153)
    ·
      refine ⟨33553073147087486810334865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44737430862783315747113153 33553073147087486810334865)
      ·
        refine ⟨25164804860315615107751149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33553073147087486810334865 25164804860315615107751149)
        ·
          refine ⟨9436801822618355665406681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25164804860315615107751149 9436801822618355665406681)
          ·
            refine ⟨7077601366963766749055011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9436801822618355665406681 7077601366963766749055011)
            ·
              refine ⟨10616402050445650123582517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7077601366963766749055011 10616402050445650123582517)
              ·
                refine ⟨995287692229279699085861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10616402050445650123582517 995287692229279699085861)
                ·
                  refine ⟨186616442292989943578599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 995287692229279699085861 186616442292989943578599)
                  ·
                    rfl

theorem cell21_817727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5, 4].length) (baseStart_817727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_817727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_817727 prefixEnd_817727 := by exact prefixLift 817727
  have htrace : WordTrace (prefixWord ++ tailWord_817727) baseStart_817727 baseEnd_817727 := by
    simpa [prefixWord, tailWord_817727, baseEnd_817727] using wordTrace_append hprefix tailTrace_817727
  have hstable : (prefixWord ++ tailWord_817727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817727).length < 2 ^ (prefixWord ++ tailWord_817727).sum := by decide
  have hdescent : baseEnd_817727 < baseStart_817727 := by decide
  rcases family_descends (prefixWord ++ tailWord_817727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817772 : List Nat := [2, 2, 1, 1, 3, 1, 3, 3, 5]
def baseStart_817772 : Nat := 118140960795 + 817772 * 2 ^ 59
def prefixEnd_817772 : Nat := 4983230072969 + 3 ^ 40 * 817772 * 2
def baseEnd_817772 : Nat := 186626711906079865328507

theorem tailTrace_817772 : CollatzResearch.WordTrace tailWord_817772 prefixEnd_817772 186626711906079865328507 := by
  unfold tailWord_817772
  simp only [CollatzResearch.WordTrace]
  refine ⟨14913297596679591591731785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19884396795572788788975713 14913297596679591591731785)
  ·
    refine ⟨11184973197509693693798839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14913297596679591591731785 11184973197509693693798839)
    ·
      refine ⟨16777459796264540540698259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11184973197509693693798839 16777459796264540540698259)
      ·
        refine ⟨25166189694396810811047389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16777459796264540540698259 25166189694396810811047389)
        ·
          refine ⟨9437321135398804054142771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25166189694396810811047389 9437321135398804054142771)
          ·
            refine ⟨14155981703098206081214157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9437321135398804054142771 14155981703098206081214157)
            ·
              refine ⟨5308493138661827280455309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14155981703098206081214157 5308493138661827280455309)
              ·
                refine ⟨1990684926998185230170741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5308493138661827280455309 1990684926998185230170741)
                ·
                  refine ⟨186626711906079865328507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1990684926998185230170741 186626711906079865328507)
                  ·
                    rfl

theorem cell21_817772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_817772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_817772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_817772 prefixEnd_817772 := by exact prefixLift 817772
  have htrace : WordTrace (prefixWord ++ tailWord_817772) baseStart_817772 baseEnd_817772 := by
    simpa [prefixWord, tailWord_817772, baseEnd_817772] using wordTrace_append hprefix tailTrace_817772
  have hstable : (prefixWord ++ tailWord_817772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817772).length < 2 ^ (prefixWord ++ tailWord_817772).sum := by decide
  have hdescent : baseEnd_817772 < baseStart_817772 := by decide
  rcases family_descends (prefixWord ++ tailWord_817772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817837 : List Nat := [1, 5, 2, 1, 1, 2, 4, 1, 4]
def baseStart_817837 : Nat := 118140960795 + 817837 * 2 ^ 59
def prefixEnd_817837 : Nat := 4983230072969 + 3 ^ 40 * 817837 * 2
def baseEnd_817837 : Nat := 186641545791654196745041

theorem tailTrace_817837 : CollatzResearch.WordTrace tailWord_817837 prefixEnd_817837 186641545791654196745041 := by
  unfold tailWord_817837
  simp only [CollatzResearch.WordTrace]
  refine ⟨29828965938123699284579765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19885977292082466189719843 29828965938123699284579765)
  ·
    refine ⟨2796465556699096807929353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29828965938123699284579765 2796465556699096807929353)
    ·
      refine ⟨2097349167524322605947015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2796465556699096807929353 2097349167524322605947015)
      ·
        refine ⟨3146023751286483908920523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2097349167524322605947015 3146023751286483908920523)
        ·
          refine ⟨4719035626929725863380785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3146023751286483908920523 4719035626929725863380785)
          ·
            refine ⟨3539276720197294397535589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4719035626929725863380785 3539276720197294397535589)
            ·
              refine ⟨663614385036992699537923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3539276720197294397535589 663614385036992699537923)
              ·
                refine ⟨995421577555489049306885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 663614385036992699537923 995421577555489049306885)
                ·
                  refine ⟨186641545791654196745041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 995421577555489049306885 186641545791654196745041)
                  ·
                    rfl

theorem cell21_817837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_817837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_817837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_817837 prefixEnd_817837 := by exact prefixLift 817837
  have htrace : WordTrace (prefixWord ++ tailWord_817837) baseStart_817837 baseEnd_817837 := by
    simpa [prefixWord, tailWord_817837, baseEnd_817837] using wordTrace_append hprefix tailTrace_817837
  have hstable : (prefixWord ++ tailWord_817837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817837).length < 2 ^ (prefixWord ++ tailWord_817837).sum := by decide
  have hdescent : baseEnd_817837 < baseStart_817837 := by decide
  rcases family_descends (prefixWord ++ tailWord_817837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817879 : List Nat := [1, 1, 3, 2, 1, 4, 1, 4, 4]
def baseStart_817879 : Nat := 118140960795 + 817879 * 2 ^ 59
def prefixEnd_817879 : Nat := 4983230072969 + 3 ^ 40 * 817879 * 2
def baseEnd_817879 : Nat := 186651130763871457044955

theorem tailTrace_817879 : CollatzResearch.WordTrace tailWord_817879 prefixEnd_817879 186651130763871457044955 := by
  unfold tailWord_817879
  simp only [CollatzResearch.WordTrace]
  refine ⟨29830497803971540457608691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19886998535981026971739127 29830497803971540457608691)
  ·
    refine ⟨44745746705957310686413037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29830497803971540457608691 44745746705957310686413037)
    ·
      refine ⟨16779655014733991507404889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44745746705957310686413037 16779655014733991507404889)
      ·
        refine ⟨12584741261050493630553667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16779655014733991507404889 12584741261050493630553667)
        ·
          refine ⟨18877111891575740445830501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12584741261050493630553667 18877111891575740445830501)
          ·
            refine ⟨3539458479670451333593219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18877111891575740445830501 3539458479670451333593219)
            ·
              refine ⟨5309187719505677000389829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3539458479670451333593219 5309187719505677000389829)
              ·
                refine ⟨995472697407314437573093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5309187719505677000389829 995472697407314437573093)
                ·
                  refine ⟨186651130763871457044955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 995472697407314437573093 186651130763871457044955)
                  ·
                    rfl

theorem cell21_817879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4, 4].length) (baseStart_817879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_817879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_817879 prefixEnd_817879 := by exact prefixLift 817879
  have htrace : WordTrace (prefixWord ++ tailWord_817879) baseStart_817879 baseEnd_817879 := by
    simpa [prefixWord, tailWord_817879, baseEnd_817879] using wordTrace_append hprefix tailTrace_817879
  have hstable : (prefixWord ++ tailWord_817879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817879).length < 2 ^ (prefixWord ++ tailWord_817879).sum := by decide
  have hdescent : baseEnd_817879 < baseStart_817879 := by decide
  rcases family_descends (prefixWord ++ tailWord_817879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817924 : List Nat := [2, 3, 2, 2, 1, 1, 1, 2, 7]
def baseStart_817924 : Nat := 118140960795 + 817924 * 2 ^ 59
def prefixEnd_817924 : Nat := 4983230072969 + 3 ^ 40 * 817924 * 2
def baseEnd_817924 : Nat := 186661400376961378794863

theorem tailTrace_817924 : CollatzResearch.WordTrace tailWord_817924 prefixEnd_817924 186661400376961378794863 := by
  unfold tailWord_817924
  simp only [CollatzResearch.WordTrace]
  refine ⟨14916069544404256571498413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19888092725872342095331217 14916069544404256571498413)
  ·
    refine ⟨5593526079151596214311905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14916069544404256571498413 5593526079151596214311905)
    ·
      refine ⟨4195144559363697160733929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5593526079151596214311905 4195144559363697160733929)
      ·
        refine ⟨3146358419522772870550447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4195144559363697160733929 3146358419522772870550447)
        ·
          refine ⟨4719537629284159305825671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3146358419522772870550447 4719537629284159305825671)
          ·
            refine ⟨7079306443926238958738507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4719537629284159305825671 7079306443926238958738507)
            ·
              refine ⟨10618959665889358438107761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7079306443926238958738507 10618959665889358438107761)
              ·
                refine ⟨7964219749417018828580821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10618959665889358438107761 7964219749417018828580821)
                ·
                  refine ⟨186661400376961378794863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7964219749417018828580821 186661400376961378794863)
                  ·
                    rfl

theorem cell21_817924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_817924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_817924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_817924 prefixEnd_817924 := by exact prefixLift 817924
  have htrace : WordTrace (prefixWord ++ tailWord_817924) baseStart_817924 baseEnd_817924 := by
    simpa [prefixWord, tailWord_817924, baseEnd_817924] using wordTrace_append hprefix tailTrace_817924
  have hstable : (prefixWord ++ tailWord_817924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817924).length < 2 ^ (prefixWord ++ tailWord_817924).sum := by decide
  have hdescent : baseEnd_817924 < baseStart_817924 := by decide
  rcases family_descends (prefixWord ++ tailWord_817924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817941 : List Nat := [1, 3, 2, 1, 2, 2, 1, 6, 3]
def baseStart_817941 : Nat := 118140960795 + 817941 * 2 ^ 59
def prefixEnd_817941 : Nat := 4983230072969 + 3 ^ 40 * 817941 * 2
def baseEnd_817941 : Nat := 186665280008573127011495

theorem tailTrace_817941 : CollatzResearch.WordTrace tailWord_817941 prefixEnd_817941 186665280008573127011495 := by
  unfold tailWord_817941
  simp only [CollatzResearch.WordTrace]
  refine ⟨29832759129746925046365677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19888506086497950030910451 29832759129746925046365677)
  ·
    refine ⟨11187284673655096892387129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29832759129746925046365677 11187284673655096892387129)
    ·
      refine ⟨8390463505241322669290347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11187284673655096892387129 8390463505241322669290347)
      ·
        refine ⟨12585695257861984003935521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8390463505241322669290347 12585695257861984003935521)
        ·
          refine ⟨9439271443396488002951641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12585695257861984003935521 9439271443396488002951641)
          ·
            refine ⟨7079453582547366002213731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9439271443396488002951641 7079453582547366002213731)
            ·
              refine ⟨10619180373821049003320597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7079453582547366002213731 10619180373821049003320597)
              ·
                refine ⟨497774080022861672030653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10619180373821049003320597 497774080022861672030653)
                ·
                  refine ⟨186665280008573127011495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 497774080022861672030653 186665280008573127011495)
                  ·
                    rfl

theorem cell21_817941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 6, 3].length) (baseStart_817941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_817941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_817941 prefixEnd_817941 := by exact prefixLift 817941
  have htrace : WordTrace (prefixWord ++ tailWord_817941) baseStart_817941 baseEnd_817941 := by
    simpa [prefixWord, tailWord_817941, baseEnd_817941] using wordTrace_append hprefix tailTrace_817941
  have hstable : (prefixWord ++ tailWord_817941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817941).length < 2 ^ (prefixWord ++ tailWord_817941).sum := by decide
  have hdescent : baseEnd_817941 < baseStart_817941 := by decide
  rcases family_descends (prefixWord ++ tailWord_817941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817969 : List Nat := [1, 2, 2, 3, 2, 1, 3, 7]
def baseStart_817969 : Nat := 118140960795 + 817969 * 2 ^ 59
def prefixEnd_817969 : Nat := 4983230072969 + 3 ^ 40 * 817969 * 2
def baseEnd_817969 : Nat := 62223889996683766848257

theorem tailTrace_817969 : CollatzResearch.WordTrace tailWord_817969 prefixEnd_817969 62223889996683766848257 := by
  unfold tailWord_817969
  simp only [CollatzResearch.WordTrace]
  refine ⟨29833780373645485828384961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19889186915763657218923307 29833780373645485828384961)
  ·
    refine ⟨22375335280234114371288721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29833780373645485828384961 22375335280234114371288721)
    ·
      refine ⟨16781501460175585778466541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22375335280234114371288721 16781501460175585778466541)
      ·
        refine ⟨6293063047565844666924953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16781501460175585778466541 6293063047565844666924953)
        ·
          refine ⟨4719797285674383500193715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6293063047565844666924953 4719797285674383500193715)
          ·
            refine ⟨7079695928511575250290573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4719797285674383500193715 7079695928511575250290573)
            ·
              refine ⟨2654885973191840718858965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7079695928511575250290573 2654885973191840718858965)
              ·
                refine ⟨62223889996683766848257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2654885973191840718858965 62223889996683766848257)
                ·
                  rfl

theorem cell21_817969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 7].length) (baseStart_817969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_817969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_817969 prefixEnd_817969 := by exact prefixLift 817969
  have htrace : WordTrace (prefixWord ++ tailWord_817969) baseStart_817969 baseEnd_817969 := by
    simpa [prefixWord, tailWord_817969, baseEnd_817969] using wordTrace_append hprefix tailTrace_817969
  have hstable : (prefixWord ++ tailWord_817969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817969).length < 2 ^ (prefixWord ++ tailWord_817969).sum := by decide
  have hdescent : baseEnd_817969 < baseStart_817969 := by decide
  rcases family_descends (prefixWord ++ tailWord_817969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818000 : List Nat := [2, 1, 1, 1, 1, 4, 5, 1, 5]
def baseStart_818000 : Nat := 118140960795 + 818000 * 2 ^ 59
def prefixEnd_818000 : Nat := 4983230072969 + 3 ^ 40 * 818000 * 2
def baseEnd_818000 : Nat := 186678744612402135528041

theorem tailTrace_818000 : CollatzResearch.WordTrace tailWord_818000 prefixEnd_818000 186678744612402135528041 := by
  unfold tailWord_818000
  simp only [CollatzResearch.WordTrace]
  refine ⟨14917455518266589061381727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19889940691022118748508969 14917455518266589061381727)
  ·
    refine ⟨22376183277399883592072591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14917455518266589061381727 22376183277399883592072591)
    ·
      refine ⟨33564274916099825388108887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22376183277399883592072591 33564274916099825388108887)
      ·
        refine ⟨50346412374149738082163331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33564274916099825388108887 50346412374149738082163331)
        ·
          refine ⟨75519618561224607123244997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50346412374149738082163331 75519618561224607123244997)
          ·
            refine ⟨14159928480229613835608437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75519618561224607123244997 14159928480229613835608437)
            ·
              refine ⟨1327493295021526297088291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14159928480229613835608437 1327493295021526297088291)
              ·
                refine ⟨1991239942532289445632437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1327493295021526297088291 1991239942532289445632437)
                ·
                  refine ⟨186678744612402135528041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1991239942532289445632437 186678744612402135528041)
                  ·
                    rfl

theorem cell21_818000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 5].length) (baseStart_818000 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_818000 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_818000 prefixEnd_818000 := by exact prefixLift 818000
  have htrace : WordTrace (prefixWord ++ tailWord_818000) baseStart_818000 baseEnd_818000 := by
    simpa [prefixWord, tailWord_818000, baseEnd_818000] using wordTrace_append hprefix tailTrace_818000
  have hstable : (prefixWord ++ tailWord_818000).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818000).length < 2 ^ (prefixWord ++ tailWord_818000).sum := by decide
  have hdescent : baseEnd_818000 < baseStart_818000 := by decide
  rcases family_descends (prefixWord ++ tailWord_818000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818124 : List Nat := [2, 2, 1, 4, 1, 1, 5, 1, 4]
def baseStart_818124 : Nat := 118140960795 + 818124 * 2 ^ 59
def prefixEnd_818124 : Nat := 4983230072969 + 3 ^ 40 * 818124 * 2
def baseEnd_818124 : Nat := 186707043101805475461121

theorem tailTrace_818124 : CollatzResearch.WordTrace tailWord_818124 prefixEnd_818124 186707043101805475461121 := by
  unfold tailWord_818124
  simp only [CollatzResearch.WordTrace]
  refine ⟨14919716844041973650138713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19892955792055964866851617 14919716844041973650138713)
  ·
    refine ⟨11189787633031480237604035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14919716844041973650138713 11189787633031480237604035)
    ·
      refine ⟨16784681449547220356406053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11189787633031480237604035 16784681449547220356406053)
      ·
        refine ⟨3147127771790103816826135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16784681449547220356406053 3147127771790103816826135)
        ·
          refine ⟨4720691657685155725239203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3147127771790103816826135 4720691657685155725239203)
          ·
            refine ⟨7081037486527733587858805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4720691657685155725239203 7081037486527733587858805)
            ·
              refine ⟨663847264361975023861763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7081037486527733587858805 663847264361975023861763)
              ·
                refine ⟨995770896542962535792645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 663847264361975023861763 995770896542962535792645)
                ·
                  refine ⟨186707043101805475461121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 995770896542962535792645 186707043101805475461121)
                  ·
                    rfl

theorem cell21_818124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 1, 4].length) (baseStart_818124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_818124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_818124 prefixEnd_818124 := by exact prefixLift 818124
  have htrace : WordTrace (prefixWord ++ tailWord_818124) baseStart_818124 baseEnd_818124 := by
    simpa [prefixWord, tailWord_818124, baseEnd_818124] using wordTrace_append hprefix tailTrace_818124
  have hstable : (prefixWord ++ tailWord_818124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818124).length < 2 ^ (prefixWord ++ tailWord_818124).sum := by decide
  have hdescent : baseEnd_818124 < baseStart_818124 := by decide
  rcases family_descends (prefixWord ++ tailWord_818124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818135 : List Nat := [1, 1, 3, 2, 1, 1, 2, 3, 7]
def baseStart_818135 : Nat := 118140960795 + 818135 * 2 ^ 59
def prefixEnd_818135 : Nat := 4983230072969 + 3 ^ 40 * 818135 * 2
def baseEnd_818135 : Nat := 186709553451671900777765

theorem tailTrace_818135 : CollatzResearch.WordTrace tailWord_818135 prefixEnd_818135 186709553451671900777765 := by
  unfold tailWord_818135
  simp only [CollatzResearch.WordTrace]
  refine ⟨29839834891044096178927859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19893223260696064119285239 29839834891044096178927859)
  ·
    refine ⟨44759752336566144268391789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29839834891044096178927859 44759752336566144268391789)
    ·
      refine ⟨16784907126212304100646921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44759752336566144268391789 16784907126212304100646921)
      ·
        refine ⟨12588680344659228075485191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16784907126212304100646921 12588680344659228075485191)
        ·
          refine ⟨18883020516988842113227787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12588680344659228075485191 18883020516988842113227787)
          ·
            refine ⟨28324530775483263169841681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18883020516988842113227787 28324530775483263169841681)
            ·
              refine ⟨21243398081612447377381261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28324530775483263169841681 21243398081612447377381261)
              ·
                refine ⟨7966274280604667766517973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21243398081612447377381261 7966274280604667766517973)
                ·
                  refine ⟨186709553451671900777765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7966274280604667766517973 186709553451671900777765)
                  ·
                    rfl

theorem cell21_818135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 7].length) (baseStart_818135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_818135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_818135 prefixEnd_818135 := by exact prefixLift 818135
  have htrace : WordTrace (prefixWord ++ tailWord_818135) baseStart_818135 baseEnd_818135 := by
    simpa [prefixWord, tailWord_818135, baseEnd_818135] using wordTrace_append hprefix tailTrace_818135
  have hstable : (prefixWord ++ tailWord_818135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818135).length < 2 ^ (prefixWord ++ tailWord_818135).sum := by decide
  have hdescent : baseEnd_818135 < baseStart_818135 := by decide
  rcases family_descends (prefixWord ++ tailWord_818135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818138 : List Nat := [3, 1, 1, 2, 4, 1, 4, 5]
def baseStart_818138 : Nat := 118140960795 + 818138 * 2 ^ 59
def prefixEnd_818138 : Nat := 4983230072969 + 3 ^ 40 * 818138 * 2
def baseEnd_818138 : Nat := 62236746030848187409253

theorem tailTrace_818138 : CollatzResearch.WordTrace tailWord_818138 prefixEnd_818138 62236746030848187409253 := by
  unfold tailWord_818138
  simp only [CollatzResearch.WordTrace]
  refine ⟨7459986077508306922821767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19893296206688818460858045 7459986077508306922821767)
  ·
    refine ⟨11189979116262460384232651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7459986077508306922821767 11189979116262460384232651)
    ·
      refine ⟨16784968674393690576348977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11189979116262460384232651 16784968674393690576348977)
      ·
        refine ⟨12588726505795267932261733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16784968674393690576348977 12588726505795267932261733)
        ·
          refine ⟨2360386219836612737299075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12588726505795267932261733 2360386219836612737299075)
          ·
            refine ⟨3540579329754919105948613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2360386219836612737299075 3540579329754919105948613)
            ·
              refine ⟨663858624329047332365365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3540579329754919105948613 663858624329047332365365)
              ·
                refine ⟨62236746030848187409253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 663858624329047332365365 62236746030848187409253)
                ·
                  rfl

theorem cell21_818138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 5].length) (baseStart_818138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_818138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_818138 prefixEnd_818138 := by exact prefixLift 818138
  have htrace : WordTrace (prefixWord ++ tailWord_818138) baseStart_818138 baseEnd_818138 := by
    simpa [prefixWord, tailWord_818138, baseEnd_818138] using wordTrace_append hprefix tailTrace_818138
  have hstable : (prefixWord ++ tailWord_818138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818138).length < 2 ^ (prefixWord ++ tailWord_818138).sum := by decide
  have hdescent : baseEnd_818138 < baseStart_818138 := by decide
  rcases family_descends (prefixWord ++ tailWord_818138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818183 : List Nat := [1, 1, 4, 3, 1, 1, 3, 3, 4]
def baseStart_818183 : Nat := 118140960795 + 818183 * 2 ^ 59
def prefixEnd_818183 : Nat := 4983230072969 + 3 ^ 40 * 818183 * 2
def baseEnd_818183 : Nat := 186720507705634483977667

theorem tailTrace_818183 : CollatzResearch.WordTrace tailWord_818183 prefixEnd_818183 186720507705634483977667 := by
  unfold tailWord_818183
  simp only [CollatzResearch.WordTrace]
  refine ⟨29841585594870200376675203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19894390396580133584450135 29841585594870200376675203)
  ·
    refine ⟨44762378392305300565012805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29841585594870200376675203 44762378392305300565012805)
    ·
      refine ⟨8392945948557243855939901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44762378392305300565012805 8392945948557243855939901)
      ·
        refine ⟨3147354730708966445977463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8392945948557243855939901 3147354730708966445977463)
        ·
          refine ⟨4721032096063449668966195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3147354730708966445977463 4721032096063449668966195)
          ·
            refine ⟨7081548144095174503449293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4721032096063449668966195 7081548144095174503449293)
            ·
              refine ⟨2655580554035690438793485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7081548144095174503449293 2655580554035690438793485)
              ·
                refine ⟨995842707763383914547557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2655580554035690438793485 995842707763383914547557)
                ·
                  refine ⟨186720507705634483977667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 995842707763383914547557 186720507705634483977667)
                  ·
                    rfl

theorem cell21_818183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3, 4].length) (baseStart_818183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_818183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_818183 prefixEnd_818183 := by exact prefixLift 818183
  have htrace : WordTrace (prefixWord ++ tailWord_818183) baseStart_818183 baseEnd_818183 := by
    simpa [prefixWord, tailWord_818183, baseEnd_818183] using wordTrace_append hprefix tailTrace_818183
  have hstable : (prefixWord ++ tailWord_818183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818183).length < 2 ^ (prefixWord ++ tailWord_818183).sum := by decide
  have hdescent : baseEnd_818183 < baseStart_818183 := by decide
  rcases family_descends (prefixWord ++ tailWord_818183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818197 : List Nat := [1, 3, 2, 1, 4, 1, 2, 7]
def baseStart_818197 : Nat := 118140960795 + 818197 * 2 ^ 59
def prefixEnd_818197 : Nat := 4983230072969 + 3 ^ 40 * 818197 * 2
def baseEnd_818197 : Nat := 62241234232124523581435

theorem tailTrace_818197 : CollatzResearch.WordTrace tailWord_818197 prefixEnd_818197 62241234232124523581435 := by
  unfold tailWord_818197
  simp only [CollatzResearch.WordTrace]
  refine ⟨29842096216819480767684845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19894730811212987178456563 29842096216819480767684845)
  ·
    refine ⟨11190786081307305287881817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29842096216819480767684845 11190786081307305287881817)
    ·
      refine ⟨8393089560980478965911363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11190786081307305287881817 8393089560980478965911363)
      ·
        refine ⟨12589634341470718448867045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8393089560980478965911363 12589634341470718448867045)
        ·
          refine ⟨2360556439025759709162571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12589634341470718448867045 2360556439025759709162571)
          ·
            refine ⟨3540834658538639563743857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2360556439025759709162571 3540834658538639563743857)
            ·
              refine ⟨2655625993903979672807893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3540834658538639563743857 2655625993903979672807893)
              ·
                refine ⟨62241234232124523581435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2655625993903979672807893 62241234232124523581435)
                ·
                  rfl

theorem cell21_818197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 7].length) (baseStart_818197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_818197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_818197 prefixEnd_818197 := by exact prefixLift 818197
  have htrace : WordTrace (prefixWord ++ tailWord_818197) baseStart_818197 baseEnd_818197 := by
    simpa [prefixWord, tailWord_818197, baseEnd_818197] using wordTrace_append hprefix tailTrace_818197
  have hstable : (prefixWord ++ tailWord_818197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818197).length < 2 ^ (prefixWord ++ tailWord_818197).sum := by decide
  have hdescent : baseEnd_818197 < baseStart_818197 := by decide
  rcases family_descends (prefixWord ++ tailWord_818197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818256 : List Nat := [2, 1, 1, 1, 1, 3, 1, 11]
def baseStart_818256 : Nat := 118140960795 + 818256 * 2 ^ 59
def prefixEnd_818256 : Nat := 4983230072969 + 3 ^ 40 * 818256 * 2
def baseEnd_818256 : Nat := 62245722433400859753617

theorem tailTrace_818256 : CollatzResearch.WordTrace tailWord_818256 prefixEnd_818256 62245722433400859753617 := by
  unfold tailWord_818256
  simp only [CollatzResearch.WordTrace]
  refine ⟨14922124061802866922041311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19896165415737155896055081 14922124061802866922041311)
  ·
    refine ⟨22383186092704300383061967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14922124061802866922041311 22383186092704300383061967)
    ·
      refine ⟨33574779139056450574592951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22383186092704300383061967 33574779139056450574592951)
      ·
        refine ⟨50362168708584675861889427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33574779139056450574592951 50362168708584675861889427)
        ·
          refine ⟨75543253062877013792834141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50362168708584675861889427 75543253062877013792834141)
          ·
            refine ⟨28328719898578880172312803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75543253062877013792834141 28328719898578880172312803)
            ·
              refine ⟨42493079847868320258469205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28328719898578880172312803 42493079847868320258469205)
              ·
                refine ⟨62245722433400859753617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 42493079847868320258469205 62245722433400859753617)
                ·
                  rfl

theorem cell21_818256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 11].length) (baseStart_818256 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_818256 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_818256 prefixEnd_818256 := by exact prefixLift 818256
  have htrace : WordTrace (prefixWord ++ tailWord_818256) baseStart_818256 baseEnd_818256 := by
    simpa [prefixWord, tailWord_818256, baseEnd_818256] using wordTrace_append hprefix tailTrace_818256
  have hstable : (prefixWord ++ tailWord_818256).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818256).length < 2 ^ (prefixWord ++ tailWord_818256).sum := by decide
  have hdescent : baseEnd_818256 < baseStart_818256 := by decide
  rcases family_descends (prefixWord ++ tailWord_818256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818338 : List Nat := [3, 3, 1, 3, 2, 2, 1, 1, 5]
def baseStart_818338 : Nat := 118140960795 + 818338 * 2 ^ 59
def prefixEnd_818338 : Nat := 4983230072969 + 3 ^ 40 * 818338 * 2
def baseEnd_818338 : Nat := 186755880817388658894017

theorem tailTrace_818338 : CollatzResearch.WordTrace tailWord_818338 prefixEnd_818338 186755880817388658894017 := by
  unfold tailWord_818338
  simp only [CollatzResearch.WordTrace]
  refine ⟨7461809727327165462141917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19898159272872441232378445 7461809727327165462141917)
  ·
    refine ⟨2798178647747687048303219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7461809727327165462141917 2798178647747687048303219)
    ·
      refine ⟨4197267971621530572454829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2798178647747687048303219 4197267971621530572454829)
      ·
        refine ⟨1573975489358073964670561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4197267971621530572454829 1573975489358073964670561)
        ·
          refine ⟨1180481617018555473502921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1573975489358073964670561 1180481617018555473502921)
          ·
            refine ⟨885361212763916605127191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1180481617018555473502921 885361212763916605127191)
            ·
              refine ⟨1328041819145874907690787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 885361212763916605127191 1328041819145874907690787)
              ·
                refine ⟨1992062728718812361536181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1328041819145874907690787 1992062728718812361536181)
                ·
                  refine ⟨186755880817388658894017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1992062728718812361536181 186755880817388658894017)
                  ·
                    rfl

theorem cell21_818338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_818338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_818338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_818338 prefixEnd_818338 := by exact prefixLift 818338
  have htrace : WordTrace (prefixWord ++ tailWord_818338) baseStart_818338 baseEnd_818338 := by
    simpa [prefixWord, tailWord_818338, baseEnd_818338] using wordTrace_append hprefix tailTrace_818338
  have hstable : (prefixWord ++ tailWord_818338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818338).length < 2 ^ (prefixWord ++ tailWord_818338).sum := by decide
  have hdescent : baseEnd_818338 < baseStart_818338 := by decide
  rcases family_descends (prefixWord ++ tailWord_818338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818425 : List Nat := [1, 2, 1, 3, 1, 1, 7, 5]
def baseStart_818425 : Nat := 118140960795 + 818425 * 2 ^ 59
def prefixEnd_818425 : Nat := 4983230072969 + 3 ^ 40 * 818425 * 2
def baseEnd_818425 : Nat := 62258578467565280314613

theorem tailTrace_818425 : CollatzResearch.WordTrace tailWord_818425 prefixEnd_818425 62258578467565280314613 := by
  unfold tailWord_818425
  simp only [CollatzResearch.WordTrace]
  refine ⟨29850412059993475706984729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19900274706662317137989819 29850412059993475706984729)
  ·
    refine ⟨22387809044995106780238547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29850412059993475706984729 22387809044995106780238547)
    ·
      refine ⟨33581713567492660170357821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22387809044995106780238547 33581713567492660170357821)
      ·
        refine ⟨12593142587809747563884183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33581713567492660170357821 12593142587809747563884183)
        ·
          refine ⟨18889713881714621345826275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12593142587809747563884183 18889713881714621345826275)
          ·
            refine ⟨28334570822571932018739413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18889713881714621345826275 28334570822571932018739413)
            ·
              refine ⟨664091503654029656689205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 28334570822571932018739413 664091503654029656689205)
              ·
                refine ⟨62258578467565280314613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 664091503654029656689205 62258578467565280314613)
                ·
                  rfl

theorem cell21_818425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 5].length) (baseStart_818425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_818425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_818425 prefixEnd_818425 := by exact prefixLift 818425
  have htrace : WordTrace (prefixWord ++ tailWord_818425) baseStart_818425 baseEnd_818425 := by
    simpa [prefixWord, tailWord_818425, baseEnd_818425] using wordTrace_append hprefix tailTrace_818425
  have hstable : (prefixWord ++ tailWord_818425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818425).length < 2 ^ (prefixWord ++ tailWord_818425).sum := by decide
  have hdescent : baseEnd_818425 < baseStart_818425 := by decide
  rcases family_descends (prefixWord ++ tailWord_818425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818456 : List Nat := [2, 1, 2, 3, 1, 4, 2, 1, 5]
def baseStart_818456 : Nat := 118140960795 + 818456 * 2 ^ 59
def prefixEnd_818456 : Nat := 4983230072969 + 3 ^ 40 * 818456 * 2
def baseEnd_818456 : Nat := 186782810025046675927109

theorem tailTrace_818456 : CollatzResearch.WordTrace tailWord_818456 prefixEnd_818456 186782810025046675927109 := by
  unfold tailWord_818456
  simp only [CollatzResearch.WordTrace]
  refine ⟨14925771361440584000681611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19901028481920778667575481 14925771361440584000681611)
  ·
    refine ⟨22388657042160876001022417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14925771361440584000681611 22388657042160876001022417)
    ·
      refine ⟨16791492781620657000766813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22388657042160876001022417 16791492781620657000766813)
      ·
        refine ⟨6296809793107746375287555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16791492781620657000766813 6296809793107746375287555)
        ·
          refine ⟨9445214689661619562931333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6296809793107746375287555 9445214689661619562931333)
          ·
            refine ⟨1770977754311553668049625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9445214689661619562931333 1770977754311553668049625)
            ·
              refine ⟨1328233315733665251037219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1770977754311553668049625 1328233315733665251037219)
              ·
                refine ⟨1992349973600497876555829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1328233315733665251037219 1992349973600497876555829)
                ·
                  refine ⟨186782810025046675927109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1992349973600497876555829 186782810025046675927109)
                  ·
                    rfl

theorem cell21_818456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 5].length) (baseStart_818456 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_818456 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_818456 prefixEnd_818456 := by exact prefixLift 818456
  have htrace : WordTrace (prefixWord ++ tailWord_818456) baseStart_818456 baseEnd_818456 := by
    simpa [prefixWord, tailWord_818456, baseEnd_818456] using wordTrace_append hprefix tailTrace_818456
  have hstable : (prefixWord ++ tailWord_818456).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818456).length < 2 ^ (prefixWord ++ tailWord_818456).sum := by decide
  have hdescent : baseEnd_818456 < baseStart_818456 := by decide
  rcases family_descends (prefixWord ++ tailWord_818456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818462 : List Nat := [4, 3, 2, 1, 2, 1, 3, 1, 4]
def baseStart_818462 : Nat := 118140960795 + 818462 * 2 ^ 59
def prefixEnd_818462 : Nat := 4983230072969 + 3 ^ 40 * 818462 * 2
def baseEnd_818462 : Nat := 186784179306791998827097

theorem tailTrace_818462 : CollatzResearch.WordTrace tailWord_818462 prefixEnd_818462 186784179306791998827097 := by
  unfold tailWord_818462
  simp only [CollatzResearch.WordTrace]
  refine ⟨3731470195107428878260205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19901174373906287350721093 3731470195107428878260205)
  ·
    refine ⟨1399301323165285829347577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3731470195107428878260205 1399301323165285829347577)
    ·
      refine ⟨1049475992373964372010683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1399301323165285829347577 1049475992373964372010683)
      ·
        refine ⟨1574213988560946558016025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1049475992373964372010683 1574213988560946558016025)
        ·
          refine ⟨1180660491420709918512019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1574213988560946558016025 1180660491420709918512019)
          ·
            refine ⟨1770990737131064877768029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1180660491420709918512019 1770990737131064877768029)
            ·
              refine ⟨664121526424149329163011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1770990737131064877768029 664121526424149329163011)
              ·
                refine ⟨996182289636223993744517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 664121526424149329163011 996182289636223993744517)
                ·
                  refine ⟨186784179306791998827097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 996182289636223993744517 186784179306791998827097)
                  ·
                    rfl

theorem cell21_818462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_818462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_818462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_818462 prefixEnd_818462 := by exact prefixLift 818462
  have htrace : WordTrace (prefixWord ++ tailWord_818462) baseStart_818462 baseEnd_818462 := by
    simpa [prefixWord, tailWord_818462, baseEnd_818462] using wordTrace_append hprefix tailTrace_818462
  have hstable : (prefixWord ++ tailWord_818462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818462).length < 2 ^ (prefixWord ++ tailWord_818462).sum := by decide
  have hdescent : baseEnd_818462 < baseStart_818462 := by decide
  rcases family_descends (prefixWord ++ tailWord_818462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818563 : List Nat := [1, 1, 1, 3, 5, 2, 2, 2, 4]
def baseStart_818563 : Nat := 118140960795 + 818563 * 2 ^ 59
def prefixEnd_818563 : Nat := 4983230072969 + 3 ^ 40 * 818563 * 2
def baseEnd_818563 : Nat := 186807228882838267643557

theorem tailTrace_818563 : CollatzResearch.WordTrace tailWord_818563 prefixEnd_818563 186807228882838267643557 := by
  unfold tailWord_818563
  simp only [CollatzResearch.WordTrace]
  refine ⟨29855445333493525275508343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19903630222329016850338895 29855445333493525275508343)
  ·
    refine ⟨44783168000240287913262515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29855445333493525275508343 44783168000240287913262515)
    ·
      refine ⟨67174752000360431869893773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44783168000240287913262515 67174752000360431869893773)
      ·
        refine ⟨25190532000135161951210165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67174752000360431869893773 25190532000135161951210165)
        ·
          refine ⟨2361612375012671432925953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25190532000135161951210165 2361612375012671432925953)
          ·
            refine ⟨1771209281259503574694465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2361612375012671432925953 1771209281259503574694465)
            ·
              refine ⟨1328406960944627681020849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1771209281259503574694465 1328406960944627681020849)
              ·
                refine ⟨996305220708470760765637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1328406960944627681020849 996305220708470760765637)
                ·
                  refine ⟨186807228882838267643557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 996305220708470760765637 186807228882838267643557)
                  ·
                    rfl

theorem cell21_818563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2, 4].length) (baseStart_818563 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_818563 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_818563 prefixEnd_818563 := by exact prefixLift 818563
  have htrace : WordTrace (prefixWord ++ tailWord_818563) baseStart_818563 baseEnd_818563 := by
    simpa [prefixWord, tailWord_818563, baseEnd_818563] using wordTrace_append hprefix tailTrace_818563
  have hstable : (prefixWord ++ tailWord_818563).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818563).length < 2 ^ (prefixWord ++ tailWord_818563).sum := by decide
  have hdescent : baseEnd_818563 < baseStart_818563 := by decide
  rcases family_descends (prefixWord ++ tailWord_818563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818591 : List Nat := [1, 1, 2, 5, 1, 2, 1, 1, 7]
def baseStart_818591 : Nat := 118140960795 + 818591 * 2 ^ 59
def prefixEnd_818591 : Nat := 4983230072969 + 3 ^ 40 * 818591 * 2
def baseEnd_818591 : Nat := 186813618864316441176833

theorem tailTrace_818591 : CollatzResearch.WordTrace tailWord_818591 prefixEnd_818591 186813618864316441176833 := by
  unfold tailWord_818591
  simp only [CollatzResearch.WordTrace]
  refine ⟨29856466577392086057527627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19904311051594724038351751 29856466577392086057527627)
  ·
    refine ⟨44784699866088129086291441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29856466577392086057527627 44784699866088129086291441)
    ·
      refine ⟨33588524899566096814718581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44784699866088129086291441 33588524899566096814718581)
      ·
        refine ⟨3148924209334321576379867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33588524899566096814718581 3148924209334321576379867)
        ·
          refine ⟨4723386314001482364569801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3148924209334321576379867 4723386314001482364569801)
          ·
            refine ⟨3542539735501111773427351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4723386314001482364569801 3542539735501111773427351)
            ·
              refine ⟨5313809603251667660141027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3542539735501111773427351 5313809603251667660141027)
              ·
                refine ⟨7970714404877501490211541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5313809603251667660141027 7970714404877501490211541)
                ·
                  refine ⟨186813618864316441176833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7970714404877501490211541 186813618864316441176833)
                  ·
                    rfl

theorem cell21_818591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 7].length) (baseStart_818591 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_818591 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_818591 prefixEnd_818591 := by exact prefixLift 818591
  have htrace : WordTrace (prefixWord ++ tailWord_818591) baseStart_818591 baseEnd_818591 := by
    simpa [prefixWord, tailWord_818591, baseEnd_818591] using wordTrace_append hprefix tailTrace_818591
  have hstable : (prefixWord ++ tailWord_818591).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818591).length < 2 ^ (prefixWord ++ tailWord_818591).sum := by decide
  have hdescent : baseEnd_818591 < baseStart_818591 := by decide
  rcases family_descends (prefixWord ++ tailWord_818591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818594 : List Nat := [3, 3, 1, 2, 1, 3, 3, 5]
def baseStart_818594 : Nat := 118140960795 + 818594 * 2 ^ 59
def prefixEnd_818594 : Nat := 4983230072969 + 3 ^ 40 * 818594 * 2
def baseEnd_818594 : Nat := 62271434501729700875609

theorem tailTrace_818594 : CollatzResearch.WordTrace tailWord_818594 prefixEnd_818594 62271434501729700875609 := by
  unfold tailWord_818594
  simp only [CollatzResearch.WordTrace]
  refine ⟨7464143999095304392471709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19904383997587478379924557 7464143999095304392471709)
  ·
    refine ⟨2799053999660739147176891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7464143999095304392471709 2799053999660739147176891)
    ·
      refine ⟨4198580999491108720765337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2799053999660739147176891 4198580999491108720765337)
      ·
        refine ⟨3148935749618331540574003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4198580999491108720765337 3148935749618331540574003)
        ·
          refine ⟨4723403624427497310861005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3148935749618331540574003 4723403624427497310861005)
          ·
            refine ⟨1771276359160311491572877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4723403624427497310861005 1771276359160311491572877)
            ·
              refine ⟨664228634685116809339829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1771276359160311491572877 664228634685116809339829)
              ·
                refine ⟨62271434501729700875609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 664228634685116809339829 62271434501729700875609)
                ·
                  rfl

theorem cell21_818594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 5].length) (baseStart_818594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_818594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_818594 prefixEnd_818594 := by exact prefixLift 818594
  have htrace : WordTrace (prefixWord ++ tailWord_818594) baseStart_818594 baseEnd_818594 := by
    simpa [prefixWord, tailWord_818594, baseEnd_818594] using wordTrace_append hprefix tailTrace_818594
  have hstable : (prefixWord ++ tailWord_818594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818594).length < 2 ^ (prefixWord ++ tailWord_818594).sum := by decide
  have hdescent : baseEnd_818594 < baseStart_818594 := by decide
  rcases family_descends (prefixWord ++ tailWord_818594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818653 : List Nat := [1, 4, 3, 1, 1, 3, 1, 7]
def baseStart_818653 : Nat := 118140960795 + 818653 * 2 ^ 59
def prefixEnd_818653 : Nat := 4983230072969 + 3 ^ 40 * 818653 * 2
def baseEnd_818653 : Nat := 62275922703006037047791

theorem tailTrace_818653 : CollatzResearch.WordTrace tailWord_818653 prefixEnd_818653 62275922703006037047791 := by
  unfold tailWord_818653
  simp only [CollatzResearch.WordTrace]
  refine ⟨29858727903167470646284613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19905818602111647097523075 29858727903167470646284613)
  ·
    refine ⟨5598511481843900746178365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29858727903167470646284613 5598511481843900746178365)
    ·
      refine ⟨2099441805691462779816887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5598511481843900746178365 2099441805691462779816887)
      ·
        refine ⟨3149162708537194169725331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2099441805691462779816887 3149162708537194169725331)
        ·
          refine ⟨4723744062805791254587997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3149162708537194169725331 4723744062805791254587997)
          ·
            refine ⟨1771404023552171720470499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4723744062805791254587997 1771404023552171720470499)
            ·
              refine ⟨2657106035328257580705749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1771404023552171720470499 2657106035328257580705749)
              ·
                refine ⟨62275922703006037047791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2657106035328257580705749 62275922703006037047791)
                ·
                  rfl

theorem cell21_818653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 7].length) (baseStart_818653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_818653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_818653 prefixEnd_818653 := by exact prefixLift 818653
  have htrace : WordTrace (prefixWord ++ tailWord_818653) baseStart_818653 baseEnd_818653 := by
    simpa [prefixWord, tailWord_818653, baseEnd_818653] using wordTrace_append hprefix tailTrace_818653
  have hstable : (prefixWord ++ tailWord_818653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818653).length < 2 ^ (prefixWord ++ tailWord_818653).sum := by decide
  have hdescent : baseEnd_818653 < baseStart_818653 := by decide
  rcases family_descends (prefixWord ++ tailWord_818653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818684 : List Nat := [2, 2, 2, 1, 2, 1, 2, 6, 3]
def baseStart_818684 : Nat := 118140960795 + 818684 * 2 ^ 59
def prefixEnd_818684 : Nat := 4983230072969 + 3 ^ 40 * 818684 * 2
def baseEnd_818684 : Nat := 186834842731368946126643

theorem tailTrace_818684 : CollatzResearch.WordTrace tailWord_818684 prefixEnd_818684 186834842731368946126643 := by
  unfold tailWord_818684
  simp only [CollatzResearch.WordTrace]
  refine ⟨14929929283027581470331553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19906572377370108627108737 14929929283027581470331553)
  ·
    refine ⟨11197446962270686102748665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14929929283027581470331553 11197446962270686102748665)
    ·
      refine ⟨8398085221703014577061499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11197446962270686102748665 8398085221703014577061499)
      ·
        refine ⟨12597127832554521865592249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8398085221703014577061499 12597127832554521865592249)
        ·
          refine ⟨9447845874415891399194187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12597127832554521865592249 9447845874415891399194187)
          ·
            refine ⟨14171768811623837098791281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9447845874415891399194187 14171768811623837098791281)
            ·
              refine ⟨10628826608717877824093461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14171768811623837098791281 10628826608717877824093461)
              ·
                refine ⟨498226247283650523004381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10628826608717877824093461 498226247283650523004381)
                ·
                  refine ⟨186834842731368946126643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 498226247283650523004381 186834842731368946126643)
                  ·
                    rfl

theorem cell21_818684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 6, 3].length) (baseStart_818684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_818684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_818684 prefixEnd_818684 := by exact prefixLift 818684
  have htrace : WordTrace (prefixWord ++ tailWord_818684) baseStart_818684 baseEnd_818684 := by
    simpa [prefixWord, tailWord_818684, baseEnd_818684] using wordTrace_append hprefix tailTrace_818684
  have hstable : (prefixWord ++ tailWord_818684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818684).length < 2 ^ (prefixWord ++ tailWord_818684).sum := by decide
  have hdescent : baseEnd_818684 < baseStart_818684 := by decide
  rcases family_descends (prefixWord ++ tailWord_818684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818788 : List Nat := [2, 3, 1, 1, 2, 4, 8]
def baseStart_818788 : Nat := 118140960795 + 818788 * 2 ^ 59
def prefixEnd_818788 : Nat := 4983230072969 + 3 ^ 40 * 818788 * 2
def baseEnd_818788 : Nat := 20762064105365319599233

theorem tailTrace_818788 : CollatzResearch.WordTrace tailWord_818788 prefixEnd_818788 20762064105365319599233 := by
  unfold tailWord_818788
  simp only [CollatzResearch.WordTrace]
  refine ⟨14931825878839194351224509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19909101171785592468299345 14931825878839194351224509)
  ·
    refine ⟨5599434704564697881709191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14931825878839194351224509 5599434704564697881709191)
    ·
      refine ⟨8399152056847046822563787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5599434704564697881709191 8399152056847046822563787)
      ·
        refine ⟨12598728085270570233845681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8399152056847046822563787 12598728085270570233845681)
        ·
          refine ⟨9449046063952927675384261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12598728085270570233845681 9449046063952927675384261)
          ·
            refine ⟨1771696136991173939134549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9449046063952927675384261 1771696136991173939134549)
            ·
              refine ⟨20762064105365319599233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1771696136991173939134549 20762064105365319599233)
              ·
                rfl

theorem cell21_818788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 8].length) (baseStart_818788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_818788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_818788 prefixEnd_818788 := by exact prefixLift 818788
  have htrace : WordTrace (prefixWord ++ tailWord_818788) baseStart_818788 baseEnd_818788 := by
    simpa [prefixWord, tailWord_818788, baseEnd_818788] using wordTrace_append hprefix tailTrace_818788
  have hstable : (prefixWord ++ tailWord_818788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818788).length < 2 ^ (prefixWord ++ tailWord_818788).sum := by decide
  have hdescent : baseEnd_818788 < baseStart_818788 := by decide
  rcases family_descends (prefixWord ++ tailWord_818788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818926 : List Nat := [4, 1, 2, 1, 1, 2, 1, 5, 4]
def baseStart_818926 : Nat := 118140960795 + 818926 * 2 ^ 59
def prefixEnd_818926 : Nat := 4983230072969 + 3 ^ 40 * 818926 * 2
def baseEnd_818926 : Nat := 186890070428430303092815

theorem tailTrace_818926 : CollatzResearch.WordTrace tailWord_818926 prefixEnd_818926 186890070428430303092815 := by
  unfold tailWord_818926
  simp only [CollatzResearch.WordTrace]
  refine ⟨3733585628897304783871579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19912456687452292180648421 3733585628897304783871579)
  ·
    refine ⟨5600378443345957175807369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3733585628897304783871579 5600378443345957175807369)
    ·
      refine ⟨4200283832509467881855527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5600378443345957175807369 4200283832509467881855527)
      ·
        refine ⟨6300425748764201822783291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4200283832509467881855527 6300425748764201822783291)
        ·
          refine ⟨9450638623146302734174937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6300425748764201822783291 9450638623146302734174937)
          ·
            refine ⟨7087978967359727050631203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9450638623146302734174937 7087978967359727050631203)
            ·
              refine ⟨10631968451039590575946805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7087978967359727050631203 10631968451039590575946805)
              ·
                refine ⟨996747042284961616495013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10631968451039590575946805 996747042284961616495013)
                ·
                  refine ⟨186890070428430303092815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 996747042284961616495013 186890070428430303092815)
                  ·
                    rfl

theorem cell21_818926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_818926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_818926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_818926 prefixEnd_818926 := by exact prefixLift 818926
  have htrace : WordTrace (prefixWord ++ tailWord_818926) baseStart_818926 baseEnd_818926 := by
    simpa [prefixWord, tailWord_818926, baseEnd_818926] using wordTrace_append hprefix tailTrace_818926
  have hstable : (prefixWord ++ tailWord_818926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818926).length < 2 ^ (prefixWord ++ tailWord_818926).sum := by decide
  have hdescent : baseEnd_818926 < baseStart_818926 := by decide
  rcases family_descends (prefixWord ++ tailWord_818926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819005 : List Nat := [1, 4, 1, 4, 1, 1, 3, 3, 3]
def baseStart_819005 : Nat := 118140960795 + 819005 * 2 ^ 59
def prefixEnd_819005 : Nat := 4983230072969 + 3 ^ 40 * 819005 * 2
def baseEnd_819005 : Nat := 186908099304743721275987

theorem tailTrace_819005 : CollatzResearch.WordTrace tailWord_819005 prefixEnd_819005 186908099304743721275987 := by
  unfold tailWord_819005
  simp only [CollatzResearch.WordTrace]
  refine ⟨29871566397892234763098469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19914377598594823175398979 29871566397892234763098469)
  ·
    refine ⟨5600918699604794018080963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29871566397892234763098469 5600918699604794018080963)
    ·
      refine ⟨8401378049407191027121445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5600918699604794018080963 8401378049407191027121445)
      ·
        refine ⟨1575258384263848317585271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8401378049407191027121445 1575258384263848317585271)
        ·
          refine ⟨2362887576395772476377907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1575258384263848317585271 2362887576395772476377907)
          ·
            refine ⟨3544331364593658714566861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2362887576395772476377907 3544331364593658714566861)
            ·
              refine ⟨1329124261722622017962573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3544331364593658714566861 1329124261722622017962573)
              ·
                refine ⟨498421598145983256735965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1329124261722622017962573 498421598145983256735965)
                ·
                  refine ⟨186908099304743721275987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 498421598145983256735965 186908099304743721275987)
                  ·
                    rfl

theorem cell21_819005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 3, 3].length) (baseStart_819005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_819005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_819005 prefixEnd_819005 := by exact prefixLift 819005
  have htrace : WordTrace (prefixWord ++ tailWord_819005) baseStart_819005 baseEnd_819005 := by
    simpa [prefixWord, tailWord_819005, baseEnd_819005] using wordTrace_append hprefix tailTrace_819005
  have hstable : (prefixWord ++ tailWord_819005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819005).length < 2 ^ (prefixWord ++ tailWord_819005).sum := by decide
  have hdescent : baseEnd_819005 < baseStart_819005 := by decide
  rcases family_descends (prefixWord ++ tailWord_819005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819016 : List Nat := [2, 1, 3, 1, 1, 6, 7]
def baseStart_819016 : Nat := 118140960795 + 819016 * 2 ^ 59
def prefixEnd_819016 : Nat := 4983230072969 + 3 ^ 40 * 819016 * 2
def baseEnd_819016 : Nat := 20767845517178905176959

theorem tailTrace_819016 : CollatzResearch.WordTrace tailWord_819016 prefixEnd_819016 20767845517178905176959 := by
  unfold tailWord_819016
  simp only [CollatzResearch.WordTrace]
  refine ⟨14935983800426191820874451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19914645067234922427832601 14935983800426191820874451)
  ·
    refine ⟨22403975700639287731311677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14935983800426191820874451 22403975700639287731311677)
    ·
      refine ⟨8401490887739732899241879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22403975700639287731311677 8401490887739732899241879)
      ·
        refine ⟨12602236331609599348862819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8401490887739732899241879 12602236331609599348862819)
        ·
          refine ⟨18903354497414399023294229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12602236331609599348862819 18903354497414399023294229)
          ·
            refine ⟨886094742066299954216917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18903354497414399023294229 886094742066299954216917)
            ·
              refine ⟨20767845517178905176959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 886094742066299954216917 20767845517178905176959)
              ·
                rfl

theorem cell21_819016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 7].length) (baseStart_819016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_819016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_819016 prefixEnd_819016 := by exact prefixLift 819016
  have htrace : WordTrace (prefixWord ++ tailWord_819016) baseStart_819016 baseEnd_819016 := by
    simpa [prefixWord, tailWord_819016, baseEnd_819016] using wordTrace_append hprefix tailTrace_819016
  have hstable : (prefixWord ++ tailWord_819016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819016).length < 2 ^ (prefixWord ++ tailWord_819016).sum := by decide
  have hdescent : baseEnd_819016 < baseStart_819016 := by decide
  rcases family_descends (prefixWord ++ tailWord_819016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819075 : List Nat := [1, 1, 1, 3, 4, 11]
def baseStart_819075 : Nat := 118140960795 + 819075 * 2 ^ 59
def prefixEnd_819075 : Nat := 4983230072969 + 3 ^ 40 * 819075 * 2
def baseEnd_819075 : Nat := 6923113861423672411451

theorem tailTrace_819075 : CollatzResearch.WordTrace tailWord_819075 prefixEnd_819075 6923113861423672411451 := by
  unfold tailWord_819075
  simp only [CollatzResearch.WordTrace]
  refine ⟨29874119507638636718146679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19916079671759091145431119 29874119507638636718146679)
  ·
    refine ⟨44811179261457955077220019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29874119507638636718146679 44811179261457955077220019)
    ·
      refine ⟨67216768892186932615830029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44811179261457955077220019 67216768892186932615830029)
      ·
        refine ⟨25206288334570099730936261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67216768892186932615830029 25206288334570099730936261)
        ·
          refine ⟨4726179062731893699550549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25206288334570099730936261 4726179062731893699550549)
          ·
            refine ⟨6923113861423672411451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4726179062731893699550549 6923113861423672411451)
            ·
              rfl

theorem cell21_819075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 11].length) (baseStart_819075 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_819075 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_819075 prefixEnd_819075 := by exact prefixLift 819075
  have htrace : WordTrace (prefixWord ++ tailWord_819075) baseStart_819075 baseEnd_819075 := by
    simpa [prefixWord, tailWord_819075, baseEnd_819075] using wordTrace_append hprefix tailTrace_819075
  have hstable : (prefixWord ++ tailWord_819075).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819075).length < 2 ^ (prefixWord ++ tailWord_819075).sum := by decide
  have hdescent : baseEnd_819075 < baseStart_819075 := by decide
  rcases family_descends (prefixWord ++ tailWord_819075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819151 : List Nat := [1, 1, 2, 1, 1, 5, 2, 8]
def baseStart_819151 : Nat := 118140960795 + 819151 * 2 ^ 59
def prefixEnd_819151 : Nat := 4983230072969 + 3 ^ 40 * 819151 * 2
def baseEnd_819151 : Nat := 62313806164626637280785

theorem tailTrace_819151 : CollatzResearch.WordTrace tailWord_819151 prefixEnd_819151 62313806164626637280785 := by
  unfold tailWord_819151
  simp only [CollatzResearch.WordTrace]
  refine ⟨29876891455363301697913307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19917927636908867798608871 29876891455363301697913307)
  ·
    refine ⟨44815337183044952546869961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29876891455363301697913307 44815337183044952546869961)
    ·
      refine ⟨33611502887283714410152471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44815337183044952546869961 33611502887283714410152471)
      ·
        refine ⟨50417254330925571615228707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33611502887283714410152471 50417254330925571615228707)
        ·
          refine ⟨75625881496388357422843061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50417254330925571615228707 75625881496388357422843061)
          ·
            refine ⟨7089926390286408508391537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75625881496388357422843061 7089926390286408508391537)
            ·
              refine ⟨5317444792714806381293653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7089926390286408508391537 5317444792714806381293653)
              ·
                refine ⟨62313806164626637280785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5317444792714806381293653 62313806164626637280785)
                ·
                  rfl

theorem cell21_819151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 8].length) (baseStart_819151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_819151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_819151 prefixEnd_819151 := by exact prefixLift 819151
  have htrace : WordTrace (prefixWord ++ tailWord_819151) baseStart_819151 baseEnd_819151 := by
    simpa [prefixWord, tailWord_819151, baseEnd_819151] using wordTrace_append hprefix tailTrace_819151
  have hstable : (prefixWord ++ tailWord_819151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819151).length < 2 ^ (prefixWord ++ tailWord_819151).sum := by decide
  have hdescent : baseEnd_819151 < baseStart_819151 := by decide
  rcases family_descends (prefixWord ++ tailWord_819151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819185 : List Nat := [1, 2, 2, 2, 6, 1, 7]
def baseStart_819185 : Nat := 118140960795 + 819185 * 2 ^ 59
def prefixEnd_819185 : Nat := 4983230072969 + 3 ^ 40 * 819185 * 2
def baseEnd_819185 : Nat := 20772130861900378697291

theorem tailTrace_819185 : CollatzResearch.WordTrace tailWord_819185 prefixEnd_819185 20772130861900378697291 := by
  unfold tailWord_819185
  simp only [CollatzResearch.WordTrace]
  refine ⟨29878131537240125504651009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19918754358160083669767339 29878131537240125504651009)
  ·
    refine ⟨22408598652930094128488257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29878131537240125504651009 22408598652930094128488257)
    ·
      refine ⟨16806448989697570596366193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22408598652930094128488257 16806448989697570596366193)
      ·
        refine ⟨12604836742273177947274645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16806448989697570596366193 12604836742273177947274645)
        ·
          refine ⟨590851722294055216278499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12604836742273177947274645 590851722294055216278499)
          ·
            refine ⟨886277583441082824417749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 590851722294055216278499 886277583441082824417749)
            ·
              refine ⟨20772130861900378697291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 886277583441082824417749 20772130861900378697291)
              ·
                rfl

theorem cell21_819185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 7].length) (baseStart_819185 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_819185 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_819185 prefixEnd_819185 := by exact prefixLift 819185
  have htrace : WordTrace (prefixWord ++ tailWord_819185) baseStart_819185 baseEnd_819185 := by
    simpa [prefixWord, tailWord_819185, baseEnd_819185] using wordTrace_append hprefix tailTrace_819185
  have hstable : (prefixWord ++ tailWord_819185).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819185).length < 2 ^ (prefixWord ++ tailWord_819185).sum := by decide
  have hdescent : baseEnd_819185 < baseStart_819185 := by decide
  rcases family_descends (prefixWord ++ tailWord_819185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819199 : List Nat := [1, 1, 2, 2, 1, 2, 1, 8, 3]
def baseStart_819199 : Nat := 118140960795 + 819199 * 2 ^ 59
def prefixEnd_819199 : Nat := 4983230072969 + 3 ^ 40 * 819199 * 2
def baseEnd_819199 : Nat := 186952372747842495042257

theorem tailTrace_819199 : CollatzResearch.WordTrace tailWord_819199 prefixEnd_819199 186952372747842495042257 := by
  unfold tailWord_819199
  simp only [CollatzResearch.WordTrace]
  refine ⟨29878642159189405895660651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19919094772792937263773767 29878642159189405895660651)
  ·
    refine ⟨44817963238784108843490977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29878642159189405895660651 44817963238784108843490977)
    ·
      refine ⟨33613472429088081632618233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44817963238784108843490977 33613472429088081632618233)
      ·
        refine ⟨25210104321816061224463675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33613472429088081632618233 25210104321816061224463675)
        ·
          refine ⟨37815156482724091836695513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25210104321816061224463675 37815156482724091836695513)
          ·
            refine ⟨28361367362043068877521635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37815156482724091836695513 28361367362043068877521635)
            ·
              refine ⟨42542051043064603316282453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28361367362043068877521635 42542051043064603316282453)
              ·
                refine ⟨498539660660913320112685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 42542051043064603316282453 498539660660913320112685)
                ·
                  refine ⟨186952372747842495042257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 498539660660913320112685 186952372747842495042257)
                  ·
                    rfl

theorem cell21_819199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 8, 3].length) (baseStart_819199 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_819199 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_819199 prefixEnd_819199 := by exact prefixLift 819199
  have htrace : WordTrace (prefixWord ++ tailWord_819199) baseStart_819199 baseEnd_819199 := by
    simpa [prefixWord, tailWord_819199, baseEnd_819199] using wordTrace_append hprefix tailTrace_819199
  have hstable : (prefixWord ++ tailWord_819199).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819199).length < 2 ^ (prefixWord ++ tailWord_819199).sum := by decide
  have hdescent : baseEnd_819199 < baseStart_819199 := by decide
  rcases family_descends (prefixWord ++ tailWord_819199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819258 : List Nat := [3, 1, 1, 1, 3, 1, 1, 5, 5]
def baseStart_819258 : Nat := 118140960795 + 819258 * 2 ^ 59
def prefixEnd_819258 : Nat := 4983230072969 + 3 ^ 40 * 819258 * 2
def baseEnd_819258 : Nat := 186965837351671503558803

theorem tailTrace_819258 : CollatzResearch.WordTrace tailWord_819258 prefixEnd_819258 186965837351671503558803 := by
  unfold tailWord_819258
  simp only [CollatzResearch.WordTrace]
  refine ⟨7470198516493914743014607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19920529377317105981372285 7470198516493914743014607)
  ·
    refine ⟨11205297774740872114521911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7470198516493914743014607 11205297774740872114521911)
    ·
      refine ⟨16807946662111308171782867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11205297774740872114521911 16807946662111308171782867)
      ·
        refine ⟨25211919993166962257674301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16807946662111308171782867 25211919993166962257674301)
        ·
          refine ⟨9454469997437610846627863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25211919993166962257674301 9454469997437610846627863)
          ·
            refine ⟨14181704996156416269941795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9454469997437610846627863 14181704996156416269941795)
            ·
              refine ⟨21272557494234624404912693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14181704996156416269941795 21272557494234624404912693)
              ·
                refine ⟨1994302265084496037960565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21272557494234624404912693 1994302265084496037960565)
                ·
                  refine ⟨186965837351671503558803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1994302265084496037960565 186965837351671503558803)
                  ·
                    rfl

theorem cell21_819258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_819258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_819258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_819258 prefixEnd_819258 := by exact prefixLift 819258
  have htrace : WordTrace (prefixWord ++ tailWord_819258) baseStart_819258 baseEnd_819258 := by
    simpa [prefixWord, tailWord_819258, baseEnd_819258] using wordTrace_append hprefix tailTrace_819258
  have hstable : (prefixWord ++ tailWord_819258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819258).length < 2 ^ (prefixWord ++ tailWord_819258).sum := by decide
  have hdescent : baseEnd_819258 < baseStart_819258 := by decide
  rcases family_descends (prefixWord ++ tailWord_819258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819292 : List Nat := [2, 2, 4, 1, 1, 2, 1, 5, 3]
def baseStart_819292 : Nat := 118140960795 + 819292 * 2 ^ 59
def prefixEnd_819292 : Nat := 4983230072969 + 3 ^ 40 * 819292 * 2
def baseEnd_819292 : Nat := 186973596614894999992067

theorem tailTrace_819292 : CollatzResearch.WordTrace tailWord_819292 prefixEnd_819292 186973596614894999992067 := by
  unfold tailWord_819292
  simp only [CollatzResearch.WordTrace]
  refine ⟨14941017073926241389398065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19921356098568321852530753 14941017073926241389398065)
  ·
    refine ⟨11205762805444681042048549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14941017073926241389398065 11205762805444681042048549)
    ·
      refine ⟨2101080526020877695384103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11205762805444681042048549 2101080526020877695384103)
      ·
        refine ⟨3151620789031316543076155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2101080526020877695384103 3151620789031316543076155)
        ·
          refine ⟨4727431183546974814614233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3151620789031316543076155 4727431183546974814614233)
          ·
            refine ⟨3545573387660231110960675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4727431183546974814614233 3545573387660231110960675)
            ·
              refine ⟨5318360081490346666441013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3545573387660231110960675 5318360081490346666441013)
              ·
                refine ⟨498596257639719999978845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5318360081490346666441013 498596257639719999978845)
                ·
                  refine ⟨186973596614894999992067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 498596257639719999978845 186973596614894999992067)
                  ·
                    rfl

theorem cell21_819292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 5, 3].length) (baseStart_819292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_819292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_819292 prefixEnd_819292 := by exact prefixLift 819292
  have htrace : WordTrace (prefixWord ++ tailWord_819292) baseStart_819292 baseEnd_819292 := by
    simpa [prefixWord, tailWord_819292, baseEnd_819292] using wordTrace_append hprefix tailTrace_819292
  have hstable : (prefixWord ++ tailWord_819292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819292).length < 2 ^ (prefixWord ++ tailWord_819292).sum := by decide
  have hdescent : baseEnd_819292 < baseStart_819292 := by decide
  rcases family_descends (prefixWord ++ tailWord_819292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819303 : List Nat := [1, 1, 5, 1, 1, 2, 10]
def baseStart_819303 : Nat := 118140960795 + 819303 * 2 ^ 59
def prefixEnd_819303 : Nat := 4983230072969 + 3 ^ 40 * 819303 * 2
def baseEnd_819303 : Nat := 20775122996084602812079

theorem tailTrace_819303 : CollatzResearch.WordTrace tailWord_819303 prefixEnd_819303 20775122996084602812079 := by
  unfold tailWord_819303
  simp only [CollatzResearch.WordTrace]
  refine ⟨29882435350812631657446563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19921623567208421104964375 29882435350812631657446563)
  ·
    refine ⟨44823653026218947486169845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29882435350812631657446563 44823653026218947486169845)
    ·
      refine ⟨4202217471208026326828423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44823653026218947486169845 4202217471208026326828423)
      ·
        refine ⟨6303326206812039490242635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4202217471208026326828423 6303326206812039490242635)
        ·
          refine ⟨9454989310218059235363953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6303326206812039490242635 9454989310218059235363953)
          ·
            refine ⟨7091241982663544426522965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9454989310218059235363953 7091241982663544426522965)
            ·
              refine ⟨20775122996084602812079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7091241982663544426522965 20775122996084602812079)
              ·
                rfl

theorem cell21_819303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 10].length) (baseStart_819303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_819303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_819303 prefixEnd_819303 := by exact prefixLift 819303
  have htrace : WordTrace (prefixWord ++ tailWord_819303) baseStart_819303 baseEnd_819303 := by
    simpa [prefixWord, tailWord_819303, baseEnd_819303] using wordTrace_append hprefix tailTrace_819303
  have hstable : (prefixWord ++ tailWord_819303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819303).length < 2 ^ (prefixWord ++ tailWord_819303).sum := by decide
  have hdescent : baseEnd_819303 < baseStart_819303 := by decide
  rcases family_descends (prefixWord ++ tailWord_819303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819306 : List Nat := [3, 1, 3, 2, 3, 1, 1, 1, 6]
def baseStart_819306 : Nat := 118140960795 + 819306 * 2 ^ 59
def prefixEnd_819306 : Nat := 4983230072969 + 3 ^ 40 * 819306 * 2
def baseEnd_819306 : Nat := 186976791605634086758705

theorem tailTrace_819306 : CollatzResearch.WordTrace tailWord_819306 prefixEnd_819306 186976791605634086758705 := by
  unfold tailWord_819306
  simp only [CollatzResearch.WordTrace]
  refine ⟨7470636192450440792451443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19921696513201175446537181 7470636192450440792451443)
  ·
    refine ⟨11205954288675661188677165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7470636192450440792451443 11205954288675661188677165)
    ·
      refine ⟨4202232858253372945753937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11205954288675661188677165 4202232858253372945753937)
      ·
        refine ⟨3151674643690029709315453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4202232858253372945753937 3151674643690029709315453)
        ·
          refine ⟨1181877991383761140993295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3151674643690029709315453 1181877991383761140993295)
          ·
            refine ⟨1772816987075641711489943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1181877991383761140993295 1772816987075641711489943)
            ·
              refine ⟨2659225480613462567234915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1772816987075641711489943 2659225480613462567234915)
              ·
                refine ⟨3988838220920193850852373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2659225480613462567234915 3988838220920193850852373)
                ·
                  refine ⟨186976791605634086758705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3988838220920193850852373 186976791605634086758705)
                  ·
                    rfl

theorem cell21_819306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 6].length) (baseStart_819306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_819306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_819306 prefixEnd_819306 := by exact prefixLift 819306
  have htrace : WordTrace (prefixWord ++ tailWord_819306) baseStart_819306 baseEnd_819306 := by
    simpa [prefixWord, tailWord_819306, baseEnd_819306] using wordTrace_append hprefix tailTrace_819306
  have hstable : (prefixWord ++ tailWord_819306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819306).length < 2 ^ (prefixWord ++ tailWord_819306).sum := by decide
  have hdescent : baseEnd_819306 < baseStart_819306 := by decide
  rcases family_descends (prefixWord ++ tailWord_819306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819365 : List Nat := [1, 3, 1, 2, 1, 3, 2, 4, 4]
def baseStart_819365 : Nat := 118140960795 + 819365 * 2 ^ 59
def prefixEnd_819365 : Nat := 4983230072969 + 3 ^ 40 * 819365 * 2
def baseEnd_819365 : Nat := 186990256209463095275251

theorem tailTrace_819365 : CollatzResearch.WordTrace tailWord_819365 prefixEnd_819365 186990256209463095275251 := by
  unfold tailWord_819365
  simp only [CollatzResearch.WordTrace]
  refine ⟨29884696676588016246203549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19923131117725344164135699 29884696676588016246203549)
  ·
    refine ⟨11206761253720506092326331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29884696676588016246203549 11206761253720506092326331)
    ·
      refine ⟨16810141880580759138489497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11206761253720506092326331 16810141880580759138489497)
      ·
        refine ⟨12607606410435569353867123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16810141880580759138489497 12607606410435569353867123)
        ·
          refine ⟨18911409615653354030800685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12607606410435569353867123 18911409615653354030800685)
          ·
            refine ⟨7091778605870007761550257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18911409615653354030800685 7091778605870007761550257)
            ·
              refine ⟨5318833954402505821162693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7091778605870007761550257 5318833954402505821162693)
              ·
                refine ⟨997281366450469841468005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5318833954402505821162693 997281366450469841468005)
                ·
                  refine ⟨186990256209463095275251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 997281366450469841468005 186990256209463095275251)
                  ·
                    rfl

theorem cell21_819365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4, 4].length) (baseStart_819365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_819365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_819365 prefixEnd_819365 := by exact prefixLift 819365
  have htrace : WordTrace (prefixWord ++ tailWord_819365) baseStart_819365 baseEnd_819365 := by
    simpa [prefixWord, tailWord_819365, baseEnd_819365] using wordTrace_append hprefix tailTrace_819365
  have hstable : (prefixWord ++ tailWord_819365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819365).length < 2 ^ (prefixWord ++ tailWord_819365).sum := by decide
  have hdescent : baseEnd_819365 < baseStart_819365 := by decide
  rcases family_descends (prefixWord ++ tailWord_819365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819374 : List Nat := [4, 1, 4, 2, 2, 1, 2, 1, 4]
def baseStart_819374 : Nat := 118140960795 + 819374 * 2 ^ 59
def prefixEnd_819374 : Nat := 4983230072969 + 3 ^ 40 * 819374 * 2
def baseEnd_819374 : Nat := 186992310132081079625233

theorem tailTrace_819374 : CollatzResearch.WordTrace tailWord_819374 prefixEnd_819374 186992310132081079625233 := by
  unfold tailWord_819374
  simp only [CollatzResearch.WordTrace]
  refine ⟨3735628116694426347910147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19923349955703607188854117 3735628116694426347910147)
  ·
    refine ⟨5603442175041639521865221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3735628116694426347910147 5603442175041639521865221)
    ·
      refine ⟨1050645407820307410349729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5603442175041639521865221 1050645407820307410349729)
      ·
        refine ⟨787984055865230557762297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1050645407820307410349729 787984055865230557762297)
        ·
          refine ⟨590988041898922918321723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 787984055865230557762297 590988041898922918321723)
          ·
            refine ⟨886482062848384377482585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 590988041898922918321723 886482062848384377482585)
            ·
              refine ⟨664861547136288283111939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 886482062848384377482585 664861547136288283111939)
              ·
                refine ⟨997292320704432424667909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 664861547136288283111939 997292320704432424667909)
                ·
                  refine ⟨186992310132081079625233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 997292320704432424667909 186992310132081079625233)
                  ·
                    rfl

theorem cell21_819374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 1, 4].length) (baseStart_819374 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_819374 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_819374 prefixEnd_819374 := by exact prefixLift 819374
  have htrace : WordTrace (prefixWord ++ tailWord_819374) baseStart_819374 baseEnd_819374 := by
    simpa [prefixWord, tailWord_819374, baseEnd_819374] using wordTrace_append hprefix tailTrace_819374
  have hstable : (prefixWord ++ tailWord_819374).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819374).length < 2 ^ (prefixWord ++ tailWord_819374).sum := by decide
  have hdescent : baseEnd_819374 < baseStart_819374 := by decide
  rcases family_descends (prefixWord ++ tailWord_819374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819396 : List Nat := [2, 3, 3, 1, 2, 1, 2, 7]
def baseStart_819396 : Nat := 118140960795 + 819396 * 2 ^ 59
def prefixEnd_819396 : Nat := 4983230072969 + 3 ^ 40 * 819396 * 2
def baseEnd_819396 : Nat := 62332443610604643419507

theorem tailTrace_819396 : CollatzResearch.WordTrace tailWord_819396 prefixEnd_819396 62332443610604643419507 := by
  unfold tailWord_819396
  simp only [CollatzResearch.WordTrace]
  refine ⟨14942913669737854270291021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19923884892983805693721361 14942913669737854270291021)
  ·
    refine ⟨5603592626151695351359133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14942913669737854270291021 5603592626151695351359133)
    ·
      refine ⟨2101347234806885756759675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5603592626151695351359133 2101347234806885756759675)
      ·
        refine ⟨3152020852210328635139513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2101347234806885756759675 3152020852210328635139513)
        ·
          refine ⟨2364015639157746476354635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3152020852210328635139513 2364015639157746476354635)
          ·
            refine ⟨3546023458736619714531953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2364015639157746476354635 3546023458736619714531953)
            ·
              refine ⟨2659517594052464785898965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3546023458736619714531953 2659517594052464785898965)
              ·
                refine ⟨62332443610604643419507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2659517594052464785898965 62332443610604643419507)
                ·
                  rfl

theorem cell21_819396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 7].length) (baseStart_819396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_819396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_819396 prefixEnd_819396 := by exact prefixLift 819396
  have htrace : WordTrace (prefixWord ++ tailWord_819396) baseStart_819396 baseEnd_819396 := by
    simpa [prefixWord, tailWord_819396, baseEnd_819396] using wordTrace_append hprefix tailTrace_819396
  have hstable : (prefixWord ++ tailWord_819396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819396).length < 2 ^ (prefixWord ++ tailWord_819396).sum := by decide
  have hdescent : baseEnd_819396 < baseStart_819396 := by decide
  rcases family_descends (prefixWord ++ tailWord_819396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819441 : List Nat := [1, 2, 2, 2, 2, 1, 4, 3, 4]
def baseStart_819441 : Nat := 118140960795 + 819441 * 2 ^ 59
def prefixEnd_819441 : Nat := 4983230072969 + 3 ^ 40 * 819441 * 2
def baseEnd_819441 : Nat := 187007600444903852008429

theorem tailTrace_819441 : CollatzResearch.WordTrace tailWord_819441 prefixEnd_819441 187007600444903852008429 := by
  unfold tailWord_819441
  simp only [CollatzResearch.WordTrace]
  refine ⟨29887468624312681225970177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19924979082875120817313451 29887468624312681225970177)
  ·
    refine ⟨22415601468234510919477633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29887468624312681225970177 22415601468234510919477633)
    ·
      refine ⟨16811701101175883189608225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22415601468234510919477633 16811701101175883189608225)
      ·
        refine ⟨12608775825881912392206169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16811701101175883189608225 12608775825881912392206169)
        ·
          refine ⟨9456581869411434294154627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12608775825881912392206169 9456581869411434294154627)
          ·
            refine ⟨14184872804117151441231941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9456581869411434294154627 14184872804117151441231941)
            ·
              refine ⟨2659663650771965895230989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14184872804117151441231941 2659663650771965895230989)
              ·
                refine ⟨997373869039487210711621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2659663650771965895230989 997373869039487210711621)
                ·
                  refine ⟨187007600444903852008429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 997373869039487210711621 187007600444903852008429)
                  ·
                    rfl

theorem cell21_819441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3, 4].length) (baseStart_819441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_819441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_819441 prefixEnd_819441 := by exact prefixLift 819441
  have htrace : WordTrace (prefixWord ++ tailWord_819441) baseStart_819441 baseEnd_819441 := by
    simpa [prefixWord, tailWord_819441, baseEnd_819441] using wordTrace_append hprefix tailTrace_819441
  have hstable : (prefixWord ++ tailWord_819441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819441).length < 2 ^ (prefixWord ++ tailWord_819441).sum := by decide
  have hdescent : baseEnd_819441 < baseStart_819441 := by decide
  rcases family_descends (prefixWord ++ tailWord_819441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819506 : List Nat := [3, 2, 1, 1, 6, 1, 2, 5]
def baseStart_819506 : Nat := 118140960795 + 819506 * 2 ^ 59
def prefixEnd_819506 : Nat := 4983230072969 + 3 ^ 40 * 819506 * 2
def baseEnd_819506 : Nat := 62340811443492727808321

theorem tailTrace_819506 : CollatzResearch.WordTrace tailWord_819506 prefixEnd_819506 62340811443492727808321 := by
  unfold tailWord_819506
  simp only [CollatzResearch.WordTrace]
  refine ⟨7472459842269299331771593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19926559579384798218057581 7472459842269299331771593)
  ·
    refine ⟨5604344881701974498828695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7472459842269299331771593 5604344881701974498828695)
    ·
      refine ⟨8406517322552961748243043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5604344881701974498828695 8406517322552961748243043)
      ·
        refine ⟨12609775983829442622364565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8406517322552961748243043 12609775983829442622364565)
        ·
          refine ⟨591083249242005122923339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12609775983829442622364565 591083249242005122923339)
          ·
            refine ⟨886624873863007684385009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 591083249242005122923339 886624873863007684385009)
            ·
              refine ⟨664968655397255763288757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 886624873863007684385009 664968655397255763288757)
              ·
                refine ⟨62340811443492727808321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 664968655397255763288757 62340811443492727808321)
                ·
                  rfl

theorem cell21_819506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 5].length) (baseStart_819506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_819506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_819506 prefixEnd_819506 := by exact prefixLift 819506
  have htrace : WordTrace (prefixWord ++ tailWord_819506) baseStart_819506 baseEnd_819506 := by
    simpa [prefixWord, tailWord_819506, baseEnd_819506] using wordTrace_append hprefix tailTrace_819506
  have hstable : (prefixWord ++ tailWord_819506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819506).length < 2 ^ (prefixWord ++ tailWord_819506).sum := by decide
  have hdescent : baseEnd_819506 < baseStart_819506 := by decide
  rcases family_descends (prefixWord ++ tailWord_819506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819593 : List Nat := [1, 2, 1, 1, 6, 1, 1, 4, 4]
def baseStart_819593 : Nat := 118140960795 + 819593 * 2 ^ 59
def prefixEnd_819593 : Nat := 4983230072969 + 3 ^ 40 * 819593 * 2
def baseEnd_819593 : Nat := 187042288915785365474785

theorem tailTrace_819593 : CollatzResearch.WordTrace tailWord_819593 prefixEnd_819593 187042288915785365474785 := by
  unfold tailWord_819593
  simp only [CollatzResearch.WordTrace]
  refine ⟨29893012519762011185503433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19928675013174674123668955 29893012519762011185503433)
  ·
    refine ⟨22419759389821508389127575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29893012519762011185503433 22419759389821508389127575)
    ·
      refine ⟨33629639084732262583691363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22419759389821508389127575 33629639084732262583691363)
      ·
        refine ⟨50444458627098393875537045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33629639084732262583691363 50444458627098393875537045)
        ·
          refine ⟨2364583998145237212915799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 50444458627098393875537045 2364583998145237212915799)
          ·
            refine ⟨3546875997217855819373699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2364583998145237212915799 3546875997217855819373699)
            ·
              refine ⟨5320313995826783729060549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3546875997217855819373699 5320313995826783729060549)
              ·
                refine ⟨997558874217521949198853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5320313995826783729060549 997558874217521949198853)
                ·
                  refine ⟨187042288915785365474785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 997558874217521949198853 187042288915785365474785)
                  ·
                    rfl

theorem cell21_819593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4, 4].length) (baseStart_819593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_819593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_819593 prefixEnd_819593 := by exact prefixLift 819593
  have htrace : WordTrace (prefixWord ++ tailWord_819593) baseStart_819593 baseEnd_819593 := by
    simpa [prefixWord, tailWord_819593, baseEnd_819593] using wordTrace_append hprefix tailTrace_819593
  have hstable : (prefixWord ++ tailWord_819593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819593).length < 2 ^ (prefixWord ++ tailWord_819593).sum := by decide
  have hdescent : baseEnd_819593 < baseStart_819593 := by decide
  rcases family_descends (prefixWord ++ tailWord_819593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819596 : List Nat := [2, 2, 1, 2, 1, 4, 4, 2, 3]
def baseStart_819596 : Nat := 118140960795 + 819596 * 2 ^ 59
def prefixEnd_819596 : Nat := 4983230072969 + 3 ^ 40 * 819596 * 2
def baseEnd_819596 : Nat := 187042973556658026924779

theorem tailTrace_819596 : CollatzResearch.WordTrace tailWord_819596 prefixEnd_819596 187042973556658026924779 := by
  unfold tailWord_819596
  simp only [CollatzResearch.WordTrace]
  refine ⟨14946560969375571348931321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19928747959167428465241761 14946560969375571348931321)
  ·
    refine ⟨11209920727031678511698491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14946560969375571348931321 11209920727031678511698491)
    ·
      refine ⟨16814881090547517767547737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11209920727031678511698491 16814881090547517767547737)
      ·
        refine ⟨12611160817910638325660803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16814881090547517767547737 12611160817910638325660803)
        ·
          refine ⟨18916741226865957488491205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12611160817910638325660803 18916741226865957488491205)
          ·
            refine ⟨3546888980037367029092101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18916741226865957488491205 3546888980037367029092101)
            ·
              refine ⟨665041683757006317954769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3546888980037367029092101 665041683757006317954769)
              ·
                refine ⟨498781262817754738466077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 665041683757006317954769 498781262817754738466077)
                ·
                  refine ⟨187042973556658026924779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 498781262817754738466077 187042973556658026924779)
                  ·
                    rfl

theorem cell21_819596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 2, 3].length) (baseStart_819596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_819596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_819596 prefixEnd_819596 := by exact prefixLift 819596
  have htrace : WordTrace (prefixWord ++ tailWord_819596) baseStart_819596 baseEnd_819596 := by
    simpa [prefixWord, tailWord_819596, baseEnd_819596] using wordTrace_append hprefix tailTrace_819596
  have hstable : (prefixWord ++ tailWord_819596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819596).length < 2 ^ (prefixWord ++ tailWord_819596).sum := by decide
  have hdescent : baseEnd_819596 < baseStart_819596 := by decide
  rcases family_descends (prefixWord ++ tailWord_819596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819607 : List Nat := [1, 1, 3, 3, 1, 1, 5, 6]
def baseStart_819607 : Nat := 118140960795 + 819607 * 2 ^ 59
def prefixEnd_819607 : Nat := 4983230072969 + 3 ^ 40 * 819607 * 2
def baseEnd_819607 : Nat := 62348494635508150747141

theorem tailTrace_819607 : CollatzResearch.WordTrace tailWord_819607 prefixEnd_819607 62348494635508150747141 := by
  unfold tailWord_819607
  simp only [CollatzResearch.WordTrace]
  refine ⟨29893523141711291576513075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19929015427807527717675383 29893523141711291576513075)
  ·
    refine ⟨44840284712566937364769613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29893523141711291576513075 44840284712566937364769613)
    ·
      refine ⟨16815106767212601511788605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44840284712566937364769613 16815106767212601511788605)
      ·
        refine ⟨6305665037704725566920727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16815106767212601511788605 6305665037704725566920727)
        ·
          refine ⟨9458497556557088350381091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6305665037704725566920727 9458497556557088350381091)
          ·
            refine ⟨14187746334835632525571637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9458497556557088350381091 14187746334835632525571637)
            ·
              refine ⟨1330101218890840549272341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14187746334835632525571637 1330101218890840549272341)
              ·
                refine ⟨62348494635508150747141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1330101218890840549272341 62348494635508150747141)
                ·
                  rfl

theorem cell21_819607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 6].length) (baseStart_819607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_819607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_819607 prefixEnd_819607 := by exact prefixLift 819607
  have htrace : WordTrace (prefixWord ++ tailWord_819607) baseStart_819607 baseEnd_819607 := by
    simpa [prefixWord, tailWord_819607, baseEnd_819607] using wordTrace_append hprefix tailTrace_819607
  have hstable : (prefixWord ++ tailWord_819607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819607).length < 2 ^ (prefixWord ++ tailWord_819607).sum := by decide
  have hdescent : baseEnd_819607 < baseStart_819607 := by decide
  rcases family_descends (prefixWord ++ tailWord_819607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819655 : List Nat := [1, 1, 4, 1, 1, 4, 2, 4, 3]
def baseStart_819655 : Nat := 118140960795 + 819655 * 2 ^ 59
def prefixEnd_819655 : Nat := 4983230072969 + 3 ^ 40 * 819655 * 2
def baseEnd_819655 : Nat := 187056438160487035441325

theorem tailTrace_819655 : CollatzResearch.WordTrace tailWord_819655 prefixEnd_819655 187056438160487035441325 := by
  unfold tailWord_819655
  simp only [CollatzResearch.WordTrace]
  refine ⟨29895273845537395774260419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19930182563691597182840279 29895273845537395774260419)
  ·
    refine ⟨44842910768306093661390629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29895273845537395774260419 44842910768306093661390629)
    ·
      refine ⟨8408045769057392561510743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44842910768306093661390629 8408045769057392561510743)
      ·
        refine ⟨12612068653586088842266115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8408045769057392561510743 12612068653586088842266115)
        ·
          refine ⟨18918102980379133263399173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12612068653586088842266115 18918102980379133263399173)
          ·
            refine ⟨3547144308821087486887345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18918102980379133263399173 3547144308821087486887345)
            ·
              refine ⟨2660358231615815615165509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3547144308821087486887345 2660358231615815615165509)
              ·
                refine ⟨498817168427965427843533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2660358231615815615165509 498817168427965427843533)
                ·
                  refine ⟨187056438160487035441325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 498817168427965427843533 187056438160487035441325)
                  ·
                    rfl

theorem cell21_819655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 4, 3].length) (baseStart_819655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_819655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_819655 prefixEnd_819655 := by exact prefixLift 819655
  have htrace : WordTrace (prefixWord ++ tailWord_819655) baseStart_819655 baseEnd_819655 := by
    simpa [prefixWord, tailWord_819655, baseEnd_819655] using wordTrace_append hprefix tailTrace_819655
  have hstable : (prefixWord ++ tailWord_819655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819655).length < 2 ^ (prefixWord ++ tailWord_819655).sum := by decide
  have hdescent : baseEnd_819655 < baseStart_819655 := by decide
  rcases family_descends (prefixWord ++ tailWord_819655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819821 : List Nat := [1, 5, 1, 1, 3, 2, 1, 1, 6]
def baseStart_819821 : Nat := 118140960795 + 819821 * 2 ^ 59
def prefixEnd_819821 : Nat := 4983230072969 + 3 ^ 40 * 819821 * 2
def baseEnd_819821 : Nat := 187094321622107635674319

theorem tailTrace_819821 : CollatzResearch.WordTrace tailWord_819821 prefixEnd_819821 187094321622107635674319 := by
  unfold tailWord_819821
  simp only [CollatzResearch.WordTrace]
  refine ⟨29901328362936006124803317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19934218908624004083202211 29901328362936006124803317)
  ·
    refine ⟨2803249534025250574200311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29901328362936006124803317 2803249534025250574200311)
    ·
      refine ⟨4204874301037875861300467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2803249534025250574200311 4204874301037875861300467)
      ·
        refine ⟨6307311451556813791950701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4204874301037875861300467 6307311451556813791950701)
        ·
          refine ⟨2365241794333805171981513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6307311451556813791950701 2365241794333805171981513)
          ·
            refine ⟨1773931345750353878986135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2365241794333805171981513 1773931345750353878986135)
            ·
              refine ⟨2660897018625530818479203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1773931345750353878986135 2660897018625530818479203)
              ·
                refine ⟨3991345527938296227718805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2660897018625530818479203 3991345527938296227718805)
                ·
                  refine ⟨187094321622107635674319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3991345527938296227718805 187094321622107635674319)
                  ·
                    rfl

theorem cell21_819821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_819821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_819821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_819821 prefixEnd_819821 := by exact prefixLift 819821
  have htrace : WordTrace (prefixWord ++ tailWord_819821) baseStart_819821 baseEnd_819821 := by
    simpa [prefixWord, tailWord_819821, baseEnd_819821] using wordTrace_append hprefix tailTrace_819821
  have hstable : (prefixWord ++ tailWord_819821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819821).length < 2 ^ (prefixWord ++ tailWord_819821).sum := by decide
  have hdescent : baseEnd_819821 < baseStart_819821 := by decide
  rcases family_descends (prefixWord ++ tailWord_819821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820015 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 10]
def baseStart_820015 : Nat := 118140960795 + 820015 * 2 ^ 59
def prefixEnd_820015 : Nat := 4983230072969 + 3 ^ 40 * 820015 * 2
def baseEnd_820015 : Nat := 187138595065206409440589

theorem tailTrace_820015 : CollatzResearch.WordTrace tailWord_820015 prefixEnd_820015 187138595065206409440589 := by
  unfold tailWord_820015
  simp only [CollatzResearch.WordTrace]
  refine ⟨29908404124233177257365499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19938936082822118171576999 29908404124233177257365499)
  ·
    refine ⟨44862606186349765886048249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29908404124233177257365499 44862606186349765886048249)
    ·
      refine ⟨33646954639762324414536187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44862606186349765886048249 33646954639762324414536187)
      ·
        refine ⟨50470431959643486621804281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33646954639762324414536187 50470431959643486621804281)
        ·
          refine ⟨37852823969732614966353211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50470431959643486621804281 37852823969732614966353211)
          ·
            refine ⟨56779235954598922449529817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37852823969732614966353211 56779235954598922449529817)
            ·
              refine ⟨42584426965949191837147363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56779235954598922449529817 42584426965949191837147363)
              ·
                refine ⟨63876640448923787755721045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42584426965949191837147363 63876640448923787755721045)
                ·
                  refine ⟨187138595065206409440589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 63876640448923787755721045 187138595065206409440589)
                  ·
                    rfl

theorem cell21_820015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 10].length) (baseStart_820015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_820015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_820015 prefixEnd_820015 := by exact prefixLift 820015
  have htrace : WordTrace (prefixWord ++ tailWord_820015) baseStart_820015 baseEnd_820015 := by
    simpa [prefixWord, tailWord_820015, baseEnd_820015] using wordTrace_append hprefix tailTrace_820015
  have hstable : (prefixWord ++ tailWord_820015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820015).length < 2 ^ (prefixWord ++ tailWord_820015).sum := by decide
  have hdescent : baseEnd_820015 < baseStart_820015 := by decide
  rcases family_descends (prefixWord ++ tailWord_820015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820038 : List Nat := [6, 1, 1, 2, 3, 1, 7]
def baseStart_820038 : Nat := 118140960795 + 820038 * 2 ^ 59
def prefixEnd_820038 : Nat := 4983230072969 + 3 ^ 40 * 820038 * 2
def baseEnd_820038 : Nat := 20793760442062608950801

theorem tailTrace_820038 : CollatzResearch.WordTrace tailWord_820038 prefixEnd_820038 20793760442062608950801 := by
  unfold tailWord_820038
  simp only [CollatzResearch.WordTrace]
  refine ⟨934663843848432880795399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19939495335433234790301845 934663843848432880795399)
  ·
    refine ⟨1401995765772649321193099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 934663843848432880795399 1401995765772649321193099)
    ·
      refine ⟨2102993648658973981789649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1401995765772649321193099 2102993648658973981789649)
      ·
        refine ⟨1577245236494230486342237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2102993648658973981789649 1577245236494230486342237)
        ·
          refine ⟨591466963685336432378339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1577245236494230486342237 591466963685336432378339)
          ·
            refine ⟨887200445528004648567509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 591466963685336432378339 887200445528004648567509)
            ·
              refine ⟨20793760442062608950801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 887200445528004648567509 20793760442062608950801)
              ·
                rfl

theorem cell21_820038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 7].length) (baseStart_820038 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_820038 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_820038 prefixEnd_820038 := by exact prefixLift 820038
  have htrace : WordTrace (prefixWord ++ tailWord_820038) baseStart_820038 baseEnd_820038 := by
    simpa [prefixWord, tailWord_820038, baseEnd_820038] using wordTrace_append hprefix tailTrace_820038
  have hstable : (prefixWord ++ tailWord_820038).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820038).length < 2 ^ (prefixWord ++ tailWord_820038).sum := by decide
  have hdescent : baseEnd_820038 < baseStart_820038 := by decide
  rcases family_descends (prefixWord ++ tailWord_820038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820052 : List Nat := [2, 4, 1, 1, 5, 1, 1, 1, 5]
def baseStart_820052 : Nat := 118140960795 + 820052 * 2 ^ 59
def prefixEnd_820052 : Nat := 4983230072969 + 3 ^ 40 * 820052 * 2
def baseEnd_820052 : Nat := 187147038969302567323847

theorem tailTrace_820052 : CollatzResearch.WordTrace tailWord_820052 prefixEnd_820052 187147038969302567323847 := by
  unfold tailWord_820052
  simp only [CollatzResearch.WordTrace]
  refine ⟨14954876812549566288231205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19939835750066088384308273 14954876812549566288231205)
  ·
    refine ⟨2804039402353043679043351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14954876812549566288231205 2804039402353043679043351)
    ·
      refine ⟨4206059103529565518565027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2804039402353043679043351 4206059103529565518565027)
      ·
        refine ⟨6309088655294348277847541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4206059103529565518565027 6309088655294348277847541)
        ·
          refine ⟨591477061433845151048207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6309088655294348277847541 591477061433845151048207)
          ·
            refine ⟨887215592150767726572311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 591477061433845151048207 887215592150767726572311)
            ·
              refine ⟨1330823388226151589858467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 887215592150767726572311 1330823388226151589858467)
              ·
                refine ⟨1996235082339227384787701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1330823388226151589858467 1996235082339227384787701)
                ·
                  refine ⟨187147038969302567323847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1996235082339227384787701 187147038969302567323847)
                  ·
                    rfl

theorem cell21_820052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_820052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_820052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_820052 prefixEnd_820052 := by exact prefixLift 820052
  have htrace : WordTrace (prefixWord ++ tailWord_820052) baseStart_820052 baseEnd_820052 := by
    simpa [prefixWord, tailWord_820052, baseEnd_820052] using wordTrace_append hprefix tailTrace_820052
  have hstable : (prefixWord ++ tailWord_820052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820052).length < 2 ^ (prefixWord ++ tailWord_820052).sum := by decide
  have hdescent : baseEnd_820052 < baseStart_820052 := by decide
  rcases family_descends (prefixWord ++ tailWord_820052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820066 : List Nat := [3, 3, 2, 1, 3, 1, 1, 3, 4]
def baseStart_820066 : Nat := 118140960795 + 820066 * 2 ^ 59
def prefixEnd_820066 : Nat := 4983230072969 + 3 ^ 40 * 820066 * 2
def baseEnd_820066 : Nat := 187150233960041654090485

theorem tailTrace_820066 : CollatzResearch.WordTrace tailWord_820066 prefixEnd_820066 187150233960041654090485 := by
  unfold tailWord_820066
  simp only [CollatzResearch.WordTrace]
  refine ⟨7477566061762103241868013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19940176164698941978314701 7477566061762103241868013)
  ·
    refine ⟨2804087273160788715700505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7477566061762103241868013 2804087273160788715700505)
    ·
      refine ⟨2103065454870591536775379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2804087273160788715700505 2103065454870591536775379)
      ·
        refine ⟨3154598182305887305163069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2103065454870591536775379 3154598182305887305163069)
        ·
          refine ⟨1182974318364707739436151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3154598182305887305163069 1182974318364707739436151)
          ·
            refine ⟨1774461477547061609154227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1182974318364707739436151 1774461477547061609154227)
            ·
              refine ⟨2661692216320592413731341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1774461477547061609154227 2661692216320592413731341)
              ·
                refine ⟨998134581120222155149253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2661692216320592413731341 998134581120222155149253)
                ·
                  refine ⟨187150233960041654090485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 998134581120222155149253 187150233960041654090485)
                  ·
                    rfl

theorem cell21_820066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_820066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_820066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_820066 prefixEnd_820066 := by exact prefixLift 820066
  have htrace : WordTrace (prefixWord ++ tailWord_820066) baseStart_820066 baseEnd_820066 := by
    simpa [prefixWord, tailWord_820066, baseEnd_820066] using wordTrace_append hprefix tailTrace_820066
  have hstable : (prefixWord ++ tailWord_820066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820066).length < 2 ^ (prefixWord ++ tailWord_820066).sum := by decide
  have hdescent : baseEnd_820066 < baseStart_820066 := by decide
  rcases family_descends (prefixWord ++ tailWord_820066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820077 : List Nat := [1, 5, 1, 1, 1, 1, 1, 3, 7]
def baseStart_820077 : Nat := 118140960795 + 820077 * 2 ^ 59
def prefixEnd_820077 : Nat := 4983230072969 + 3 ^ 40 * 820077 * 2
def baseEnd_820077 : Nat := 187152744309908079407129

theorem tailTrace_820077 : CollatzResearch.WordTrace tailWord_820077 prefixEnd_820077 187152744309908079407129 := by
  unfold tailWord_820077
  simp only [CollatzResearch.WordTrace]
  refine ⟨29910665450008561846122485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19940443633339041230748323 29910665450008561846122485)
  ·
    refine ⟨2804124885938302673073983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29910665450008561846122485 2804124885938302673073983)
    ·
      refine ⟨4206187328907454009610975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2804124885938302673073983 4206187328907454009610975)
      ·
        refine ⟨6309280993361181014416463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4206187328907454009610975 6309280993361181014416463)
        ·
          refine ⟨9463921490041771521624695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6309280993361181014416463 9463921490041771521624695)
          ·
            refine ⟨14195882235062657282437043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9463921490041771521624695 14195882235062657282437043)
            ·
              refine ⟨21293823352593985923655565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14195882235062657282437043 21293823352593985923655565)
              ·
                refine ⟨7985183757222744721370837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21293823352593985923655565 7985183757222744721370837)
                ·
                  refine ⟨187152744309908079407129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7985183757222744721370837 187152744309908079407129)
                  ·
                    rfl

theorem cell21_820077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_820077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_820077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_820077 prefixEnd_820077 := by exact prefixLift 820077
  have htrace : WordTrace (prefixWord ++ tailWord_820077) baseStart_820077 baseEnd_820077 := by
    simpa [prefixWord, tailWord_820077, baseEnd_820077] using wordTrace_append hprefix tailTrace_820077
  have hstable : (prefixWord ++ tailWord_820077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820077).length < 2 ^ (prefixWord ++ tailWord_820077).sum := by decide
  have hdescent : baseEnd_820077 < baseStart_820077 := by decide
  rcases family_descends (prefixWord ++ tailWord_820077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820091 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 8]
def baseStart_820091 : Nat := 118140960795 + 820091 * 2 ^ 59
def prefixEnd_820091 : Nat := 4983230072969 + 3 ^ 40 * 820091 * 2
def baseEnd_820091 : Nat := 187155939300647166173767

theorem tailTrace_820091 : CollatzResearch.WordTrace tailWord_820091 prefixEnd_820091 187155939300647166173767 := by
  unfold tailWord_820091
  simp only [CollatzResearch.WordTrace]
  refine ⟨29911176071957842237132127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19940784047971894824754751 29911176071957842237132127)
  ·
    refine ⟨44866764107936763355698191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29911176071957842237132127 44866764107936763355698191)
    ·
      refine ⟨67300146161905145033547287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44866764107936763355698191 67300146161905145033547287)
      ·
        refine ⟨100950219242857717550320931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67300146161905145033547287 100950219242857717550320931)
        ·
          refine ⟨151425328864286576325481397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100950219242857717550320931 151425328864286576325481397)
          ·
            refine ⟨14196124581026866530513881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 151425328864286576325481397 14196124581026866530513881)
            ·
              refine ⟨10647093435770149897885411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14196124581026866530513881 10647093435770149897885411)
              ·
                refine ⟨15970640153655224846828117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10647093435770149897885411 15970640153655224846828117)
                ·
                  refine ⟨187155939300647166173767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15970640153655224846828117 187155939300647166173767)
                  ·
                    rfl

theorem cell21_820091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 8].length) (baseStart_820091 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_820091 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_820091 prefixEnd_820091 := by exact prefixLift 820091
  have htrace : WordTrace (prefixWord ++ tailWord_820091) baseStart_820091 baseEnd_820091 := by
    simpa [prefixWord, tailWord_820091, baseEnd_820091] using wordTrace_append hprefix tailTrace_820091
  have hstable : (prefixWord ++ tailWord_820091).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820091).length < 2 ^ (prefixWord ++ tailWord_820091).sum := by decide
  have hdescent : baseEnd_820091 < baseStart_820091 := by decide
  rcases family_descends (prefixWord ++ tailWord_820091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820108 : List Nat := [2, 2, 1, 2, 1, 2, 3, 4, 4]
def baseStart_820108 : Nat := 118140960795 + 820108 * 2 ^ 59
def prefixEnd_820108 : Nat := 4983230072969 + 3 ^ 40 * 820108 * 2
def baseEnd_820108 : Nat := 187159818932258914390399

theorem tailTrace_820108 : CollatzResearch.WordTrace tailWord_820108 prefixEnd_820108 187159818932258914390399 := by
  unfold tailWord_820108
  simp only [CollatzResearch.WordTrace]
  refine ⟨14955898056448127070250489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19941197408597502760333985 14955898056448127070250489)
  ·
    refine ⟨11216923542336095302687867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14955898056448127070250489 11216923542336095302687867)
    ·
      refine ⟨16825385313504142954031801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11216923542336095302687867 16825385313504142954031801)
      ·
        refine ⟨12619038985128107215523851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16825385313504142954031801 12619038985128107215523851)
        ·
          refine ⟨18928558477692160823285777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12619038985128107215523851 18928558477692160823285777)
          ·
            refine ⟨14196418858269120617464333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18928558477692160823285777 14196418858269120617464333)
            ·
              refine ⟨5323657071850920231549125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14196418858269120617464333 5323657071850920231549125)
              ·
                refine ⟨998185700972047543415461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5323657071850920231549125 998185700972047543415461)
                ·
                  refine ⟨187159818932258914390399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 998185700972047543415461 187159818932258914390399)
                  ·
                    rfl

theorem cell21_820108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4, 4].length) (baseStart_820108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_820108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_820108 prefixEnd_820108 := by exact prefixLift 820108
  have htrace : WordTrace (prefixWord ++ tailWord_820108) baseStart_820108 baseEnd_820108 := by
    simpa [prefixWord, tailWord_820108, baseEnd_820108] using wordTrace_append hprefix tailTrace_820108
  have hstable : (prefixWord ++ tailWord_820108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820108).length < 2 ^ (prefixWord ++ tailWord_820108).sum := by decide
  have hdescent : baseEnd_820108 < baseStart_820108 := by decide
  rcases family_descends (prefixWord ++ tailWord_820108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820280 : List Nat := [2, 1, 2, 1, 5, 3, 2, 2, 3]
def baseStart_820280 : Nat := 118140960795 + 820280 * 2 ^ 59
def prefixEnd_820280 : Nat := 4983230072969 + 3 ^ 40 * 820280 * 2
def baseEnd_820280 : Nat := 187199071675624837523381

theorem tailTrace_820280 : CollatzResearch.WordTrace tailWord_820280 prefixEnd_820280 187199071675624837523381 := by
  unfold tailWord_820280
  simp only [CollatzResearch.WordTrace]
  refine ⟨14959034734136563757881147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19945379645515418343841529 14959034734136563757881147)
  ·
    refine ⟨22438552101204845636821721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14959034734136563757881147 22438552101204845636821721)
    ·
      refine ⟨16828914075903634227616291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22438552101204845636821721 16828914075903634227616291)
      ·
        refine ⟨25243371113855451341424437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16828914075903634227616291 25243371113855451341424437)
        ·
          refine ⟨2366566041923948563258541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25243371113855451341424437 2366566041923948563258541)
          ·
            refine ⟨887462265721480711221953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2366566041923948563258541 887462265721480711221953)
            ·
              refine ⟨665596699291110533416465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 887462265721480711221953 665596699291110533416465)
              ·
                refine ⟨499197524468332900062349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 665596699291110533416465 499197524468332900062349)
                ·
                  refine ⟨187199071675624837523381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 499197524468332900062349 187199071675624837523381)
                  ·
                    rfl

theorem cell21_820280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 2, 3].length) (baseStart_820280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_820280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_820280 prefixEnd_820280 := by exact prefixLift 820280
  have htrace : WordTrace (prefixWord ++ tailWord_820280) baseStart_820280 baseEnd_820280 := by
    simpa [prefixWord, tailWord_820280, baseEnd_820280] using wordTrace_append hprefix tailTrace_820280
  have hstable : (prefixWord ++ tailWord_820280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820280).length < 2 ^ (prefixWord ++ tailWord_820280).sum := by decide
  have hdescent : baseEnd_820280 < baseStart_820280 := by decide
  rcases family_descends (prefixWord ++ tailWord_820280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820294 : List Nat := [6, 1, 1, 1, 1, 2, 2, 3, 4]
def baseStart_820294 : Nat := 118140960795 + 820294 * 2 ^ 59
def prefixEnd_820294 : Nat := 4983230072969 + 3 ^ 40 * 820294 * 2
def baseEnd_820294 : Nat := 187202266666363924290019

theorem tailTrace_820294 : CollatzResearch.WordTrace tailWord_820294 prefixEnd_820294 187202266666363924290019 := by
  unfold tailWord_820294
  simp only [CollatzResearch.WordTrace]
  refine ⟨934955627819450247086623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19945720060148271937847957 934955627819450247086623)
  ·
    refine ⟨1402433441729175370629935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 934955627819450247086623 1402433441729175370629935)
    ·
      refine ⟨2103650162593763055944903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1402433441729175370629935 2103650162593763055944903)
      ·
        refine ⟨3155475243890644583917355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2103650162593763055944903 3155475243890644583917355)
        ·
          refine ⟨4733212865835966875876033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3155475243890644583917355 4733212865835966875876033)
          ·
            refine ⟨3549909649376975156907025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4733212865835966875876033 3549909649376975156907025)
            ·
              refine ⟨2662432237032731367680269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3549909649376975156907025 2662432237032731367680269)
              ·
                refine ⟨998412088887274262880101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2662432237032731367680269 998412088887274262880101)
                ·
                  refine ⟨187202266666363924290019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 998412088887274262880101 187202266666363924290019)
                  ·
                    rfl

theorem cell21_820294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_820294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_820294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_820294 prefixEnd_820294 := by exact prefixLift 820294
  have htrace : WordTrace (prefixWord ++ tailWord_820294) baseStart_820294 baseEnd_820294 := by
    simpa [prefixWord, tailWord_820294, baseEnd_820294] using wordTrace_append hprefix tailTrace_820294
  have hstable : (prefixWord ++ tailWord_820294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820294).length < 2 ^ (prefixWord ++ tailWord_820294).sum := by decide
  have hdescent : baseEnd_820294 < baseStart_820294 := by decide
  rcases family_descends (prefixWord ++ tailWord_820294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820319 : List Nat := [1, 1, 2, 3, 1, 1, 4, 2, 6]
def baseStart_820319 : Nat := 118140960795 + 820319 * 2 ^ 59
def prefixEnd_820319 : Nat := 4983230072969 + 3 ^ 40 * 820319 * 2
def baseEnd_820319 : Nat := 187207972006969436373301

theorem tailTrace_820319 : CollatzResearch.WordTrace tailWord_820319 prefixEnd_820319 187207972006969436373301 := by
  unfold tailWord_820319
  simp only [CollatzResearch.WordTrace]
  refine ⟨29919491915131837176432011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19946327943421224784288007 29919491915131837176432011)
  ·
    refine ⟨44879237872697755764648017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29919491915131837176432011 44879237872697755764648017)
    ·
      refine ⟨33659428404523316823486013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44879237872697755764648017 33659428404523316823486013)
      ·
        refine ⟨12622285651696243808807255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33659428404523316823486013 12622285651696243808807255)
        ·
          refine ⟨18933428477544365713210883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12622285651696243808807255 18933428477544365713210883)
          ·
            refine ⟨28400142716316548569816325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18933428477544365713210883 28400142716316548569816325)
            ·
              refine ⟨5325026759309352856840561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28400142716316548569816325 5325026759309352856840561)
              ·
                refine ⟨3993770069482014642630421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5325026759309352856840561 3993770069482014642630421)
                ·
                  refine ⟨187207972006969436373301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3993770069482014642630421 187207972006969436373301)
                  ·
                    rfl

theorem cell21_820319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 6].length) (baseStart_820319 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_820319 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_820319 prefixEnd_820319 := by exact prefixLift 820319
  have htrace : WordTrace (prefixWord ++ tailWord_820319) baseStart_820319 baseEnd_820319 := by
    simpa [prefixWord, tailWord_820319, baseEnd_820319] using wordTrace_append hprefix tailTrace_820319
  have hstable : (prefixWord ++ tailWord_820319).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820319).length < 2 ^ (prefixWord ++ tailWord_820319).sum := by decide
  have hdescent : baseEnd_820319 < baseStart_820319 := by decide
  rcases family_descends (prefixWord ++ tailWord_820319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820426 : List Nat := [3, 1, 2, 1, 3, 2, 2, 7]
def baseStart_820426 : Nat := 118140960795 + 820426 * 2 ^ 59
def prefixEnd_820426 : Nat := 4983230072969 + 3 ^ 40 * 820426 * 2
def baseEnd_820426 : Nat := 62410796954920342696583

theorem tailTrace_820426 : CollatzResearch.WordTrace tailWord_820426 prefixEnd_820426 62410796954920342696583 := by
  unfold tailWord_820426
  simp only [CollatzResearch.WordTrace]
  refine ⟨7480848631436048612644283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19948929683829462967051421 7480848631436048612644283)
  ·
    refine ⟨11221272947154072918966425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7480848631436048612644283 11221272947154072918966425)
    ·
      refine ⟨8415954710365554689224819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11221272947154072918966425 8415954710365554689224819)
      ·
        refine ⟨12623932065548332033837229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8415954710365554689224819 12623932065548332033837229)
        ·
          refine ⟨4733974524580624512688961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12623932065548332033837229 4733974524580624512688961)
          ·
            refine ⟨3550480893435468384516721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4733974524580624512688961 3550480893435468384516721)
            ·
              refine ⟨2662860670076601288387541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3550480893435468384516721 2662860670076601288387541)
              ·
                refine ⟨62410796954920342696583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2662860670076601288387541 62410796954920342696583)
                ·
                  rfl

theorem cell21_820426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 7].length) (baseStart_820426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_820426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_820426 prefixEnd_820426 := by exact prefixLift 820426
  have htrace : WordTrace (prefixWord ++ tailWord_820426) baseStart_820426 baseEnd_820426 := by
    simpa [prefixWord, tailWord_820426, baseEnd_820426] using wordTrace_append hprefix tailTrace_820426
  have hstable : (prefixWord ++ tailWord_820426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820426).length < 2 ^ (prefixWord ++ tailWord_820426).sum := by decide
  have hdescent : baseEnd_820426 < baseStart_820426 := by decide
  rcases family_descends (prefixWord ++ tailWord_820426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820522 : List Nat := [3, 1, 4, 2, 1, 2, 3, 1, 4]
def baseStart_820522 : Nat := 118140960795 + 820522 * 2 ^ 59
def prefixEnd_820522 : Nat := 4983230072969 + 3 ^ 40 * 820522 * 2
def baseEnd_820522 : Nat := 187254299372686194489553

theorem tailTrace_820522 : CollatzResearch.WordTrace tailWord_820522 prefixEnd_820522 187254299372686194489553 := by
  unfold tailWord_820522
  simp only [CollatzResearch.WordTrace]
  refine ⟨7481723983349100711517955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19951263955597601897381213 7481723983349100711517955)
  ·
    refine ⟨11222585975023651067276933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7481723983349100711517955 11222585975023651067276933)
    ·
      refine ⟨2104234870316934575114425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11222585975023651067276933 2104234870316934575114425)
      ·
        refine ⟨1578176152737700931335819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2104234870316934575114425 1578176152737700931335819)
        ·
          refine ⟨2367264229106551397003729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1578176152737700931335819 2367264229106551397003729)
          ·
            refine ⟨1775448171829913547752797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2367264229106551397003729 1775448171829913547752797)
            ·
              refine ⟨665793064436217580407299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1775448171829913547752797 665793064436217580407299)
              ·
                refine ⟨998689596654326370610949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 665793064436217580407299 998689596654326370610949)
                ·
                  refine ⟨187254299372686194489553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 998689596654326370610949 187254299372686194489553)
                  ·
                    rfl

theorem cell21_820522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 1, 4].length) (baseStart_820522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_820522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_820522 prefixEnd_820522 := by exact prefixLift 820522
  have htrace : WordTrace (prefixWord ++ tailWord_820522) baseStart_820522 baseEnd_820522 := by
    simpa [prefixWord, tailWord_820522, baseEnd_820522] using wordTrace_append hprefix tailTrace_820522
  have hstable : (prefixWord ++ tailWord_820522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820522).length < 2 ^ (prefixWord ++ tailWord_820522).sum := by decide
  have hdescent : baseEnd_820522 < baseStart_820522 := by decide
  rcases family_descends (prefixWord ++ tailWord_820522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820533 : List Nat := [1, 3, 3, 1, 2, 2, 2, 2, 5]
def baseStart_820533 : Nat := 118140960795 + 820533 * 2 ^ 59
def prefixEnd_820533 : Nat := 4983230072969 + 3 ^ 40 * 820533 * 2
def baseEnd_820533 : Nat := 187256809722552619806197

theorem tailTrace_820533 : CollatzResearch.WordTrace tailWord_820533 prefixEnd_820533 187256809722552619806197 := by
  unfold tailWord_820533
  simp only [CollatzResearch.WordTrace]
  refine ⟨29927297136356551724722253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19951531424237701149814835 29927297136356551724722253)
  ·
    refine ⟨11222736426133706896770845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29927297136356551724722253 11222736426133706896770845)
    ·
      refine ⟨4208526159800140086289067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11222736426133706896770845 4208526159800140086289067)
      ·
        refine ⟨6312789239700210129433601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4208526159800140086289067 6312789239700210129433601)
        ·
          refine ⟨4734591929775157597075201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6312789239700210129433601 4734591929775157597075201)
          ·
            refine ⟨3550943947331368197806401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4734591929775157597075201 3550943947331368197806401)
            ·
              refine ⟨2663207960498526148354801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3550943947331368197806401 2663207960498526148354801)
              ·
                refine ⟨1997405970373894611266101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2663207960498526148354801 1997405970373894611266101)
                ·
                  refine ⟨187256809722552619806197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1997405970373894611266101 187256809722552619806197)
                  ·
                    rfl

theorem cell21_820533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_820533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_820533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_820533 prefixEnd_820533 := by exact prefixLift 820533
  have htrace : WordTrace (prefixWord ++ tailWord_820533) baseStart_820533 baseEnd_820533 := by
    simpa [prefixWord, tailWord_820533, baseEnd_820533] using wordTrace_append hprefix tailTrace_820533
  have hstable : (prefixWord ++ tailWord_820533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820533).length < 2 ^ (prefixWord ++ tailWord_820533).sum := by decide
  have hdescent : baseEnd_820533 < baseStart_820533 := by decide
  rcases family_descends (prefixWord ++ tailWord_820533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820564 : List Nat := [2, 4, 1, 1, 2, 1, 2, 4, 4]
def baseStart_820564 : Nat := 118140960795 + 820564 * 2 ^ 59
def prefixEnd_820564 : Nat := 4983230072969 + 3 ^ 40 * 820564 * 2
def baseEnd_820564 : Nat := 187263884344903454789467

theorem tailTrace_820564 : CollatzResearch.WordTrace tailWord_820564 prefixEnd_820564 187263884344903454789467 := by
  unfold tailWord_820564
  simp only [CollatzResearch.WordTrace]
  refine ⟨14964213899622122009550373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19952285199496162679400497 14964213899622122009550373)
  ·
    refine ⟨2805790106179147876790695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14964213899622122009550373 2805790106179147876790695)
    ·
      refine ⟨4208685159268721815186043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2805790106179147876790695 4208685159268721815186043)
      ·
        refine ⟨6313027738903082722779065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4208685159268721815186043 6313027738903082722779065)
        ·
          refine ⟨4734770804177312042084299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6313027738903082722779065 4734770804177312042084299)
          ·
            refine ⟨7102156206265968063126449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4734770804177312042084299 7102156206265968063126449)
            ·
              refine ⟨5326617154699476047344837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7102156206265968063126449 5326617154699476047344837)
              ·
                refine ⟨998740716506151758877157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5326617154699476047344837 998740716506151758877157)
                ·
                  refine ⟨187263884344903454789467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 998740716506151758877157 187263884344903454789467)
                  ·
                    rfl

theorem cell21_820564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_820564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_820564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_820564 prefixEnd_820564 := by exact prefixLift 820564
  have htrace : WordTrace (prefixWord ++ tailWord_820564) baseStart_820564 baseEnd_820564 := by
    simpa [prefixWord, tailWord_820564, baseEnd_820564] using wordTrace_append hprefix tailTrace_820564
  have hstable : (prefixWord ++ tailWord_820564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820564).length < 2 ^ (prefixWord ++ tailWord_820564).sum := by decide
  have hdescent : baseEnd_820564 < baseStart_820564 := by decide
  rcases family_descends (prefixWord ++ tailWord_820564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820567 : List Nat := [1, 1, 3, 2, 3, 3, 3, 2, 3]
def baseStart_820567 : Nat := 118140960795 + 820567 * 2 ^ 59
def prefixEnd_820567 : Nat := 4983230072969 + 3 ^ 40 * 820567 * 2
def baseEnd_820567 : Nat := 187264568985776116239461

theorem tailTrace_820567 : CollatzResearch.WordTrace tailWord_820567 prefixEnd_820567 187264568985776116239461 := by
  unfold tailWord_820567
  simp only [CollatzResearch.WordTrace]
  refine ⟨29928537218233375531459955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19952358145488917020973303 29928537218233375531459955)
  ·
    refine ⟨44892805827350063297189933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29928537218233375531459955 44892805827350063297189933)
    ·
      refine ⟨16834802185256273736446225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44892805827350063297189933 16834802185256273736446225)
      ·
        refine ⟨12626101638942205302334669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16834802185256273736446225 12626101638942205302334669)
        ·
          refine ⟨4734788114603326988375501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12626101638942205302334669 4734788114603326988375501)
          ·
            refine ⟨1775545542976247620640813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4734788114603326988375501 1775545542976247620640813)
            ·
              refine ⟨665829578616092857740305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1775545542976247620640813 665829578616092857740305)
              ·
                refine ⟨499372183962069643305229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 665829578616092857740305 499372183962069643305229)
                ·
                  refine ⟨187264568985776116239461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 499372183962069643305229 187264568985776116239461)
                  ·
                    rfl

theorem cell21_820567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 2, 3].length) (baseStart_820567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_820567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_820567 prefixEnd_820567 := by exact prefixLift 820567
  have htrace : WordTrace (prefixWord ++ tailWord_820567) baseStart_820567 baseEnd_820567 := by
    simpa [prefixWord, tailWord_820567, baseEnd_820567] using wordTrace_append hprefix tailTrace_820567
  have hstable : (prefixWord ++ tailWord_820567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820567).length < 2 ^ (prefixWord ++ tailWord_820567).sum := by decide
  have hdescent : baseEnd_820567 < baseStart_820567 := by decide
  rcases family_descends (prefixWord ++ tailWord_820567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820573 : List Nat := [1, 4, 5, 1, 2, 1, 2, 1, 4]
def baseStart_820573 : Nat := 118140960795 + 820573 * 2 ^ 59
def prefixEnd_820573 : Nat := 4983230072969 + 3 ^ 40 * 820573 * 2
def baseEnd_820573 : Nat := 187265938267521439139449

theorem tailTrace_820573 : CollatzResearch.WordTrace tailWord_820573 prefixEnd_820573 187265938267521439139449 := by
  unfold tailWord_820573
  simp only [CollatzResearch.WordTrace]
  refine ⟨29928756056211638556178373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19952504037474425704118915 29928756056211638556178373)
  ·
    refine ⟨5611641760539682229283445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29928756056211638556178373 5611641760539682229283445)
    ·
      refine ⟨526091415050595208995323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5611641760539682229283445 526091415050595208995323)
      ·
        refine ⟨789137122575892813492985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526091415050595208995323 789137122575892813492985)
        ·
          refine ⟨591852841931919610119739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 789137122575892813492985 591852841931919610119739)
          ·
            refine ⟨887779262897879415179609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 591852841931919610119739 887779262897879415179609)
            ·
              refine ⟨665834447173409561384707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 887779262897879415179609 665834447173409561384707)
              ·
                refine ⟨998751670760114342077061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 665834447173409561384707 998751670760114342077061)
                ·
                  refine ⟨187265938267521439139449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 998751670760114342077061 187265938267521439139449)
                  ·
                    rfl

theorem cell21_820573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 1, 4].length) (baseStart_820573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_820573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_820573 prefixEnd_820573 := by exact prefixLift 820573
  have htrace : WordTrace (prefixWord ++ tailWord_820573) baseStart_820573 baseEnd_820573 := by
    simpa [prefixWord, tailWord_820573, baseEnd_820573] using wordTrace_append hprefix tailTrace_820573
  have hstable : (prefixWord ++ tailWord_820573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820573).length < 2 ^ (prefixWord ++ tailWord_820573).sum := by decide
  have hdescent : baseEnd_820573 < baseStart_820573 := by decide
  rcases family_descends (prefixWord ++ tailWord_820573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820592 : List Nat := [2, 1, 1, 1, 4, 2, 2, 1, 7]
def baseStart_820592 : Nat := 118140960795 + 820592 * 2 ^ 59
def prefixEnd_820592 : Nat := 4983230072969 + 3 ^ 40 * 820592 * 2
def baseEnd_820592 : Nat := 187270274326381628322743

theorem tailTrace_820592 : CollatzResearch.WordTrace tailWord_820592 prefixEnd_820592 187270274326381628322743 := by
  unfold tailWord_820592
  simp only [CollatzResearch.WordTrace]
  refine ⟨14964724521571402400560015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19952966028761869867413353 14964724521571402400560015)
  ·
    refine ⟨22447086782357103600840023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14964724521571402400560015 22447086782357103600840023)
    ·
      refine ⟨33670630173535655401260035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22447086782357103600840023 33670630173535655401260035)
      ·
        refine ⟨50505945260303483101890053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33670630173535655401260035 50505945260303483101890053)
        ·
          refine ⟨9469864736306903081604385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50505945260303483101890053 9469864736306903081604385)
          ·
            refine ⟨7102398552230177311203289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9469864736306903081604385 7102398552230177311203289)
            ·
              refine ⟨5326798914172632983402467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7102398552230177311203289 5326798914172632983402467)
              ·
                refine ⟨7990198371258949475103701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5326798914172632983402467 7990198371258949475103701)
                ·
                  refine ⟨187270274326381628322743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7990198371258949475103701 187270274326381628322743)
                  ·
                    rfl

theorem cell21_820592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 7].length) (baseStart_820592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_820592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_820592 prefixEnd_820592 := by exact prefixLift 820592
  have htrace : WordTrace (prefixWord ++ tailWord_820592) baseStart_820592 baseEnd_820592 := by
    simpa [prefixWord, tailWord_820592, baseEnd_820592] using wordTrace_append hprefix tailTrace_820592
  have hstable : (prefixWord ++ tailWord_820592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820592).length < 2 ^ (prefixWord ++ tailWord_820592).sum := by decide
  have hdescent : baseEnd_820592 < baseStart_820592 := by decide
  rcases family_descends (prefixWord ++ tailWord_820592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820750 : List Nat := [4, 1, 1, 2, 4, 2, 2, 1, 4]
def baseStart_820750 : Nat := 118140960795 + 820750 * 2 ^ 59
def prefixEnd_820750 : Nat := 4983230072969 + 3 ^ 40 * 820750 * 2
def baseEnd_820750 : Nat := 187306332079008464689087

theorem tailTrace_820750 : CollatzResearch.WordTrace tailWord_820750 prefixEnd_820750 187306332079008464689087 := by
  unfold tailWord_820750
  simp only [CollatzResearch.WordTrace]
  refine ⟨3741901472071299723171463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19956807851046931856914469 3741901472071299723171463)
  ·
    refine ⟨5612852208106949584757195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3741901472071299723171463 5612852208106949584757195)
    ·
      refine ⟨8419278312160424377135793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5612852208106949584757195 8419278312160424377135793)
      ·
        refine ⟨6314458734120318282851845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8419278312160424377135793 6314458734120318282851845)
        ·
          refine ⟨1183961012647559678034721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6314458734120318282851845 1183961012647559678034721)
          ·
            refine ⟨887970759485669758526041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1183961012647559678034721 887970759485669758526041)
            ·
              refine ⟨665978069614252318894531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 887970759485669758526041 665978069614252318894531)
              ·
                refine ⟨998967104421378478341797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 665978069614252318894531 998967104421378478341797)
                ·
                  refine ⟨187306332079008464689087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 998967104421378478341797 187306332079008464689087)
                  ·
                    rfl

theorem cell21_820750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_820750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_820750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_820750 prefixEnd_820750 := by exact prefixLift 820750
  have htrace : WordTrace (prefixWord ++ tailWord_820750) baseStart_820750 baseEnd_820750 := by
    simpa [prefixWord, tailWord_820750, baseEnd_820750] using wordTrace_append hprefix tailTrace_820750
  have hstable : (prefixWord ++ tailWord_820750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820750).length < 2 ^ (prefixWord ++ tailWord_820750).sum := by decide
  have hdescent : baseEnd_820750 < baseStart_820750 := by decide
  rcases family_descends (prefixWord ++ tailWord_820750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820778 : List Nat := [3, 1, 4, 1, 1, 1, 2, 5, 3]
def baseStart_820778 : Nat := 118140960795 + 820778 * 2 ^ 59
def prefixEnd_820778 : Nat := 4983230072969 + 3 ^ 40 * 820778 * 2
def baseEnd_820778 : Nat := 187312722060486638222363

theorem tailTrace_820778 : CollatzResearch.WordTrace tailWord_820778 prefixEnd_820778 187312722060486638222363 := by
  unfold tailWord_820778
  simp only [CollatzResearch.WordTrace]
  refine ⟨7484058255117239641847747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19957488680312639044927325 7484058255117239641847747)
  ·
    refine ⟨11226087382675859462771621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7484058255117239641847747 11226087382675859462771621)
    ·
      refine ⟨2104891384251723649269679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11226087382675859462771621 2104891384251723649269679)
      ·
        refine ⟨3157337076377585473904519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2104891384251723649269679 3157337076377585473904519)
        ·
          refine ⟨4736005614566378210856779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3157337076377585473904519 4736005614566378210856779)
          ·
            refine ⟨7104008421849567316285169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4736005614566378210856779 7104008421849567316285169)
            ·
              refine ⟨5328006316387175487213877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7104008421849567316285169 5328006316387175487213877)
              ·
                refine ⟨499500592161297701926301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5328006316387175487213877 499500592161297701926301)
                ·
                  refine ⟨187312722060486638222363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 499500592161297701926301 187312722060486638222363)
                  ·
                    rfl

theorem cell21_820778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 5, 3].length) (baseStart_820778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_820778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_820778 prefixEnd_820778 := by exact prefixLift 820778
  have htrace : WordTrace (prefixWord ++ tailWord_820778) baseStart_820778 baseEnd_820778 := by
    simpa [prefixWord, tailWord_820778, baseEnd_820778] using wordTrace_append hprefix tailTrace_820778
  have hstable : (prefixWord ++ tailWord_820778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820778).length < 2 ^ (prefixWord ++ tailWord_820778).sum := by decide
  have hdescent : baseEnd_820778 < baseStart_820778 := by decide
  rcases family_descends (prefixWord ++ tailWord_820778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820789 : List Nat := [1, 3, 3, 1, 1, 12]
def baseStart_820789 : Nat := 118140960795 + 820789 * 2 ^ 59
def prefixEnd_820789 : Nat := 4983230072969 + 3 ^ 40 * 820789 * 2
def baseEnd_820789 : Nat := 6937601200383446797741

theorem tailTrace_820789 : CollatzResearch.WordTrace tailWord_820789 prefixEnd_820789 6937601200383446797741 := by
  unfold tailWord_820789
  simp only [CollatzResearch.WordTrace]
  refine ⟨29936634223429107446041421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19957756148952738297360947 29936634223429107446041421)
  ·
    refine ⟨11226237833785915292265533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29936634223429107446041421 11226237833785915292265533)
    ·
      refine ⟨4209839187669718234599575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11226237833785915292265533 4209839187669718234599575)
      ·
        refine ⟨6314758781504577351899363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4209839187669718234599575 6314758781504577351899363)
        ·
          refine ⟨9472138172256866027849045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6314758781504577351899363 9472138172256866027849045)
          ·
            refine ⟨6937601200383446797741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 9472138172256866027849045 6937601200383446797741)
            ·
              rfl

theorem cell21_820789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 12].length) (baseStart_820789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_820789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_820789 prefixEnd_820789 := by exact prefixLift 820789
  have htrace : WordTrace (prefixWord ++ tailWord_820789) baseStart_820789 baseEnd_820789 := by
    simpa [prefixWord, tailWord_820789, baseEnd_820789] using wordTrace_append hprefix tailTrace_820789
  have hstable : (prefixWord ++ tailWord_820789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820789).length < 2 ^ (prefixWord ++ tailWord_820789).sum := by decide
  have hdescent : baseEnd_820789 < baseStart_820789 := by decide
  rcases family_descends (prefixWord ++ tailWord_820789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820792 : List Nat := [2, 1, 2, 1, 4, 3, 2, 2, 4]
def baseStart_820792 : Nat := 118140960795 + 820792 * 2 ^ 59
def prefixEnd_820792 : Nat := 4983230072969 + 3 ^ 40 * 820792 * 2
def baseEnd_820792 : Nat := 187315917051225724989001

theorem tailTrace_820792 : CollatzResearch.WordTrace tailWord_820792 prefixEnd_820792 187315917051225724989001 := by
  unfold tailWord_820792
  simp only [CollatzResearch.WordTrace]
  refine ⟨14968371821209119479200315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19957829094945492638933753 14968371821209119479200315)
  ·
    refine ⟨22452557731813679218800473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14968371821209119479200315 22452557731813679218800473)
    ·
      refine ⟨16839418298860259414100355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22452557731813679218800473 16839418298860259414100355)
      ·
        refine ⟨25259127448290389121150533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16839418298860259414100355 25259127448290389121150533)
        ·
          refine ⟨4736086396554447960215725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25259127448290389121150533 4736086396554447960215725)
          ·
            refine ⟨1776032398707917985080897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4736086396554447960215725 1776032398707917985080897)
            ·
              refine ⟨1332024299030938488810673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1776032398707917985080897 1332024299030938488810673)
              ·
                refine ⟨999018224273203866608005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1332024299030938488810673 999018224273203866608005)
                ·
                  refine ⟨187315917051225724989001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 999018224273203866608005 187315917051225724989001)
                  ·
                    rfl

theorem cell21_820792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2, 4].length) (baseStart_820792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_820792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_820792 prefixEnd_820792 := by exact prefixLift 820792
  have htrace : WordTrace (prefixWord ++ tailWord_820792) baseStart_820792 baseEnd_820792 := by
    simpa [prefixWord, tailWord_820792, baseEnd_820792] using wordTrace_append hprefix tailTrace_820792
  have hstable : (prefixWord ++ tailWord_820792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820792).length < 2 ^ (prefixWord ++ tailWord_820792).sum := by decide
  have hdescent : baseEnd_820792 < baseStart_820792 := by decide
  rcases family_descends (prefixWord ++ tailWord_820792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820854 : List Nat := [5, 1, 1, 2, 2, 2, 2, 1, 5]
def baseStart_820854 : Nat := 118140960795 + 820854 * 2 ^ 59
def prefixEnd_820854 : Nat := 4983230072969 + 3 ^ 40 * 820854 * 2
def baseEnd_820854 : Nat := 187330066295927394955541

theorem tailTrace_820854 : CollatzResearch.WordTrace tailWord_820854 prefixEnd_820854 187330066295927394955541 := by
  unfold tailWord_820854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1871187810512101471697351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19959336645462415698105077 1871187810512101471697351)
  ·
    refine ⟨2806781715768152207546027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1871187810512101471697351 2806781715768152207546027)
    ·
      refine ⟨4210172573652228311319041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2806781715768152207546027 4210172573652228311319041)
      ·
        refine ⟨3157629430239171233489281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4210172573652228311319041 3157629430239171233489281)
        ·
          refine ⟨2368222072679378425116961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3157629430239171233489281 2368222072679378425116961)
          ·
            refine ⟨1776166554509533818837721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2368222072679378425116961 1776166554509533818837721)
            ·
              refine ⟨1332124915882150364128291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1776166554509533818837721 1332124915882150364128291)
              ·
                refine ⟨1998187373823225546192437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1332124915882150364128291 1998187373823225546192437)
                ·
                  refine ⟨187330066295927394955541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1998187373823225546192437 187330066295927394955541)
                  ·
                    rfl

theorem cell21_820854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_820854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_820854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_820854 prefixEnd_820854 := by exact prefixLift 820854
  have htrace : WordTrace (prefixWord ++ tailWord_820854) baseStart_820854 baseEnd_820854 := by
    simpa [prefixWord, tailWord_820854, baseEnd_820854] using wordTrace_append hprefix tailTrace_820854
  have hstable : (prefixWord ++ tailWord_820854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820854).length < 2 ^ (prefixWord ++ tailWord_820854).sum := by decide
  have hdescent : baseEnd_820854 < baseStart_820854 := by decide
  rcases family_descends (prefixWord ++ tailWord_820854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820927 : List Nat := [1, 1, 2, 2, 2, 3, 3, 3, 4]
def baseStart_820927 : Nat := 118140960795 + 820927 * 2 ^ 59
def prefixEnd_820927 : Nat := 4983230072969 + 3 ^ 40 * 820927 * 2
def baseEnd_820927 : Nat := 187346725890495490238725

theorem tailTrace_820927 : CollatzResearch.WordTrace tailWord_820927 prefixEnd_820927 187346725890495490238725 := by
  unfold tailWord_820927
  simp only [CollatzResearch.WordTrace]
  refine ⟨29941667496929157014565035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19961111664619438009710023 29941667496929157014565035)
  ·
    refine ⟨44912501245393735521847553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29941667496929157014565035 44912501245393735521847553)
    ·
      refine ⟨33684375934045301641385665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44912501245393735521847553 33684375934045301641385665)
      ·
        refine ⟨25263281950533976231039249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33684375934045301641385665 25263281950533976231039249)
        ·
          refine ⟨18947461462900482173279437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25263281950533976231039249 18947461462900482173279437)
          ·
            refine ⟨7105298048587680814979789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18947461462900482173279437 7105298048587680814979789)
            ·
              refine ⟨2664486768220380305617421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7105298048587680814979789 2664486768220380305617421)
              ·
                refine ⟨999182538082642614606533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2664486768220380305617421 999182538082642614606533)
                ·
                  refine ⟨187346725890495490238725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 999182538082642614606533 187346725890495490238725)
                  ·
                    rfl

theorem cell21_820927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4].length) (baseStart_820927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_820927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_820927 prefixEnd_820927 := by exact prefixLift 820927
  have htrace : WordTrace (prefixWord ++ tailWord_820927) baseStart_820927 baseEnd_820927 := by
    simpa [prefixWord, tailWord_820927, baseEnd_820927] using wordTrace_append hprefix tailTrace_820927
  have hstable : (prefixWord ++ tailWord_820927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820927).length < 2 ^ (prefixWord ++ tailWord_820927).sum := by decide
  have hdescent : baseEnd_820927 < baseStart_820927 := by decide
  rcases family_descends (prefixWord ++ tailWord_820927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820986 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 8]
def baseStart_820986 : Nat := 118140960795 + 820986 * 2 ^ 59
def prefixEnd_820986 : Nat := 4983230072969 + 3 ^ 40 * 820986 * 2
def baseEnd_820986 : Nat := 187360190494324498755271

theorem tailTrace_820986 : CollatzResearch.WordTrace tailWord_820986 prefixEnd_820986 187360190494324498755271 := by
  unfold tailWord_820986
  simp only [CollatzResearch.WordTrace]
  refine ⟨7485954850928852522740703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19962546269143606727308541 7485954850928852522740703)
  ·
    refine ⟨11228932276393278784111055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7485954850928852522740703 11228932276393278784111055)
    ·
      refine ⟨16843398414589918176166583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11228932276393278784111055 16843398414589918176166583)
      ·
        refine ⟨25265097621884877264249875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16843398414589918176166583 25265097621884877264249875)
        ·
          refine ⟨37897646432827315896374813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25265097621884877264249875 37897646432827315896374813)
          ·
            refine ⟨14211617412310243461140555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37897646432827315896374813 14211617412310243461140555)
            ·
              refine ⟨21317426118465365191710833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14211617412310243461140555 21317426118465365191710833)
              ·
                refine ⟨15988069588849023893783125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21317426118465365191710833 15988069588849023893783125)
                ·
                  refine ⟨187360190494324498755271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15988069588849023893783125 187360190494324498755271)
                  ·
                    rfl

theorem cell21_820986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_820986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_820986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_820986 prefixEnd_820986 := by exact prefixLift 820986
  have htrace : WordTrace (prefixWord ++ tailWord_820986) baseStart_820986 baseEnd_820986 := by
    simpa [prefixWord, tailWord_820986, baseEnd_820986] using wordTrace_append hprefix tailTrace_820986
  have hstable : (prefixWord ++ tailWord_820986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820986).length < 2 ^ (prefixWord ++ tailWord_820986).sum := by decide
  have hdescent : baseEnd_820986 < baseStart_820986 := by decide
  rcases family_descends (prefixWord ++ tailWord_820986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821012 : List Nat := [2, 4, 4, 1, 2, 1, 1, 2, 4]
def baseStart_821012 : Nat := 118140960795 + 821012 * 2 ^ 59
def prefixEnd_821012 : Nat := 4983230072969 + 3 ^ 40 * 821012 * 2
def baseEnd_821012 : Nat := 187366124048554231321885

theorem tailTrace_821012 : CollatzResearch.WordTrace tailWord_821012 prefixEnd_821012 187366124048554231321885 := by
  unfold tailWord_821012
  simp only [CollatzResearch.WordTrace]
  refine ⟨14972383850810608265704645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19963178467747477687606193 14972383850810608265704645)
  ·
    refine ⟨2807321972026989049819621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14972383850810608265704645 2807321972026989049819621)
    ·
      refine ⟨526372869755060446841179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2807321972026989049819621 526372869755060446841179)
      ·
        refine ⟨789559304632590670261769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526372869755060446841179 789559304632590670261769)
        ·
          refine ⟨592169478474443002696327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 789559304632590670261769 592169478474443002696327)
          ·
            refine ⟨888254217711664504044491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592169478474443002696327 888254217711664504044491)
            ·
              refine ⟨1332381326567496756066737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 888254217711664504044491 1332381326567496756066737)
              ·
                refine ⟨999285994925622567050053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1332381326567496756066737 999285994925622567050053)
                ·
                  refine ⟨187366124048554231321885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 999285994925622567050053 187366124048554231321885)
                  ·
                    rfl

theorem cell21_821012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_821012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_821012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_821012 prefixEnd_821012 := by exact prefixLift 821012
  have htrace : WordTrace (prefixWord ++ tailWord_821012) baseStart_821012 baseEnd_821012 := by
    simpa [prefixWord, tailWord_821012, baseEnd_821012] using wordTrace_append hprefix tailTrace_821012
  have hstable : (prefixWord ++ tailWord_821012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821012).length < 2 ^ (prefixWord ++ tailWord_821012).sum := by decide
  have hdescent : baseEnd_821012 < baseStart_821012 := by decide
  rcases family_descends (prefixWord ++ tailWord_821012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821048 : List Nat := [2, 1, 2, 1, 3, 3, 2, 2, 5]
def baseStart_821048 : Nat := 118140960795 + 821048 * 2 ^ 59
def prefixEnd_821048 : Nat := 4983230072969 + 3 ^ 40 * 821048 * 2
def baseEnd_821048 : Nat := 187374339739026168721811

theorem tailTrace_821048 : CollatzResearch.WordTrace tailWord_821048 prefixEnd_821048 187374339739026168721811 := by
  unfold tailWord_821048
  simp only [CollatzResearch.WordTrace]
  refine ⟨14973040364745397339859899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19964053819660529786479865 14973040364745397339859899)
  ·
    refine ⟨22459560547118096009789849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14973040364745397339859899 22459560547118096009789849)
    ·
      refine ⟨16844670410338572007342387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22459560547118096009789849 16844670410338572007342387)
      ·
        refine ⟨25267005615507858011013581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16844670410338572007342387 25267005615507858011013581)
        ·
          refine ⟨9475127105815446754130093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25267005615507858011013581 9475127105815446754130093)
          ·
            refine ⟨3553172664680792532798785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9475127105815446754130093 3553172664680792532798785)
            ·
              refine ⟨2664879498510594399599089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3553172664680792532798785 2664879498510594399599089)
              ·
                refine ⟨1998659623882945799699317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2664879498510594399599089 1998659623882945799699317)
                ·
                  refine ⟨187374339739026168721811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1998659623882945799699317 187374339739026168721811)
                  ·
                    rfl

theorem cell21_821048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 5].length) (baseStart_821048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_821048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_821048 prefixEnd_821048 := by exact prefixLift 821048
  have htrace : WordTrace (prefixWord ++ tailWord_821048) baseStart_821048 baseEnd_821048 := by
    simpa [prefixWord, tailWord_821048, baseEnd_821048] using wordTrace_append hprefix tailTrace_821048
  have hstable : (prefixWord ++ tailWord_821048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821048).length < 2 ^ (prefixWord ++ tailWord_821048).sum := by decide
  have hdescent : baseEnd_821048 < baseStart_821048 := by decide
  rcases family_descends (prefixWord ++ tailWord_821048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821082 : List Nat := [3, 1, 1, 2, 1, 3, 5, 2, 3]
def baseStart_821082 : Nat := 118140960795 + 821082 * 2 ^ 59
def prefixEnd_821082 : Nat := 4983230072969 + 3 ^ 40 * 821082 * 2
def baseEnd_821082 : Nat := 187382099002249665155075

theorem tailTrace_821082 : CollatzResearch.WordTrace tailWord_821082 prefixEnd_821082 187382099002249665155075 := by
  unfold tailWord_821082
  simp only [CollatzResearch.WordTrace]
  refine ⟨7486830202841904621614375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19964880540911745657638333 7486830202841904621614375)
  ·
    refine ⟨11230245304262856932421563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7486830202841904621614375 11230245304262856932421563)
    ·
      refine ⟨16845367956394285398632345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11230245304262856932421563 16845367956394285398632345)
      ·
        refine ⟨12634025967295714048974259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16845367956394285398632345 12634025967295714048974259)
        ·
          refine ⟨18951038950943571073461389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12634025967295714048974259 18951038950943571073461389)
          ·
            refine ⟨7106639606603839152548021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18951038950943571073461389 7106639606603839152548021)
            ·
              refine ⟨666247463119109920551377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7106639606603839152548021 666247463119109920551377)
              ·
                refine ⟨499685597339332440413533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 666247463119109920551377 499685597339332440413533)
                ·
                  refine ⟨187382099002249665155075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 499685597339332440413533 187382099002249665155075)
                  ·
                    rfl

theorem cell21_821082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 2, 3].length) (baseStart_821082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_821082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_821082 prefixEnd_821082 := by exact prefixLift 821082
  have htrace : WordTrace (prefixWord ++ tailWord_821082) baseStart_821082 baseEnd_821082 := by
    simpa [prefixWord, tailWord_821082, baseEnd_821082] using wordTrace_append hprefix tailTrace_821082
  have hstable : (prefixWord ++ tailWord_821082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821082).length < 2 ^ (prefixWord ++ tailWord_821082).sum := by decide
  have hdescent : baseEnd_821082 < baseStart_821082 := by decide
  rcases family_descends (prefixWord ++ tailWord_821082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821107 : List Nat := [1, 1, 1, 2, 2, 1, 3, 3, 7]
def baseStart_821107 : Nat := 118140960795 + 821107 * 2 ^ 59
def prefixEnd_821107 : Nat := 4983230072969 + 3 ^ 40 * 821107 * 2
def baseEnd_821107 : Nat := 187387804342855177238357

theorem tailTrace_821107 : CollatzResearch.WordTrace tailWord_821107 prefixEnd_821107 187387804342855177238357 := by
  unfold tailWord_821107
  simp only [CollatzResearch.WordTrace]
  refine ⟨29948232636277047756117575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19965488424184698504078383 29948232636277047756117575)
  ·
    refine ⟨44922348954415571634176363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29948232636277047756117575 44922348954415571634176363)
    ·
      refine ⟨67383523431623357451264545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44922348954415571634176363 67383523431623357451264545)
      ·
        refine ⟨50537642573717518088448409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67383523431623357451264545 50537642573717518088448409)
        ·
          refine ⟨37903231930288138566336307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50537642573717518088448409 37903231930288138566336307)
          ·
            refine ⟨56854847895432207849504461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37903231930288138566336307 56854847895432207849504461)
            ·
              refine ⟨21320567960787077943564173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56854847895432207849504461 21320567960787077943564173)
              ·
                refine ⟨7995212985295154228836565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21320567960787077943564173 7995212985295154228836565)
                ·
                  refine ⟨187387804342855177238357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7995212985295154228836565 187387804342855177238357)
                  ·
                    rfl

theorem cell21_821107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 7].length) (baseStart_821107 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_821107 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_821107 prefixEnd_821107 := by exact prefixLift 821107
  have htrace : WordTrace (prefixWord ++ tailWord_821107) baseStart_821107 baseEnd_821107 := by
    simpa [prefixWord, tailWord_821107, baseEnd_821107] using wordTrace_append hprefix tailTrace_821107
  have hstable : (prefixWord ++ tailWord_821107).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821107).length < 2 ^ (prefixWord ++ tailWord_821107).sum := by decide
  have hdescent : baseEnd_821107 < baseStart_821107 := by decide
  rcases family_descends (prefixWord ++ tailWord_821107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821141 : List Nat := [1, 3, 2, 1, 1, 3, 3, 4, 3]
def baseStart_821141 : Nat := 118140960795 + 821141 * 2 ^ 59
def prefixEnd_821141 : Nat := 4983230072969 + 3 ^ 40 * 821141 * 2
def baseEnd_821141 : Nat := 187395563606078673671621

theorem tailTrace_821141 : CollatzResearch.WordTrace tailWord_821141 prefixEnd_821141 187395563606078673671621 := by
  unfold tailWord_821141
  simp only [CollatzResearch.WordTrace]
  refine ⟨29949472718153871562855277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19966315145435914375236851 29949472718153871562855277)
  ·
    refine ⟨11231052269307701836070729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29949472718153871562855277 11231052269307701836070729)
    ·
      refine ⟨8423289201980776377053047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11231052269307701836070729 8423289201980776377053047)
      ·
        refine ⟨12634933802971164565579571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8423289201980776377053047 12634933802971164565579571)
        ·
          refine ⟨18952400704456746848369357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12634933802971164565579571 18952400704456746848369357)
          ·
            refine ⟨7107150264171280068138509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18952400704456746848369357 7107150264171280068138509)
            ·
              refine ⟨2665181349064230025551941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7107150264171280068138509 2665181349064230025551941)
              ·
                refine ⟨499721502949543129790989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2665181349064230025551941 499721502949543129790989)
                ·
                  refine ⟨187395563606078673671621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 499721502949543129790989 187395563606078673671621)
                  ·
                    rfl

theorem cell21_821141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 4, 3].length) (baseStart_821141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_821141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_821141 prefixEnd_821141 := by exact prefixLift 821141
  have htrace : WordTrace (prefixWord ++ tailWord_821141) baseStart_821141 baseEnd_821141 := by
    simpa [prefixWord, tailWord_821141, baseEnd_821141] using wordTrace_append hprefix tailTrace_821141
  have hstable : (prefixWord ++ tailWord_821141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821141).length < 2 ^ (prefixWord ++ tailWord_821141).sum := by decide
  have hdescent : baseEnd_821141 < baseStart_821141 := by decide
  rcases family_descends (prefixWord ++ tailWord_821141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821144 : List Nat := [2, 1, 2, 6, 2, 1, 1, 6]
def baseStart_821144 : Nat := 118140960795 + 821144 * 2 ^ 59
def prefixEnd_821144 : Nat := 4983230072969 + 3 ^ 40 * 821144 * 2
def baseEnd_821144 : Nat := 62465416082317111707205

theorem tailTrace_821144 : CollatzResearch.WordTrace tailWord_821144 prefixEnd_821144 62465416082317111707205 := by
  unfold tailWord_821144
  simp only [CollatzResearch.WordTrace]
  refine ⟨14974791068571501537607243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19966388091428668716809657 14974791068571501537607243)
  ·
    refine ⟨22462186602857252306410865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14974791068571501537607243 22462186602857252306410865)
    ·
      refine ⟨16846639952142939229808149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22462186602857252306410865 16846639952142939229808149)
      ·
        refine ⟨789686247756700276397257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16846639952142939229808149 789686247756700276397257)
        ·
          refine ⟨592264685817525207297943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 789686247756700276397257 592264685817525207297943)
          ·
            refine ⟨888397028726287810946915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592264685817525207297943 888397028726287810946915)
            ·
              refine ⟨1332595543089431716420373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 888397028726287810946915 1332595543089431716420373)
              ·
                refine ⟨62465416082317111707205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1332595543089431716420373 62465416082317111707205)
                ·
                  rfl

theorem cell21_821144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 6].length) (baseStart_821144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_821144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_821144 prefixEnd_821144 := by exact prefixLift 821144
  have htrace : WordTrace (prefixWord ++ tailWord_821144) baseStart_821144 baseEnd_821144 := by
    simpa [prefixWord, tailWord_821144, baseEnd_821144] using wordTrace_append hprefix tailTrace_821144
  have hstable : (prefixWord ++ tailWord_821144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821144).length < 2 ^ (prefixWord ++ tailWord_821144).sum := by decide
  have hdescent : baseEnd_821144 < baseStart_821144 := by decide
  rcases family_descends (prefixWord ++ tailWord_821144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821183 : List Nat := [1, 1, 2, 2, 2, 1, 3, 2, 7]
def baseStart_821183 : Nat := 118140960795 + 821183 * 2 ^ 59
def prefixEnd_821183 : Nat := 4983230072969 + 3 ^ 40 * 821183 * 2
def baseEnd_821183 : Nat := 187405148578295933971535

theorem tailTrace_821183 : CollatzResearch.WordTrace tailWord_821183 prefixEnd_821183 187405148578295933971535 := by
  unfold tailWord_821183
  simp only [CollatzResearch.WordTrace]
  refine ⟨29951004584001712735884203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19967336389334475157256135 29951004584001712735884203)
  ·
    refine ⟨44926506876002569103826305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29951004584001712735884203 44926506876002569103826305)
    ·
      refine ⟨33694880157001926827869729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44926506876002569103826305 33694880157001926827869729)
      ·
        refine ⟨25271160117751445120902297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33694880157001926827869729 25271160117751445120902297)
        ·
          refine ⟨18953370088313583840676723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25271160117751445120902297 18953370088313583840676723)
          ·
            refine ⟨28430055132470375761015085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18953370088313583840676723 28430055132470375761015085)
            ·
              refine ⟨10661270674676390910380657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28430055132470375761015085 10661270674676390910380657)
              ·
                refine ⟨7995953006007293182785493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10661270674676390910380657 7995953006007293182785493)
                ·
                  refine ⟨187405148578295933971535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7995953006007293182785493 187405148578295933971535)
                  ·
                    rfl

theorem cell21_821183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 7].length) (baseStart_821183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_821183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_821183 prefixEnd_821183 := by exact prefixLift 821183
  have htrace : WordTrace (prefixWord ++ tailWord_821183) baseStart_821183 baseEnd_821183 := by
    simpa [prefixWord, tailWord_821183, baseEnd_821183] using wordTrace_append hprefix tailTrace_821183
  have hstable : (prefixWord ++ tailWord_821183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821183).length < 2 ^ (prefixWord ++ tailWord_821183).sum := by decide
  have hdescent : baseEnd_821183 < baseStart_821183 := by decide
  rcases family_descends (prefixWord ++ tailWord_821183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821206 : List Nat := [5, 2, 1, 1, 3, 1, 3, 1, 4]
def baseStart_821206 : Nat := 118140960795 + 821206 * 2 ^ 59
def prefixEnd_821206 : Nat := 4983230072969 + 3 ^ 40 * 821206 * 2
def baseEnd_821206 : Nat := 187410397491653005088155

theorem tailTrace_821206 : CollatzResearch.WordTrace tailWord_821206 prefixEnd_821206 187410397491653005088155 := by
  unfold tailWord_821206
  simp only [CollatzResearch.WordTrace]
  refine ⟨1871990216432399228998217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19967895641945591775980981 1871990216432399228998217)
  ·
    refine ⟨1403992662324299421748663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1871990216432399228998217 1403992662324299421748663)
    ·
      refine ⟨2105988993486449132622995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1403992662324299421748663 2105988993486449132622995)
      ·
        refine ⟨3158983490229673698934493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2105988993486449132622995 3158983490229673698934493)
        ·
          refine ⟨1184618808836127637100435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3158983490229673698934493 1184618808836127637100435)
          ·
            refine ⟨1776928213254191455650653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1184618808836127637100435 1776928213254191455650653)
            ·
              refine ⟨666348079970321795868995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1776928213254191455650653 666348079970321795868995)
              ·
                refine ⟨999522119955482693803493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 666348079970321795868995 999522119955482693803493)
                ·
                  refine ⟨187410397491653005088155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 999522119955482693803493 187410397491653005088155)
                  ·
                    rfl

theorem cell21_821206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_821206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_821206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_821206 prefixEnd_821206 := by exact prefixLift 821206
  have htrace : WordTrace (prefixWord ++ tailWord_821206) baseStart_821206 baseEnd_821206 := by
    simpa [prefixWord, tailWord_821206, baseEnd_821206] using wordTrace_append hprefix tailTrace_821206
  have hstable : (prefixWord ++ tailWord_821206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821206).length < 2 ^ (prefixWord ++ tailWord_821206).sum := by decide
  have hdescent : baseEnd_821206 < baseStart_821206 := by decide
  rcases family_descends (prefixWord ++ tailWord_821206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821304 : List Nat := [2, 1, 2, 1, 15]
def baseStart_821304 : Nat := 118140960795 + 821304 * 2 ^ 59
def prefixEnd_821304 : Nat := 4983230072969 + 3 ^ 40 * 821304 * 2
def baseEnd_821304 : Nat := 2313984721318847067341

theorem tailTrace_821304 : CollatzResearch.WordTrace tailWord_821304 prefixEnd_821304 2313984721318847067341 := by
  unfold tailWord_821304
  simp only [CollatzResearch.WordTrace]
  refine ⟨14977708908281675200519483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19970278544375566934025977 14977708908281675200519483)
  ·
    refine ⟨22466563362422512800779225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14977708908281675200519483 22466563362422512800779225)
    ·
      refine ⟨16849922521816884600584419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22466563362422512800779225 16849922521816884600584419)
      ·
        refine ⟨25274883782725326900876629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16849922521816884600584419 25274883782725326900876629)
        ·
          refine ⟨2313984721318847067341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 25274883782725326900876629 2313984721318847067341)
          ·
            rfl

theorem cell21_821304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 15].length) (baseStart_821304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_821304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_821304 prefixEnd_821304 := by exact prefixLift 821304
  have htrace : WordTrace (prefixWord ++ tailWord_821304) baseStart_821304 baseEnd_821304 := by
    simpa [prefixWord, tailWord_821304, baseEnd_821304] using wordTrace_append hprefix tailTrace_821304
  have hstable : (prefixWord ++ tailWord_821304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821304).length < 2 ^ (prefixWord ++ tailWord_821304).sum := by decide
  have hdescent : baseEnd_821304 < baseStart_821304 := by decide
  rcases family_descends (prefixWord ++ tailWord_821304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821335 : List Nat := [1, 1, 3, 2, 2, 1, 3, 1, 7]
def baseStart_821335 : Nat := 118140960795 + 821335 * 2 ^ 59
def prefixEnd_821335 : Nat := 4983230072969 + 3 ^ 40 * 821335 * 2
def baseEnd_821335 : Nat := 187439837049177447437891

theorem tailTrace_821335 : CollatzResearch.WordTrace tailWord_821335 prefixEnd_821335 187439837049177447437891 := by
  unfold tailWord_821335
  simp only [CollatzResearch.WordTrace]
  refine ⟨29956548479451042695417459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19971032319634028463611639 29956548479451042695417459)
  ·
    refine ⟨44934822719176564043126189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29956548479451042695417459 44934822719176564043126189)
    ·
      refine ⟨16850558519691211516172321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44934822719176564043126189 16850558519691211516172321)
      ·
        refine ⟨12637918889768408637129241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16850558519691211516172321 12637918889768408637129241)
        ·
          refine ⟨9478439167326306477846931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12637918889768408637129241 9478439167326306477846931)
          ·
            refine ⟨14217658750989459716770397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9478439167326306477846931 14217658750989459716770397)
            ·
              refine ⟨5331622031621047393788899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14217658750989459716770397 5331622031621047393788899)
              ·
                refine ⟨7997433047431571090683349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5331622031621047393788899 7997433047431571090683349)
                ·
                  refine ⟨187439837049177447437891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7997433047431571090683349 187439837049177447437891)
                  ·
                    rfl

theorem cell21_821335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 7].length) (baseStart_821335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_821335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_821335 prefixEnd_821335 := by exact prefixLift 821335
  have htrace : WordTrace (prefixWord ++ tailWord_821335) baseStart_821335 baseEnd_821335 := by
    simpa [prefixWord, tailWord_821335, baseEnd_821335] using wordTrace_append hprefix tailTrace_821335
  have hstable : (prefixWord ++ tailWord_821335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821335).length < 2 ^ (prefixWord ++ tailWord_821335).sum := by decide
  have hdescent : baseEnd_821335 < baseStart_821335 := by decide
  rcases family_descends (prefixWord ++ tailWord_821335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821369 : List Nat := [1, 2, 1, 3, 4, 1, 2, 4, 3]
def baseStart_821369 : Nat := 118140960795 + 821369 * 2 ^ 59
def prefixEnd_821369 : Nat := 4983230072969 + 3 ^ 40 * 821369 * 2
def baseEnd_821369 : Nat := 187447596312400943871155

theorem tailTrace_821369 : CollatzResearch.WordTrace tailWord_821369 prefixEnd_821369 187447596312400943871155 := by
  unfold tailWord_821369
  simp only [CollatzResearch.WordTrace]
  refine ⟨29957788561327866502155161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19971859040885244334770107 29957788561327866502155161)
  ·
    refine ⟨22468341420995899876616371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29957788561327866502155161 22468341420995899876616371)
    ·
      refine ⟨33702512131493849814924557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22468341420995899876616371 33702512131493849814924557)
      ·
        refine ⟨12638442049310193680596709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33702512131493849814924557 12638442049310193680596709)
        ·
          refine ⟨2369707884245661315111883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12638442049310193680596709 2369707884245661315111883)
          ·
            refine ⟨3554561826368491972667825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2369707884245661315111883 3554561826368491972667825)
            ·
              refine ⟨2665921369776368979500869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3554561826368491972667825 2665921369776368979500869)
              ·
                refine ⟨499860256833069183656413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2665921369776368979500869 499860256833069183656413)
                ·
                  refine ⟨187447596312400943871155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 499860256833069183656413 187447596312400943871155)
                  ·
                    rfl

theorem cell21_821369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 4, 3].length) (baseStart_821369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_821369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_821369 prefixEnd_821369 := by exact prefixLift 821369
  have htrace : WordTrace (prefixWord ++ tailWord_821369) baseStart_821369 baseEnd_821369 := by
    simpa [prefixWord, tailWord_821369, baseEnd_821369] using wordTrace_append hprefix tailTrace_821369
  have hstable : (prefixWord ++ tailWord_821369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821369).length < 2 ^ (prefixWord ++ tailWord_821369).sum := by decide
  have hdescent : baseEnd_821369 < baseStart_821369 := by decide
  rcases family_descends (prefixWord ++ tailWord_821369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821479 : List Nat := [1, 1, 5, 3, 1, 3, 2, 2, 3]
def baseStart_821479 : Nat := 118140960795 + 821479 * 2 ^ 59
def prefixEnd_821479 : Nat := 4983230072969 + 3 ^ 40 * 821479 * 2
def baseEnd_821479 : Nat := 187472699811065197037597

theorem tailTrace_821479 : CollatzResearch.WordTrace tailWord_821479 prefixEnd_821479 187472699811065197037597 := by
  unfold tailWord_821479
  simp only [CollatzResearch.WordTrace]
  refine ⟨29961800590929355288659491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19974533727286236859106327 29961800590929355288659491)
  ·
    refine ⟨44942700886394032932989237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29961800590929355288659491 44942700886394032932989237)
    ·
      refine ⟨4213378208099440587467741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44942700886394032932989237 4213378208099440587467741)
      ·
        refine ⟨1580016828037290220300403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4213378208099440587467741 1580016828037290220300403)
        ·
          refine ⟨2370025242055935330450605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1580016828037290220300403 2370025242055935330450605)
          ·
            refine ⟨888759465770975748918977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2370025242055935330450605 888759465770975748918977)
            ·
              refine ⟨666569599328231811689233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 888759465770975748918977 666569599328231811689233)
              ·
                refine ⟨499927199496173858766925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 666569599328231811689233 499927199496173858766925)
                ·
                  refine ⟨187472699811065197037597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 499927199496173858766925 187472699811065197037597)
                  ·
                    rfl

theorem cell21_821479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 2, 3].length) (baseStart_821479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_821479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_821479 prefixEnd_821479 := by exact prefixLift 821479
  have htrace : WordTrace (prefixWord ++ tailWord_821479) baseStart_821479 baseEnd_821479 := by
    simpa [prefixWord, tailWord_821479, baseEnd_821479] using wordTrace_append hprefix tailTrace_821479
  have hstable : (prefixWord ++ tailWord_821479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821479).length < 2 ^ (prefixWord ++ tailWord_821479).sum := by decide
  have hdescent : baseEnd_821479 < baseStart_821479 := by decide
  rcases family_descends (prefixWord ++ tailWord_821479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821490 : List Nat := [3, 2, 1, 3, 2, 3, 1, 6]
def baseStart_821490 : Nat := 118140960795 + 821490 * 2 ^ 59
def prefixEnd_821490 : Nat := 4983230072969 + 3 ^ 40 * 821490 * 2
def baseEnd_821490 : Nat := 62491736720310540784747

theorem tailTrace_821490 : CollatzResearch.WordTrace tailWord_821490 prefixEnd_821490 62491736720310540784747 := by
  unfold tailWord_821490
  simp only [CollatzResearch.WordTrace]
  refine ⟨7490550448472376041827481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19974801195926336111539949 7490550448472376041827481)
  ·
    refine ⟨5617912836354282031370611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7490550448472376041827481 5617912836354282031370611)
    ·
      refine ⟨8426869254531423047055917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5617912836354282031370611 8426869254531423047055917)
      ·
        refine ⟨3160075970449283642645969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8426869254531423047055917 3160075970449283642645969)
        ·
          refine ⟨2370056977836962731984477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3160075970449283642645969 2370056977836962731984477)
          ·
            refine ⟨888771366688861024494179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2370056977836962731984477 888771366688861024494179)
            ·
              refine ⟨1333157050033291536741269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 888771366688861024494179 1333157050033291536741269)
              ·
                refine ⟨62491736720310540784747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1333157050033291536741269 62491736720310540784747)
                ·
                  rfl

theorem cell21_821490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 6].length) (baseStart_821490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_821490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_821490 prefixEnd_821490 := by exact prefixLift 821490
  have htrace : WordTrace (prefixWord ++ tailWord_821490) baseStart_821490 baseEnd_821490 := by
    simpa [prefixWord, tailWord_821490, baseEnd_821490] using wordTrace_append hprefix tailTrace_821490
  have hstable : (prefixWord ++ tailWord_821490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821490).length < 2 ^ (prefixWord ++ tailWord_821490).sum := by decide
  have hdescent : baseEnd_821490 < baseStart_821490 := by decide
  rcases family_descends (prefixWord ++ tailWord_821490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821518 : List Nat := [4, 1, 1, 2, 1, 2, 2, 2, 6]
def baseStart_821518 : Nat := 118140960795 + 821518 * 2 ^ 59
def prefixEnd_821518 : Nat := 4983230072969 + 3 ^ 40 * 821518 * 2
def baseEnd_821518 : Nat := 187481600142409795887517

theorem tailTrace_821518 : CollatzResearch.WordTrace tailWord_821518 prefixEnd_821518 187481600142409795887517 := by
  unfold tailWord_821518
  simp only [CollatzResearch.WordTrace]
  refine ⟨3745402879723508118666151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19975482025192043299552805 3745402879723508118666151)
  ·
    refine ⟨5618104319585262177999227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3745402879723508118666151 5618104319585262177999227)
    ·
      refine ⟨8427156479377893266998841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5618104319585262177999227 8427156479377893266998841)
      ·
        refine ⟨6320367359533419950249131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8427156479377893266998841 6320367359533419950249131)
        ·
          refine ⟨9480551039300129925373697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6320367359533419950249131 9480551039300129925373697)
          ·
            refine ⟨7110413279475097444030273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9480551039300129925373697 7110413279475097444030273)
            ·
              refine ⟨5332809959606323083022705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7110413279475097444030273 5332809959606323083022705)
              ·
                refine ⟨3999607469704742312267029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5332809959606323083022705 3999607469704742312267029)
                ·
                  refine ⟨187481600142409795887517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3999607469704742312267029 187481600142409795887517)
                  ·
                    rfl

theorem cell21_821518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_821518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_821518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_821518 prefixEnd_821518 := by exact prefixLift 821518
  have htrace : WordTrace (prefixWord ++ tailWord_821518) baseStart_821518 baseEnd_821518 := by
    simpa [prefixWord, tailWord_821518, baseEnd_821518] using wordTrace_append hprefix tailTrace_821518
  have hstable : (prefixWord ++ tailWord_821518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821518).length < 2 ^ (prefixWord ++ tailWord_821518).sum := by decide
  have hdescent : baseEnd_821518 < baseStart_821518 := by decide
  rcases family_descends (prefixWord ++ tailWord_821518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821521 : List Nat := [1, 2, 2, 1, 1, 6, 2, 3, 3]
def baseStart_821521 : Nat := 118140960795 + 821521 * 2 ^ 59
def prefixEnd_821521 : Nat := 4983230072969 + 3 ^ 40 * 821521 * 2
def baseEnd_821521 : Nat := 187482284783282457337511

theorem tailTrace_821521 : CollatzResearch.WordTrace tailWord_821521 prefixEnd_821521 187482284783282457337511 := by
  unfold tailWord_821521
  simp only [CollatzResearch.WordTrace]
  refine ⟨29963332456777196461688417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19975554971184797641125611 29963332456777196461688417)
  ·
    refine ⟨22472499342582897346266313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29963332456777196461688417 22472499342582897346266313)
    ·
      refine ⟨16854374506937173009699735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22472499342582897346266313 16854374506937173009699735)
      ·
        refine ⟨25281561760405759514549603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16854374506937173009699735 25281561760405759514549603)
        ·
          refine ⟨37922342640608639271824405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25281561760405759514549603 37922342640608639271824405)
          ·
            refine ⟨1777609811278529965866769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 37922342640608639271824405 1777609811278529965866769)
            ·
              refine ⟨1333207358458897474400077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1777609811278529965866769 1333207358458897474400077)
              ·
                refine ⟨499952759422086552900029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1333207358458897474400077 499952759422086552900029)
                ·
                  refine ⟨187482284783282457337511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 499952759422086552900029 187482284783282457337511)
                  ·
                    rfl

theorem cell21_821521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 3, 3].length) (baseStart_821521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_821521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_821521 prefixEnd_821521 := by exact prefixLift 821521
  have htrace : WordTrace (prefixWord ++ tailWord_821521) baseStart_821521 baseEnd_821521 := by
    simpa [prefixWord, tailWord_821521, baseEnd_821521] using wordTrace_append hprefix tailTrace_821521
  have hstable : (prefixWord ++ tailWord_821521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821521).length < 2 ^ (prefixWord ++ tailWord_821521).sum := by decide
  have hdescent : baseEnd_821521 < baseStart_821521 := by decide
  rcases family_descends (prefixWord ++ tailWord_821521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821535 : List Nat := [1, 1, 2, 4, 3, 1, 3, 2, 4]
def baseStart_821535 : Nat := 118140960795 + 821535 * 2 ^ 59
def prefixEnd_821535 : Nat := 4983230072969 + 3 ^ 40 * 821535 * 2
def baseEnd_821535 : Nat := 187485479774021544104149

theorem tailTrace_821535 : CollatzResearch.WordTrace tailWord_821535 prefixEnd_821535 187485479774021544104149 := by
  unfold tailWord_821535
  simp only [CollatzResearch.WordTrace]
  refine ⟨29963843078726476852698059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19975895385817651235132039 29963843078726476852698059)
  ·
    refine ⟨44945764618089715279047089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29963843078726476852698059 44945764618089715279047089)
    ·
      refine ⟨33709323463567286459285317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44945764618089715279047089 33709323463567286459285317)
      ·
        refine ⟨6320498149418866211115997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33709323463567286459285317 6320498149418866211115997)
        ·
          refine ⟨2370186806032074829168499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6320498149418866211115997 2370186806032074829168499)
          ·
            refine ⟨3555280209048112243752749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2370186806032074829168499 3555280209048112243752749)
            ·
              refine ⟨1333230078393042091407281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3555280209048112243752749 1333230078393042091407281)
              ·
                refine ⟨999922558794781568555461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1333230078393042091407281 999922558794781568555461)
                ·
                  refine ⟨187485479774021544104149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 999922558794781568555461 187485479774021544104149)
                  ·
                    rfl

theorem cell21_821535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2, 4].length) (baseStart_821535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_821535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_821535 prefixEnd_821535 := by exact prefixLift 821535
  have htrace : WordTrace (prefixWord ++ tailWord_821535) baseStart_821535 baseEnd_821535 := by
    simpa [prefixWord, tailWord_821535, baseEnd_821535] using wordTrace_append hprefix tailTrace_821535
  have hstable : (prefixWord ++ tailWord_821535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821535).length < 2 ^ (prefixWord ++ tailWord_821535).sum := by decide
  have hdescent : baseEnd_821535 < baseStart_821535 := by decide
  rcases family_descends (prefixWord ++ tailWord_821535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821566 : List Nat := [4, 2, 1, 2, 1, 2, 4, 5]
def baseStart_821566 : Nat := 118140960795 + 821566 * 2 ^ 59
def prefixEnd_821566 : Nat := 4983230072969 + 3 ^ 40 * 821566 * 2
def baseEnd_821566 : Nat := 62497518132124126362473

theorem tailTrace_821566 : CollatzResearch.WordTrace tailWord_821566 prefixEnd_821566 62497518132124126362473 := by
  unfold tailWord_821566
  simp only [CollatzResearch.WordTrace]
  refine ⟨3745621717701771143384569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19976649161076112764717701 3745621717701771143384569)
  ·
    refine ⟨2809216288276328357538427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3745621717701771143384569 2809216288276328357538427)
    ·
      refine ⟨4213824432414492536307641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2809216288276328357538427 4213824432414492536307641)
      ·
        refine ⟨3160368324310869402230731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4213824432414492536307641 3160368324310869402230731)
        ·
          refine ⟨4740552486466304103346097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3160368324310869402230731 4740552486466304103346097)
          ·
            refine ⟨3555414364849728077509573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4740552486466304103346097 3555414364849728077509573)
            ·
              refine ⟨666640193409324014533045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3555414364849728077509573 666640193409324014533045)
              ·
                refine ⟨62497518132124126362473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 666640193409324014533045 62497518132124126362473)
                ·
                  rfl

theorem cell21_821566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_821566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_821566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_821566 prefixEnd_821566 := by exact prefixLift 821566
  have htrace : WordTrace (prefixWord ++ tailWord_821566) baseStart_821566 baseEnd_821566 := by
    simpa [prefixWord, tailWord_821566, baseEnd_821566] using wordTrace_append hprefix tailTrace_821566
  have hstable : (prefixWord ++ tailWord_821566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821566).length < 2 ^ (prefixWord ++ tailWord_821566).sum := by decide
  have hdescent : baseEnd_821566 < baseStart_821566 := by decide
  rcases family_descends (prefixWord ++ tailWord_821566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821572 : List Nat := [2, 3, 4, 1, 3, 1, 1, 3, 3]
def baseStart_821572 : Nat := 118140960795 + 821572 * 2 ^ 59
def prefixEnd_821572 : Nat := 4983230072969 + 3 ^ 40 * 821572 * 2
def baseEnd_821572 : Nat := 187493923678117701987407

theorem tailTrace_821572 : CollatzResearch.WordTrace tailWord_821572 prefixEnd_821572 187493923678117701987407 := by
  unfold tailWord_821572
  simp only [CollatzResearch.WordTrace]
  refine ⟨14982596289796216085897485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19976795053061621447863313 14982596289796216085897485)
  ·
    refine ⟨5618473608673581032211557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14982596289796216085897485 5618473608673581032211557)
    ·
      refine ⟨1053463801626296443539667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5618473608673581032211557 1053463801626296443539667)
      ·
        refine ⟨1580195702439444665309501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1053463801626296443539667 1580195702439444665309501)
        ·
          refine ⟨592573388414791749491063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1580195702439444665309501 592573388414791749491063)
          ·
            refine ⟨888860082622187624236595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592573388414791749491063 888860082622187624236595)
            ·
              refine ⟨1333290123933281436354893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 888860082622187624236595 1333290123933281436354893)
              ·
                refine ⟨499983796474980538633085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1333290123933281436354893 499983796474980538633085)
                ·
                  refine ⟨187493923678117701987407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 499983796474980538633085 187493923678117701987407)
                  ·
                    rfl

theorem cell21_821572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 3, 3].length) (baseStart_821572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_821572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_821572 prefixEnd_821572 := by exact prefixLift 821572
  have htrace : WordTrace (prefixWord ++ tailWord_821572) baseStart_821572 baseEnd_821572 := by
    simpa [prefixWord, tailWord_821572, baseEnd_821572] using wordTrace_append hprefix tailTrace_821572
  have hstable : (prefixWord ++ tailWord_821572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821572).length < 2 ^ (prefixWord ++ tailWord_821572).sum := by decide
  have hdescent : baseEnd_821572 < baseStart_821572 := by decide
  rcases family_descends (prefixWord ++ tailWord_821572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821594 : List Nat := [3, 1, 1, 2, 1, 2, 1, 6, 4]
def baseStart_821594 : Nat := 118140960795 + 821594 * 2 ^ 59
def prefixEnd_821594 : Nat := 4983230072969 + 3 ^ 40 * 821594 * 2
def baseEnd_821594 : Nat := 187498944377850552620695

theorem tailTrace_821594 : CollatzResearch.WordTrace tailWord_821594 prefixEnd_821594 187498944377850552620695 := by
  unfold tailWord_821594
  simp only [CollatzResearch.WordTrace]
  refine ⟨7491498746378182482273959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19977329990341819952730557 7491498746378182482273959)
  ·
    refine ⟨11237248119567273723410939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7491498746378182482273959 11237248119567273723410939)
    ·
      refine ⟨16855872179350910585116409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11237248119567273723410939 16855872179350910585116409)
      ·
        refine ⟨12641904134513182938837307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16855872179350910585116409 12641904134513182938837307)
        ·
          refine ⟨18962856201769774408255961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12641904134513182938837307 18962856201769774408255961)
          ·
            refine ⟨14222142151327330806191971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18962856201769774408255961 14222142151327330806191971)
            ·
              refine ⟨21333213226990996209287957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14222142151327330806191971 21333213226990996209287957)
              ·
                refine ⟨999994370015202947310373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21333213226990996209287957 999994370015202947310373)
                ·
                  refine ⟨187498944377850552620695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 999994370015202947310373 187498944377850552620695)
                  ·
                    rfl

theorem cell21_821594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6, 4].length) (baseStart_821594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_821594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_821594 prefixEnd_821594 := by exact prefixLift 821594
  have htrace : WordTrace (prefixWord ++ tailWord_821594) baseStart_821594 baseEnd_821594 := by
    simpa [prefixWord, tailWord_821594, baseEnd_821594] using wordTrace_append hprefix tailTrace_821594
  have hstable : (prefixWord ++ tailWord_821594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821594).length < 2 ^ (prefixWord ++ tailWord_821594).sum := by decide
  have hdescent : baseEnd_821594 < baseStart_821594 := by decide
  rcases family_descends (prefixWord ++ tailWord_821594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821642 : List Nat := [3, 1, 2, 5, 2, 8]
def baseStart_821642 : Nat := 118140960795 + 821642 * 2 ^ 59
def prefixEnd_821642 : Nat := 4983230072969 + 3 ^ 40 * 821642 * 2
def baseEnd_821642 : Nat := 6944811060437523548911

theorem tailTrace_821642 : CollatzResearch.WordTrace tailWord_821642 prefixEnd_821642 6944811060437523548911 := by
  unfold tailWord_821642
  simp only [CollatzResearch.WordTrace]
  refine ⟨7491936422334708531710795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19978497126225889417895453 7491936422334708531710795)
  ·
    refine ⟨11237904633502062797566193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7491936422334708531710795 11237904633502062797566193)
    ·
      refine ⟨8428428475126547098174645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11237904633502062797566193 8428428475126547098174645)
      ·
        refine ⟨790165169543113790453873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8428428475126547098174645 790165169543113790453873)
        ·
          refine ⟨592623877157335342840405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 790165169543113790453873 592623877157335342840405)
          ·
            refine ⟨6944811060437523548911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 592623877157335342840405 6944811060437523548911)
            ·
              rfl

theorem cell21_821642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 8].length) (baseStart_821642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_821642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_821642 prefixEnd_821642 := by exact prefixLift 821642
  have htrace : WordTrace (prefixWord ++ tailWord_821642) baseStart_821642 baseEnd_821642 := by
    simpa [prefixWord, tailWord_821642, baseEnd_821642] using wordTrace_append hprefix tailTrace_821642
  have hstable : (prefixWord ++ tailWord_821642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821642).length < 2 ^ (prefixWord ++ tailWord_821642).sum := by decide
  have hdescent : baseEnd_821642 < baseStart_821642 := by decide
  rcases family_descends (prefixWord ++ tailWord_821642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821780 : List Nat := [2, 4, 3, 1, 1, 2, 1, 3, 4]
def baseStart_821780 : Nat := 118140960795 + 821780 * 2 ^ 59
def prefixEnd_821780 : Nat := 4983230072969 + 3 ^ 40 * 821780 * 2
def baseEnd_821780 : Nat := 187541392111955562520315

theorem tailTrace_821780 : CollatzResearch.WordTrace tailWord_821780 prefixEnd_821780 187541392111955562520315 := by
  unfold tailWord_821780
  simp only [CollatzResearch.WordTrace]
  refine ⟨14986389481419441847683397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19981852641892589130244529 14986389481419441847683397)
  ·
    refine ⟨2809948027766145346440637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14986389481419441847683397 2809948027766145346440637)
    ·
      refine ⟨1053730510412304504915239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2809948027766145346440637 1053730510412304504915239)
      ·
        refine ⟨1580595765618456757372859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1053730510412304504915239 1580595765618456757372859)
        ·
          refine ⟨2370893648427685136059289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1580595765618456757372859 2370893648427685136059289)
          ·
            refine ⟨1778170236320763852044467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2370893648427685136059289 1778170236320763852044467)
            ·
              refine ⟨2667255354481145778066701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1778170236320763852044467 2667255354481145778066701)
              ·
                refine ⟨1000220757930429666775013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2667255354481145778066701 1000220757930429666775013)
                ·
                  refine ⟨187541392111955562520315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1000220757930429666775013 187541392111955562520315)
                  ·
                    rfl

theorem cell21_821780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_821780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_821780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_821780 prefixEnd_821780 := by exact prefixLift 821780
  have htrace : WordTrace (prefixWord ++ tailWord_821780) baseStart_821780 baseEnd_821780 := by
    simpa [prefixWord, tailWord_821780, baseEnd_821780] using wordTrace_append hprefix tailTrace_821780
  have hstable : (prefixWord ++ tailWord_821780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821780).length < 2 ^ (prefixWord ++ tailWord_821780).sum := by decide
  have hdescent : baseEnd_821780 < baseStart_821780 := by decide
  rcases family_descends (prefixWord ++ tailWord_821780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821825 : List Nat := [1, 2, 5, 1, 1, 3, 1, 4, 3]
def baseStart_821825 : Nat := 118140960795 + 821825 * 2 ^ 59
def prefixEnd_821825 : Nat := 4983230072969 + 3 ^ 40 * 821825 * 2
def baseEnd_821825 : Nat := 187551661725045484270223

theorem tailTrace_821825 : CollatzResearch.WordTrace tailWord_821825 prefixEnd_821825 187551661725045484270223 := by
  unfold tailWord_821825
  simp only [CollatzResearch.WordTrace]
  refine ⟨29974420247675856380754929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19982946831783904253836619 29974420247675856380754929)
  ·
    refine ⟨22480815185756892285566197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29974420247675856380754929 22480815185756892285566197)
    ·
      refine ⟨2107576423664708651771831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22480815185756892285566197 2107576423664708651771831)
      ·
        refine ⟨3161364635497062977657747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2107576423664708651771831 3161364635497062977657747)
        ·
          refine ⟨4742046953245594466486621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3161364635497062977657747 4742046953245594466486621)
          ·
            refine ⟨1778267607467097924932483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4742046953245594466486621 1778267607467097924932483)
            ·
              refine ⟨2667401411200646887398725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1778267607467097924932483 2667401411200646887398725)
              ·
                refine ⟨500137764600121291387261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2667401411200646887398725 500137764600121291387261)
                ·
                  refine ⟨187551661725045484270223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 500137764600121291387261 187551661725045484270223)
                  ·
                    rfl

theorem cell21_821825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 4, 3].length) (baseStart_821825 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_821825 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_821825 prefixEnd_821825 := by exact prefixLift 821825
  have htrace : WordTrace (prefixWord ++ tailWord_821825) baseStart_821825 baseEnd_821825 := by
    simpa [prefixWord, tailWord_821825, baseEnd_821825] using wordTrace_append hprefix tailTrace_821825
  have hstable : (prefixWord ++ tailWord_821825).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821825).length < 2 ^ (prefixWord ++ tailWord_821825).sum := by decide
  have hdescent : baseEnd_821825 < baseStart_821825 := by decide
  rcases family_descends (prefixWord ++ tailWord_821825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821828 : List Nat := [2, 3, 5, 1, 1, 2, 1, 6]
def baseStart_821828 : Nat := 118140960795 + 821828 * 2 ^ 59
def prefixEnd_821828 : Nat := 4983230072969 + 3 ^ 40 * 821828 * 2
def baseEnd_821828 : Nat := 62517448788639381906739

theorem tailTrace_821828 : CollatzResearch.WordTrace tailWord_821828 prefixEnd_821828 62517448788639381906739 := by
  unfold tailWord_821828
  simp only [CollatzResearch.WordTrace]
  refine ⟨14987264833332493946557069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19983019777776658595409425 14987264833332493946557069)
  ·
    refine ⟨5620224312499685229958901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14987264833332493946557069 5620224312499685229958901)
    ·
      refine ⟨526896029296845490308647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5620224312499685229958901 526896029296845490308647)
      ·
        refine ⟨790344043945268235462971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526896029296845490308647 790344043945268235462971)
        ·
          refine ⟨1185516065917902353194457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 790344043945268235462971 1185516065917902353194457)
          ·
            refine ⟨889137049438426764895843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1185516065917902353194457 889137049438426764895843)
            ·
              refine ⟨1333705574157640147343765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 889137049438426764895843 1333705574157640147343765)
              ·
                refine ⟨62517448788639381906739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1333705574157640147343765 62517448788639381906739)
                ·
                  rfl

theorem cell21_821828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 6].length) (baseStart_821828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_821828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_821828 prefixEnd_821828 := by exact prefixLift 821828
  have htrace : WordTrace (prefixWord ++ tailWord_821828) baseStart_821828 baseEnd_821828 := by
    simpa [prefixWord, tailWord_821828, baseEnd_821828] using wordTrace_append hprefix tailTrace_821828
  have hstable : (prefixWord ++ tailWord_821828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821828).length < 2 ^ (prefixWord ++ tailWord_821828).sum := by decide
  have hdescent : baseEnd_821828 < baseStart_821828 := by decide
  rcases family_descends (prefixWord ++ tailWord_821828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821884 : List Nat := [2, 2, 2, 1, 1, 2, 4, 4, 3]
def baseStart_821884 : Nat := 118140960795 + 821884 * 2 ^ 59
def prefixEnd_821884 : Nat := 4983230072969 + 3 ^ 40 * 821884 * 2
def baseEnd_821884 : Nat := 187565126328874492786769

theorem tailTrace_821884 : CollatzResearch.WordTrace tailWord_821884 prefixEnd_821884 187565126328874492786769 := by
  unfold tailWord_821884
  simp only [CollatzResearch.WordTrace]
  refine ⟨14988286077231054728576353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19984381436308072971435137 14988286077231054728576353)
  ·
    refine ⟨11241214557923291046432265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14988286077231054728576353 11241214557923291046432265)
    ·
      refine ⟨8430910918442468284824199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11241214557923291046432265 8430910918442468284824199)
      ·
        refine ⟨12646366377663702427236299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8430910918442468284824199 12646366377663702427236299)
        ·
          refine ⟨18969549566495553640854449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12646366377663702427236299 18969549566495553640854449)
          ·
            refine ⟨14227162174871665230640837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18969549566495553640854449 14227162174871665230640837)
            ·
              refine ⟨2667592907788437230745157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14227162174871665230640837 2667592907788437230745157)
              ·
                refine ⟨500173670210331980764717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2667592907788437230745157 500173670210331980764717)
                ·
                  refine ⟨187565126328874492786769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 500173670210331980764717 187565126328874492786769)
                  ·
                    rfl

theorem cell21_821884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 4, 3].length) (baseStart_821884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_821884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_821884 prefixEnd_821884 := by exact prefixLift 821884
  have htrace : WordTrace (prefixWord ++ tailWord_821884) baseStart_821884 baseEnd_821884 := by
    simpa [prefixWord, tailWord_821884, baseEnd_821884] using wordTrace_append hprefix tailTrace_821884
  have hstable : (prefixWord ++ tailWord_821884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821884).length < 2 ^ (prefixWord ++ tailWord_821884).sum := by decide
  have hdescent : baseEnd_821884 < baseStart_821884 := by decide
  rcases family_descends (prefixWord ++ tailWord_821884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821912 : List Nat := [2, 1, 2, 4, 1, 1, 3, 7]
def baseStart_821912 : Nat := 118140960795 + 821912 * 2 ^ 59
def prefixEnd_821912 : Nat := 4983230072969 + 3 ^ 40 * 821912 * 2
def baseEnd_821912 : Nat := 62523838770117555440015

theorem tailTrace_821912 : CollatzResearch.WordTrace tailWord_821912 prefixEnd_821912 62523838770117555440015 := by
  unfold tailWord_821912
  simp only [CollatzResearch.WordTrace]
  refine ⟨14988796699180335119585995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19985062265573780159447993 14988796699180335119585995)
  ·
    refine ⟨22483195048770502679378993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14988796699180335119585995 22483195048770502679378993)
    ·
      refine ⟨16862396286577877009534245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22483195048770502679378993 16862396286577877009534245)
      ·
        refine ⟨3161699303733351939287671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16862396286577877009534245 3161699303733351939287671)
        ·
          refine ⟨4742548955600027908931507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3161699303733351939287671 4742548955600027908931507)
          ·
            refine ⟨7113823433400041863397261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4742548955600027908931507 7113823433400041863397261)
            ·
              refine ⟨2667683787525015698773973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7113823433400041863397261 2667683787525015698773973)
              ·
                refine ⟨62523838770117555440015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2667683787525015698773973 62523838770117555440015)
                ·
                  rfl

theorem cell21_821912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 7].length) (baseStart_821912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_821912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_821912 prefixEnd_821912 := by exact prefixLift 821912
  have htrace : WordTrace (prefixWord ++ tailWord_821912) baseStart_821912 baseEnd_821912 := by
    simpa [prefixWord, tailWord_821912, baseEnd_821912] using wordTrace_append hprefix tailTrace_821912
  have hstable : (prefixWord ++ tailWord_821912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821912).length < 2 ^ (prefixWord ++ tailWord_821912).sum := by decide
  have hdescent : baseEnd_821912 < baseStart_821912 := by decide
  rcases family_descends (prefixWord ++ tailWord_821912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822050 : List Nat := [3, 3, 1, 1, 2, 3, 1, 1, 6]
def baseStart_822050 : Nat := 118140960795 + 822050 * 2 ^ 59
def prefixEnd_822050 : Nat := 4983230072969 + 3 ^ 40 * 822050 * 2
def baseEnd_822050 : Nat := 187603009790495093019763

theorem tailTrace_822050 : CollatzResearch.WordTrace tailWord_822050 prefixEnd_822050 187603009790495093019763 := by
  unfold tailWord_822050
  simp only [CollatzResearch.WordTrace]
  refine ⟨7495656667965179951923901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19988417781240479871797069 7495656667965179951923901)
  ·
    refine ⟨2810871250486942481971463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7495656667965179951923901 2810871250486942481971463)
    ·
      refine ⟨4216306875730413722957195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2810871250486942481971463 4216306875730413722957195)
      ·
        refine ⟨6324460313595620584435793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4216306875730413722957195 6324460313595620584435793)
        ·
          refine ⟨4743345235196715438326845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6324460313595620584435793 4743345235196715438326845)
          ·
            refine ⟨1778754463198768289372567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4743345235196715438326845 1778754463198768289372567)
            ·
              refine ⟨2668131694798152434058851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1778754463198768289372567 2668131694798152434058851)
              ·
                refine ⟨4002197542197228651088277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2668131694798152434058851 4002197542197228651088277)
                ·
                  refine ⟨187603009790495093019763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4002197542197228651088277 187603009790495093019763)
                  ·
                    rfl

theorem cell21_822050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_822050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_822050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_822050 prefixEnd_822050 := by exact prefixLift 822050
  have htrace : WordTrace (prefixWord ++ tailWord_822050) baseStart_822050 baseEnd_822050 := by
    simpa [prefixWord, tailWord_822050, baseEnd_822050] using wordTrace_append hprefix tailTrace_822050
  have hstable : (prefixWord ++ tailWord_822050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822050).length < 2 ^ (prefixWord ++ tailWord_822050).sum := by decide
  have hdescent : baseEnd_822050 < baseStart_822050 := by decide
  rcases family_descends (prefixWord ++ tailWord_822050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822067 : List Nat := [1, 1, 1, 2, 6, 2, 3, 1, 4]
def baseStart_822067 : Nat := 118140960795 + 822067 * 2 ^ 59
def prefixEnd_822067 : Nat := 4983230072969 + 3 ^ 40 * 822067 * 2
def baseEnd_822067 : Nat := 187606889422106841236395

theorem tailTrace_822067 : CollatzResearch.WordTrace tailWord_822067 prefixEnd_822067 187606889422106841236395 := by
  unfold tailWord_822067
  simp only [CollatzResearch.WordTrace]
  refine ⟨29983246712799131711064455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19988831141866087807376303 29983246712799131711064455)
  ·
    refine ⟨44974870069198697566596683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29983246712799131711064455 44974870069198697566596683)
    ·
      refine ⟨67462305103798046349895025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44974870069198697566596683 67462305103798046349895025)
      ·
        refine ⟨50596728827848534762421269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67462305103798046349895025 50596728827848534762421269)
        ·
          refine ⟨2371721663805400066988497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 50596728827848534762421269 2371721663805400066988497)
          ·
            refine ⟨1778791247854050050241373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2371721663805400066988497 1778791247854050050241373)
            ·
              refine ⟨667046717945268768840515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1778791247854050050241373 667046717945268768840515)
              ·
                refine ⟨1000570076917903153260773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 667046717945268768840515 1000570076917903153260773)
                ·
                  refine ⟨187606889422106841236395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1000570076917903153260773 187606889422106841236395)
                  ·
                    rfl

theorem cell21_822067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 1, 4].length) (baseStart_822067 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_822067 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_822067 prefixEnd_822067 := by exact prefixLift 822067
  have htrace : WordTrace (prefixWord ++ tailWord_822067) baseStart_822067 baseEnd_822067 := by
    simpa [prefixWord, tailWord_822067, baseEnd_822067] using wordTrace_append hprefix tailTrace_822067
  have hstable : (prefixWord ++ tailWord_822067).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822067).length < 2 ^ (prefixWord ++ tailWord_822067).sum := by decide
  have hdescent : baseEnd_822067 < baseStart_822067 := by decide
  rcases family_descends (prefixWord ++ tailWord_822067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822123 : List Nat := [1, 1, 1, 1, 2, 2, 5, 8]
def baseStart_822123 : Nat := 118140960795 + 822123 * 2 ^ 59
def prefixEnd_822123 : Nat := 4983230072969 + 3 ^ 40 * 822123 * 2
def baseEnd_822123 : Nat := 62539889795021062767649

theorem tailTrace_822123 : CollatzResearch.WordTrace tailWord_822123 prefixEnd_822123 62539889795021062767649 := by
  unfold tailWord_822123
  simp only [CollatzResearch.WordTrace]
  refine ⟨29985289200596253275103023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19990192800397502183402015 29985289200596253275103023)
  ·
    refine ⟨44977933800894379912654535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29985289200596253275103023 44977933800894379912654535)
    ·
      refine ⟨67466900701341569868981803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44977933800894379912654535 67466900701341569868981803)
      ·
        refine ⟨101200351052012354803472705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67466900701341569868981803 101200351052012354803472705)
        ·
          refine ⟨75900263289009266102604529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101200351052012354803472705 75900263289009266102604529)
          ·
            refine ⟨56925197466756949576953397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75900263289009266102604529 56925197466756949576953397)
            ·
              refine ⟨5336737262508464022839381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56925197466756949576953397 5336737262508464022839381)
              ·
                refine ⟨62539889795021062767649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5336737262508464022839381 62539889795021062767649)
                ·
                  rfl

theorem cell21_822123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 8].length) (baseStart_822123 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_822123 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_822123 prefixEnd_822123 := by exact prefixLift 822123
  have htrace : WordTrace (prefixWord ++ tailWord_822123) baseStart_822123 baseEnd_822123 := by
    simpa [prefixWord, tailWord_822123, baseEnd_822123] using wordTrace_append hprefix tailTrace_822123
  have hstable : (prefixWord ++ tailWord_822123).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822123).length < 2 ^ (prefixWord ++ tailWord_822123).sum := by decide
  have hdescent : baseEnd_822123 < baseStart_822123 := by decide
  rcases family_descends (prefixWord ++ tailWord_822123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822185 : List Nat := [1, 2, 1, 1, 1, 1, 5, 5, 4]
def baseStart_822185 : Nat := 118140960795 + 822185 * 2 ^ 59
def prefixEnd_822185 : Nat := 4983230072969 + 3 ^ 40 * 822185 * 2
def baseEnd_822185 : Nat := 187633818629764858269487

theorem tailTrace_822185 : CollatzResearch.WordTrace tailWord_822185 prefixEnd_822185 187633818629764858269487 := by
  unfold tailWord_822185
  simp only [CollatzResearch.WordTrace]
  refine ⟨29987550526371637863860009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19991700350914425242573339 29987550526371637863860009)
  ·
    refine ⟨22490662894778728397895007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29987550526371637863860009 22490662894778728397895007)
    ·
      refine ⟨33735994342168092596842511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22490662894778728397895007 33735994342168092596842511)
      ·
        refine ⟨50603991513252138895263767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33735994342168092596842511 50603991513252138895263767)
        ·
          refine ⟨75905987269878208342895651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50603991513252138895263767 75905987269878208342895651)
          ·
            refine ⟨113858980904817312514343477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75905987269878208342895651 113858980904817312514343477)
            ·
              refine ⟨10674279459826623048219701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113858980904817312514343477 10674279459826623048219701)
              ·
                refine ⟨1000713699358745910770597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10674279459826623048219701 1000713699358745910770597)
                ·
                  refine ⟨187633818629764858269487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1000713699358745910770597 187633818629764858269487)
                  ·
                    rfl

theorem cell21_822185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5, 4].length) (baseStart_822185 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_822185 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_822185 prefixEnd_822185 := by exact prefixLift 822185
  have htrace : WordTrace (prefixWord ++ tailWord_822185) baseStart_822185 baseEnd_822185 := by
    simpa [prefixWord, tailWord_822185, baseEnd_822185] using wordTrace_append hprefix tailTrace_822185
  have hstable : (prefixWord ++ tailWord_822185).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822185).length < 2 ^ (prefixWord ++ tailWord_822185).sum := by decide
  have hdescent : baseEnd_822185 < baseStart_822185 := by decide
  rcases family_descends (prefixWord ++ tailWord_822185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822199 : List Nat := [1, 1, 3, 1, 3, 1, 2, 9]
def baseStart_822199 : Nat := 118140960795 + 822199 * 2 ^ 59
def prefixEnd_822199 : Nat := 4983230072969 + 3 ^ 40 * 822199 * 2
def baseEnd_822199 : Nat := 62545671206834648345375

theorem tailTrace_822199 : CollatzResearch.WordTrace tailWord_822199 prefixEnd_822199 62545671206834648345375 := by
  unfold tailWord_822199
  simp only [CollatzResearch.WordTrace]
  refine ⟨29988061148320918254869651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19992040765547278836579767 29988061148320918254869651)
  ·
    refine ⟨44982091722481377382304477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29988061148320918254869651 44982091722481377382304477)
    ·
      refine ⟨16868284395930516518364179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44982091722481377382304477 16868284395930516518364179)
      ·
        refine ⟨25302426593895774777546269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16868284395930516518364179 25302426593895774777546269)
        ·
          refine ⟨9488409972710915541579851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25302426593895774777546269 9488409972710915541579851)
          ·
            refine ⟨14232614959066373312369777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9488409972710915541579851 14232614959066373312369777)
            ·
              refine ⟨10674461219299779984277333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14232614959066373312369777 10674461219299779984277333)
              ·
                refine ⟨62545671206834648345375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10674461219299779984277333 62545671206834648345375)
                ·
                  rfl

theorem cell21_822199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 9].length) (baseStart_822199 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_822199 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_822199 prefixEnd_822199 := by exact prefixLift 822199
  have htrace : WordTrace (prefixWord ++ tailWord_822199) baseStart_822199 baseEnd_822199 := by
    simpa [prefixWord, tailWord_822199, baseEnd_822199] using wordTrace_append hprefix tailTrace_822199
  have hstable : (prefixWord ++ tailWord_822199).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822199).length < 2 ^ (prefixWord ++ tailWord_822199).sum := by decide
  have hdescent : baseEnd_822199 < baseStart_822199 := by decide
  rcases family_descends (prefixWord ++ tailWord_822199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822205 : List Nat := [1, 4, 1, 2, 4, 1, 2, 3, 3]
def baseStart_822205 : Nat := 118140960795 + 822205 * 2 ^ 59
def prefixEnd_822205 : Nat := 4983230072969 + 3 ^ 40 * 822205 * 2
def baseEnd_822205 : Nat := 187638382902249267936113

theorem tailTrace_822205 : CollatzResearch.WordTrace tailWord_822205 prefixEnd_822205 187638382902249267936113 := by
  unfold tailWord_822205
  simp only [CollatzResearch.WordTrace]
  refine ⟨29988279986299181279588069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19992186657532787519725379 29988279986299181279588069)
  ·
    refine ⟨5622802497431096489922763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29988279986299181279588069 5622802497431096489922763)
    ·
      refine ⟨8434203746146644734884145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5622802497431096489922763 8434203746146644734884145)
      ·
        refine ⟨6325652809609983551163109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8434203746146644734884145 6325652809609983551163109)
        ·
          refine ⟨1186059901801871915843083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6325652809609983551163109 1186059901801871915843083)
          ·
            refine ⟨1779089852702807873764625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1186059901801871915843083 1779089852702807873764625)
            ·
              refine ⟨1334317389527105905323469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1779089852702807873764625 1334317389527105905323469)
              ·
                refine ⟨500369021072664714496301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1334317389527105905323469 500369021072664714496301)
                ·
                  refine ⟨187638382902249267936113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 500369021072664714496301 187638382902249267936113)
                  ·
                    rfl

theorem cell21_822205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 3, 3].length) (baseStart_822205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_822205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_822205 prefixEnd_822205 := by exact prefixLift 822205
  have htrace : WordTrace (prefixWord ++ tailWord_822205) baseStart_822205 baseEnd_822205 := by
    simpa [prefixWord, tailWord_822205, baseEnd_822205] using wordTrace_append hprefix tailTrace_822205
  have hstable : (prefixWord ++ tailWord_822205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822205).length < 2 ^ (prefixWord ++ tailWord_822205).sum := by decide
  have hdescent : baseEnd_822205 < baseStart_822205 := by decide
  rcases family_descends (prefixWord ++ tailWord_822205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822216 : List Nat := [2, 1, 3, 1, 5, 1, 8]
def baseStart_822216 : Nat := 118140960795 + 822216 * 2 ^ 59
def prefixEnd_822216 : Nat := 4983230072969 + 3 ^ 40 * 822216 * 2
def baseEnd_822216 : Nat := 20848988139123965916973

theorem tailTrace_822216 : CollatzResearch.WordTrace tailWord_822216 prefixEnd_822216 20848988139123965916973 := by
  unfold tailWord_822216
  simp only [CollatzResearch.WordTrace]
  refine ⟨14994340594629665079119251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19992454126172886772159001 14994340594629665079119251)
  ·
    refine ⟨22491510891944497618678877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14994340594629665079119251 22491510891944497618678877)
    ·
      refine ⟨8434316584479186607004579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22491510891944497618678877 8434316584479186607004579)
      ·
        refine ⟨12651474876718779910506869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8434316584479186607004579 12651474876718779910506869)
        ·
          refine ⟨1186075769692385616610019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12651474876718779910506869 1186075769692385616610019)
          ·
            refine ⟨1779113654538578424915029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1186075769692385616610019 1779113654538578424915029)
            ·
              refine ⟨20848988139123965916973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1779113654538578424915029 20848988139123965916973)
              ·
                rfl

theorem cell21_822216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 8].length) (baseStart_822216 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_822216 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_822216 prefixEnd_822216 := by exact prefixLift 822216
  have htrace : WordTrace (prefixWord ++ tailWord_822216) baseStart_822216 baseEnd_822216 := by
    simpa [prefixWord, tailWord_822216, baseEnd_822216] using wordTrace_append hprefix tailTrace_822216
  have hstable : (prefixWord ++ tailWord_822216).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822216).length < 2 ^ (prefixWord ++ tailWord_822216).sum := by decide
  have hdescent : baseEnd_822216 < baseStart_822216 := by decide
  rcases family_descends (prefixWord ++ tailWord_822216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822247 : List Nat := [1, 1, 5, 2, 2, 1, 2, 2, 5]
def baseStart_822247 : Nat := 118140960795 + 822247 * 2 ^ 59
def prefixEnd_822247 : Nat := 4983230072969 + 3 ^ 40 * 822247 * 2
def baseEnd_822247 : Nat := 187647967874466528236027

theorem tailTrace_822247 : CollatzResearch.WordTrace tailWord_822247 prefixEnd_822247 187647967874466528236027 := by
  unfold tailWord_822247
  simp only [CollatzResearch.WordTrace]
  refine ⟨29989811852147022452616995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19993207901431348301744663 29989811852147022452616995)
  ·
    refine ⟨44984717778220533678925493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29989811852147022452616995 44984717778220533678925493)
    ·
      refine ⟨4217317291708175032399265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44984717778220533678925493 4217317291708175032399265)
      ·
        refine ⟨3162987968781131274299449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4217317291708175032399265 3162987968781131274299449)
        ·
          refine ⟨2372240976585848455724587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3162987968781131274299449 2372240976585848455724587)
          ·
            refine ⟨3558361464878772683586881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2372240976585848455724587 3558361464878772683586881)
            ·
              refine ⟨2668771098659079512690161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3558361464878772683586881 2668771098659079512690161)
              ·
                refine ⟨2001578323994309634517621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2668771098659079512690161 2001578323994309634517621)
                ·
                  refine ⟨187647967874466528236027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2001578323994309634517621 187647967874466528236027)
                  ·
                    rfl

theorem cell21_822247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 5].length) (baseStart_822247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_822247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_822247 prefixEnd_822247 := by exact prefixLift 822247
  have htrace : WordTrace (prefixWord ++ tailWord_822247) baseStart_822247 baseEnd_822247 := by
    simpa [prefixWord, tailWord_822247, baseEnd_822247] using wordTrace_append hprefix tailTrace_822247
  have hstable : (prefixWord ++ tailWord_822247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822247).length < 2 ^ (prefixWord ++ tailWord_822247).sum := by decide
  have hdescent : baseEnd_822247 < baseStart_822247 := by decide
  rcases family_descends (prefixWord ++ tailWord_822247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822295 : List Nat := [1, 1, 3, 5, 1, 1, 4, 1, 4]
def baseStart_822295 : Nat := 118140960795 + 822295 * 2 ^ 59
def prefixEnd_822295 : Nat := 4983230072969 + 3 ^ 40 * 822295 * 2
def baseEnd_822295 : Nat := 187658922128429111435929

theorem tailTrace_822295 : CollatzResearch.WordTrace tailWord_822295 prefixEnd_822295 187658922128429111435929 := by
  unfold tailWord_822295
  simp only [CollatzResearch.WordTrace]
  refine ⟨29991562555973126650364339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19994375037315417766909559 29991562555973126650364339)
  ·
    refine ⟨44987343833959689975546509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29991562555973126650364339 44987343833959689975546509)
    ·
      refine ⟨16870253937734883740829941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44987343833959689975546509 16870253937734883740829941)
      ·
        refine ⟨1581586306662645350702807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16870253937734883740829941 1581586306662645350702807)
        ·
          refine ⟨2372379459993968026054211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1581586306662645350702807 2372379459993968026054211)
          ·
            refine ⟨3558569189990952039081317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2372379459993968026054211 3558569189990952039081317)
            ·
              refine ⟨667231723123303507327747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3558569189990952039081317 667231723123303507327747)
              ·
                refine ⟨1000847584684955260991621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 667231723123303507327747 1000847584684955260991621)
                ·
                  refine ⟨187658922128429111435929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1000847584684955260991621 187658922128429111435929)
                  ·
                    rfl

theorem cell21_822295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 1, 4].length) (baseStart_822295 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_822295 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_822295 prefixEnd_822295 := by exact prefixLift 822295
  have htrace : WordTrace (prefixWord ++ tailWord_822295) baseStart_822295 baseEnd_822295 := by
    simpa [prefixWord, tailWord_822295, baseEnd_822295] using wordTrace_append hprefix tailTrace_822295
  have hstable : (prefixWord ++ tailWord_822295).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822295).length < 2 ^ (prefixWord ++ tailWord_822295).sum := by decide
  have hdescent : baseEnd_822295 < baseStart_822295 := by decide
  rcases family_descends (prefixWord ++ tailWord_822295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822323 : List Nat := [1, 1, 1, 2, 4, 1, 1, 7, 3]
def baseStart_822323 : Nat := 118140960795 + 822323 * 2 ^ 59
def prefixEnd_822323 : Nat := 4983230072969 + 3 ^ 40 * 822323 * 2
def baseEnd_822323 : Nat := 187665312109907284969205

theorem tailTrace_822323 : CollatzResearch.WordTrace tailWord_822323 prefixEnd_822323 187665312109907284969205 := by
  unfold tailWord_822323
  simp only [CollatzResearch.WordTrace]
  refine ⟨29992583799871687432383623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19995055866581124954922415 29992583799871687432383623)
  ·
    refine ⟨44988875699807531148575435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29992583799871687432383623 44988875699807531148575435)
    ·
      refine ⟨67483313549711296722863153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44988875699807531148575435 67483313549711296722863153)
      ·
        refine ⟨50612485162283472542147365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67483313549711296722863153 50612485162283472542147365)
        ·
          refine ⟨9489840967928151101652631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50612485162283472542147365 9489840967928151101652631)
          ·
            refine ⟨14234761451892226652478947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9489840967928151101652631 14234761451892226652478947)
            ·
              refine ⟨21352142177838339978718421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14234761451892226652478947 21352142177838339978718421)
              ·
                refine ⟨500440832293086093251213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 21352142177838339978718421 500440832293086093251213)
                ·
                  refine ⟨187665312109907284969205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 500440832293086093251213 187665312109907284969205)
                  ·
                    rfl

theorem cell21_822323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 7, 3].length) (baseStart_822323 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_822323 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_822323 prefixEnd_822323 := by exact prefixLift 822323
  have htrace : WordTrace (prefixWord ++ tailWord_822323) baseStart_822323 baseEnd_822323 := by
    simpa [prefixWord, tailWord_822323, baseEnd_822323] using wordTrace_append hprefix tailTrace_822323
  have hstable : (prefixWord ++ tailWord_822323).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822323).length < 2 ^ (prefixWord ++ tailWord_822323).sum := by decide
  have hdescent : baseEnd_822323 < baseStart_822323 := by decide
  rcases family_descends (prefixWord ++ tailWord_822323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822354 : List Nat := [3, 2, 2, 1, 3, 1, 2, 3, 4]
def baseStart_822354 : Nat := 118140960795 + 822354 * 2 ^ 59
def prefixEnd_822354 : Nat := 4983230072969 + 3 ^ 40 * 822354 * 2
def baseEnd_822354 : Nat := 187672386732258119952475

theorem tailTrace_822354 : CollatzResearch.WordTrace tailWord_822354 prefixEnd_822354 187672386732258119952475 := by
  unfold tailWord_822354
  simp only [CollatzResearch.WordTrace]
  refine ⟨7498428615689844931690529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19995809641839586484508077 7498428615689844931690529)
  ·
    refine ⟨5623821461767383698767897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7498428615689844931690529 5623821461767383698767897)
    ·
      refine ⟨4217866096325537774075923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5623821461767383698767897 4217866096325537774075923)
      ·
        refine ⟨6326799144488306661113885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4217866096325537774075923 6326799144488306661113885)
        ·
          refine ⟨2372549679183114997917707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6326799144488306661113885 2372549679183114997917707)
          ·
            refine ⟨3558824518774672496876561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2372549679183114997917707 3558824518774672496876561)
            ·
              refine ⟨2669118389081004372657421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3558824518774672496876561 2669118389081004372657421)
              ·
                refine ⟨1000919395905376639746533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2669118389081004372657421 1000919395905376639746533)
                ·
                  refine ⟨187672386732258119952475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1000919395905376639746533 187672386732258119952475)
                  ·
                    rfl

theorem cell21_822354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_822354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_822354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_822354 prefixEnd_822354 := by exact prefixLift 822354
  have htrace : WordTrace (prefixWord ++ tailWord_822354) baseStart_822354 baseEnd_822354 := by
    simpa [prefixWord, tailWord_822354, baseEnd_822354] using wordTrace_append hprefix tailTrace_822354
  have hstable : (prefixWord ++ tailWord_822354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822354).length < 2 ^ (prefixWord ++ tailWord_822354).sum := by decide
  have hdescent : baseEnd_822354 < baseStart_822354 := by decide
  rcases family_descends (prefixWord ++ tailWord_822354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822368 : List Nat := [2, 1, 1, 3, 2, 2, 5, 5]
def baseStart_822368 : Nat := 118140960795 + 822368 * 2 ^ 59
def prefixEnd_822368 : Nat := 4983230072969 + 3 ^ 40 * 822368 * 2
def baseEnd_822368 : Nat := 62558527240999068906371

theorem tailTrace_822368 : CollatzResearch.WordTrace tailWord_822368 prefixEnd_822368 62558527240999068906371 := by
  unfold tailWord_822368
  simp only [CollatzResearch.WordTrace]
  refine ⟨14997112542354330058885879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19996150056472440078514505 14997112542354330058885879)
  ·
    refine ⟨22495668813531495088328819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14997112542354330058885879 22495668813531495088328819)
    ·
      refine ⟨33743503220297242632493229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22495668813531495088328819 33743503220297242632493229)
      ·
        refine ⟨12653813707611465987184961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33743503220297242632493229 12653813707611465987184961)
        ·
          refine ⟨9490360280708599490388721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12653813707611465987184961 9490360280708599490388721)
          ·
            refine ⟨7117770210531449617791541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9490360280708599490388721 7117770210531449617791541)
            ·
              refine ⟨667290957237323401667957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7117770210531449617791541 667290957237323401667957)
              ·
                refine ⟨62558527240999068906371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 667290957237323401667957 62558527240999068906371)
                ·
                  rfl

theorem cell21_822368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 5].length) (baseStart_822368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_822368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_822368 prefixEnd_822368 := by exact prefixLift 822368
  have htrace : WordTrace (prefixWord ++ tailWord_822368) baseStart_822368 baseEnd_822368 := by
    simpa [prefixWord, tailWord_822368, baseEnd_822368] using wordTrace_append hprefix tailTrace_822368
  have hstable : (prefixWord ++ tailWord_822368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822368).length < 2 ^ (prefixWord ++ tailWord_822368).sum := by decide
  have hdescent : baseEnd_822368 < baseStart_822368 := by decide
  rcases family_descends (prefixWord ++ tailWord_822368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822430 : List Nat := [4, 3, 1, 1, 2, 1, 1, 2, 6]
def baseStart_822430 : Nat := 118140960795 + 822430 * 2 ^ 59
def prefixEnd_822430 : Nat := 4983230072969 + 3 ^ 40 * 822430 * 2
def baseEnd_822430 : Nat := 187689730967698876685653

theorem tailTrace_822430 : CollatzResearch.WordTrace tailWord_822430 prefixEnd_822430 187689730967698876685653 := by
  unfold tailWord_822430
  simp only [CollatzResearch.WordTrace]
  refine ⟨3749560801310505588316093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19997657606989363137685829 3749560801310505588316093)
  ·
    refine ⟨1406085300491439595618535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3749560801310505588316093 1406085300491439595618535)
    ·
      refine ⟨2109127950737159393427803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1406085300491439595618535 2109127950737159393427803)
      ·
        refine ⟨3163691926105739090141705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2109127950737159393427803 3163691926105739090141705)
        ·
          refine ⟨2372768944579304317606279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3163691926105739090141705 2372768944579304317606279)
          ·
            refine ⟨3559153416868956476409419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2372768944579304317606279 3559153416868956476409419)
            ·
              refine ⟨5338730125303434714614129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3559153416868956476409419 5338730125303434714614129)
              ·
                refine ⟨4004047593977576035960597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5338730125303434714614129 4004047593977576035960597)
                ·
                  refine ⟨187689730967698876685653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4004047593977576035960597 187689730967698876685653)
                  ·
                    rfl

theorem cell21_822430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_822430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_822430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_822430 prefixEnd_822430 := by exact prefixLift 822430
  have htrace : WordTrace (prefixWord ++ tailWord_822430) baseStart_822430 baseEnd_822430 := by
    simpa [prefixWord, tailWord_822430, baseEnd_822430] using wordTrace_append hprefix tailTrace_822430
  have hstable : (prefixWord ++ tailWord_822430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822430).length < 2 ^ (prefixWord ++ tailWord_822430).sum := by decide
  have hdescent : baseEnd_822430 < baseStart_822430 := by decide
  rcases family_descends (prefixWord ++ tailWord_822430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822464 : List Nat := [2, 1, 1, 2, 7, 1, 2, 1, 4]
def baseStart_822464 : Nat := 118140960795 + 822464 * 2 ^ 59
def prefixEnd_822464 : Nat := 4983230072969 + 3 ^ 40 * 822464 * 2
def baseEnd_822464 : Nat := 187697490230922373118917

theorem tailTrace_822464 : CollatzResearch.WordTrace tailWord_822464 prefixEnd_822464 187697490230922373118917 := by
  unfold tailWord_822464
  simp only [CollatzResearch.WordTrace]
  refine ⟨14998863246180434256633223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19998484328240579008844297 14998863246180434256633223)
  ·
    refine ⟨22498294869270651384949835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14998863246180434256633223 22498294869270651384949835)
    ·
      refine ⟨33747442303905977077424753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22498294869270651384949835 33747442303905977077424753)
      ·
        refine ⟨25310581727929482808068565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33747442303905977077424753 25310581727929482808068565)
        ·
          refine ⟨593216759248347253314107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 25310581727929482808068565 593216759248347253314107)
          ·
            refine ⟨889825138872520879971161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593216759248347253314107 889825138872520879971161)
            ·
              refine ⟨667368854154390659978371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 889825138872520879971161 667368854154390659978371)
              ·
                refine ⟨1001053281231585989967557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 667368854154390659978371 1001053281231585989967557)
                ·
                  refine ⟨187697490230922373118917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1001053281231585989967557 187697490230922373118917)
                  ·
                    rfl

theorem cell21_822464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 1, 4].length) (baseStart_822464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_822464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_822464 prefixEnd_822464 := by exact prefixLift 822464
  have htrace : WordTrace (prefixWord ++ tailWord_822464) baseStart_822464 baseEnd_822464 := by
    simpa [prefixWord, tailWord_822464, baseEnd_822464] using wordTrace_append hprefix tailTrace_822464
  have hstable : (prefixWord ++ tailWord_822464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822464).length < 2 ^ (prefixWord ++ tailWord_822464).sum := by decide
  have hdescent : baseEnd_822464 < baseStart_822464 := by decide
  rcases family_descends (prefixWord ++ tailWord_822464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822503 : List Nat := [1, 1, 5, 3, 11]
def baseStart_822503 : Nat := 118140960795 + 822503 * 2 ^ 59
def prefixEnd_822503 : Nat := 4983230072969 + 3 ^ 40 * 822503 * 2
def baseEnd_822503 : Nat := 2317362846447740394677

theorem tailTrace_822503 : CollatzResearch.WordTrace tailWord_822503 prefixEnd_822503 2317362846447740394677 := by
  unfold tailWord_822503
  simp only [CollatzResearch.WordTrace]
  refine ⟨29999148939219578173936163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19999432626146385449290775 29999148939219578173936163)
  ·
    refine ⟨44998723408829367260904245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29999148939219578173936163 44998723408829367260904245)
    ·
      refine ⟨4218630319577753180709773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44998723408829367260904245 4218630319577753180709773)
      ·
        refine ⟨1581986369841657442766165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4218630319577753180709773 1581986369841657442766165)
        ·
          refine ⟨2317362846447740394677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1581986369841657442766165 2317362846447740394677)
          ·
            rfl

theorem cell21_822503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 11].length) (baseStart_822503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_822503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_822503 prefixEnd_822503 := by exact prefixLift 822503
  have htrace : WordTrace (prefixWord ++ tailWord_822503) baseStart_822503 baseEnd_822503 := by
    simpa [prefixWord, tailWord_822503, baseEnd_822503] using wordTrace_append hprefix tailTrace_822503
  have hstable : (prefixWord ++ tailWord_822503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822503).length < 2 ^ (prefixWord ++ tailWord_822503).sum := by decide
  have hdescent : baseEnd_822503 < baseStart_822503 := by decide
  rcases family_descends (prefixWord ++ tailWord_822503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822506 : List Nat := [3, 1, 3, 1, 1, 4, 2, 2, 4]
def baseStart_822506 : Nat := 118140960795 + 822506 * 2 ^ 59
def prefixEnd_822506 : Nat := 4983230072969 + 3 ^ 40 * 822506 * 2
def baseEnd_822506 : Nat := 187707075203139633418831

theorem tailTrace_822506 : CollatzResearch.WordTrace tailWord_822506 prefixEnd_822506 187707075203139633418831 := by
  unfold tailWord_822506
  simp only [CollatzResearch.WordTrace]
  refine ⟨7499814589552177421573843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19999505572139139790863581 7499814589552177421573843)
  ·
    refine ⟨11249721884328266132360765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7499814589552177421573843 11249721884328266132360765)
    ·
      refine ⟨4218645706623099799635287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11249721884328266132360765 4218645706623099799635287)
      ·
        refine ⟨6327968559934649699452931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4218645706623099799635287 6327968559934649699452931)
        ·
          refine ⟨9491952839901974549179397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6327968559934649699452931 9491952839901974549179397)
          ·
            refine ⟨1779741157481620227971137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9491952839901974549179397 1779741157481620227971137)
            ·
              refine ⟨1334805868111215170978353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1779741157481620227971137 1334805868111215170978353)
              ·
                refine ⟨1001104401083411378233765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1334805868111215170978353 1001104401083411378233765)
                ·
                  refine ⟨187707075203139633418831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1001104401083411378233765 187707075203139633418831)
                  ·
                    rfl

theorem cell21_822506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2, 4].length) (baseStart_822506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_822506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_822506 prefixEnd_822506 := by exact prefixLift 822506
  have htrace : WordTrace (prefixWord ++ tailWord_822506) baseStart_822506 baseEnd_822506 := by
    simpa [prefixWord, tailWord_822506, baseEnd_822506] using wordTrace_append hprefix tailTrace_822506
  have hstable : (prefixWord ++ tailWord_822506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822506).length < 2 ^ (prefixWord ++ tailWord_822506).sum := by decide
  have hdescent : baseEnd_822506 < baseStart_822506 := by decide
  rcases family_descends (prefixWord ++ tailWord_822506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822509 : List Nat := [1, 5, 1, 2, 2, 1, 4, 2, 3]
def baseStart_822509 : Nat := 118140960795 + 822509 * 2 ^ 59
def prefixEnd_822509 : Nat := 4983230072969 + 3 ^ 40 * 822509 * 2
def baseEnd_822509 : Nat := 187707759844012294868825

theorem tailTrace_822509 : CollatzResearch.WordTrace tailWord_822509 prefixEnd_822509 187707759844012294868825 := by
  unfold tailWord_822509
  simp only [CollatzResearch.WordTrace]
  refine ⟨29999367777197841198654581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19999578518131894132436387 29999367777197841198654581)
  ·
    refine ⟨2812440729112297612373867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29999367777197841198654581 2812440729112297612373867)
    ·
      refine ⟨4218661093668446418560801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2812440729112297612373867 4218661093668446418560801)
      ·
        refine ⟨3163995820251334813920601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4218661093668446418560801 3163995820251334813920601)
        ·
          refine ⟨2372996865188501110440451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3163995820251334813920601 2372996865188501110440451)
          ·
            refine ⟨3559495297782751665660677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2372996865188501110440451 3559495297782751665660677)
            ·
              refine ⟨667405368334265937311377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3559495297782751665660677 667405368334265937311377)
              ·
                refine ⟨500554026250699452983533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 667405368334265937311377 500554026250699452983533)
                ·
                  refine ⟨187707759844012294868825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 500554026250699452983533 187707759844012294868825)
                  ·
                    rfl

theorem cell21_822509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_822509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_822509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_822509 prefixEnd_822509 := by exact prefixLift 822509
  have htrace : WordTrace (prefixWord ++ tailWord_822509) baseStart_822509 baseEnd_822509 := by
    simpa [prefixWord, tailWord_822509, baseEnd_822509] using wordTrace_append hprefix tailTrace_822509
  have hstable : (prefixWord ++ tailWord_822509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822509).length < 2 ^ (prefixWord ++ tailWord_822509).sum := by decide
  have hdescent : baseEnd_822509 < baseStart_822509 := by decide
  rcases family_descends (prefixWord ++ tailWord_822509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822565 : List Nat := [1, 3, 1, 2, 4, 2, 1, 1, 6]
def baseStart_822565 : Nat := 118140960795 + 822565 * 2 ^ 59
def prefixEnd_822565 : Nat := 4983230072969 + 3 ^ 40 * 822565 * 2
def baseEnd_822565 : Nat := 187720539806968641935377

theorem tailTrace_822565 : CollatzResearch.WordTrace tailWord_822565 prefixEnd_822565 187720539806968641935377 := by
  unfold tailWord_822565
  simp only [CollatzResearch.WordTrace]
  refine ⟨30001410264994962762693149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20000940176663308508462099 30001410264994962762693149)
  ·
    refine ⟨11250528849373111036009931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30001410264994962762693149 11250528849373111036009931)
    ·
      refine ⟨16875793274059666554014897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11250528849373111036009931 16875793274059666554014897)
      ·
        refine ⟨12656844955544749915511173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16875793274059666554014897 12656844955544749915511173)
        ·
          refine ⟨2373158429164640609158345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12656844955544749915511173 2373158429164640609158345)
          ·
            refine ⟨1779868821873480456868759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2373158429164640609158345 1779868821873480456868759)
            ·
              refine ⟨2669803232810220685303139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1779868821873480456868759 2669803232810220685303139)
              ·
                refine ⟨4004704849215331027954709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2669803232810220685303139 4004704849215331027954709)
                ·
                  refine ⟨187720539806968641935377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4004704849215331027954709 187720539806968641935377)
                  ·
                    rfl

theorem cell21_822565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 6].length) (baseStart_822565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_822565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_822565 prefixEnd_822565 := by exact prefixLift 822565
  have htrace : WordTrace (prefixWord ++ tailWord_822565) baseStart_822565 baseEnd_822565 := by
    simpa [prefixWord, tailWord_822565, baseEnd_822565] using wordTrace_append hprefix tailTrace_822565
  have hstable : (prefixWord ++ tailWord_822565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822565).length < 2 ^ (prefixWord ++ tailWord_822565).sum := by decide
  have hdescent : baseEnd_822565 < baseStart_822565 := by decide
  rcases family_descends (prefixWord ++ tailWord_822565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822568 : List Nat := [2, 1, 5, 1, 2, 1, 2, 4, 3]
def baseStart_822568 : Nat := 118140960795 + 822568 * 2 ^ 59
def prefixEnd_822568 : Nat := 4983230072969 + 3 ^ 40 * 822568 * 2
def baseEnd_822568 : Nat := 187721224447841303385371

theorem tailTrace_822568 : CollatzResearch.WordTrace tailWord_822568 prefixEnd_822568 187721224447841303385371 := by
  unfold tailWord_822568
  simp only [CollatzResearch.WordTrace]
  refine ⟨15000759841992047137526179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20001013122656062850034905 15000759841992047137526179)
  ·
    refine ⟨22501139762988070706289269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15000759841992047137526179 22501139762988070706289269)
    ·
      refine ⟨2109481852780131628714619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22501139762988070706289269 2109481852780131628714619)
      ·
        refine ⟨3164222779170197443071929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2109481852780131628714619 3164222779170197443071929)
        ·
          refine ⟨2373167084377648082303947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3164222779170197443071929 2373167084377648082303947)
          ·
            refine ⟨3559750626566472123455921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2373167084377648082303947 3559750626566472123455921)
            ·
              refine ⟨2669812969924854092591941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3559750626566472123455921 2669812969924854092591941)
              ·
                refine ⟨500589931860910142360989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2669812969924854092591941 500589931860910142360989)
                ·
                  refine ⟨187721224447841303385371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 500589931860910142360989 187721224447841303385371)
                  ·
                    rfl

theorem cell21_822568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 4, 3].length) (baseStart_822568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_822568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_822568 prefixEnd_822568 := by exact prefixLift 822568
  have htrace : WordTrace (prefixWord ++ tailWord_822568) baseStart_822568 baseEnd_822568 := by
    simpa [prefixWord, tailWord_822568, baseEnd_822568] using wordTrace_append hprefix tailTrace_822568
  have hstable : (prefixWord ++ tailWord_822568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822568).length < 2 ^ (prefixWord ++ tailWord_822568).sum := by decide
  have hdescent : baseEnd_822568 < baseStart_822568 := by decide
  rcases family_descends (prefixWord ++ tailWord_822568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822627 : List Nat := [1, 1, 1, 5, 2, 4, 1, 1, 5]
def baseStart_822627 : Nat := 118140960795 + 822627 * 2 ^ 59
def prefixEnd_822627 : Nat := 4983230072969 + 3 ^ 40 * 822627 * 2
def baseEnd_822627 : Nat := 187734689051670311901917

theorem tailTrace_822627 : CollatzResearch.WordTrace tailWord_822627 prefixEnd_822627 187734689051670311901917 := by
  unfold tailWord_822627
  simp only [CollatzResearch.WordTrace]
  refine ⟨30003671590770347351450135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20002447727180231567633423 30003671590770347351450135)
  ·
    refine ⟨45005507386155521027175203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30003671590770347351450135 45005507386155521027175203)
    ·
      refine ⟨67508261079233281540762805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45005507386155521027175203 67508261079233281540762805)
      ·
        refine ⟨6328899476178120144446513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67508261079233281540762805 6328899476178120144446513)
        ·
          refine ⟨4746674607133590108334885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6328899476178120144446513 4746674607133590108334885)
          ·
            refine ⟨890001488837548145312791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4746674607133590108334885 890001488837548145312791)
            ·
              refine ⟨1335002233256322217969187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 890001488837548145312791 1335002233256322217969187)
              ·
                refine ⟨2002503349884483326953781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1335002233256322217969187 2002503349884483326953781)
                ·
                  refine ⟨187734689051670311901917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2002503349884483326953781 187734689051670311901917)
                  ·
                    rfl

theorem cell21_822627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 5].length) (baseStart_822627 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_822627 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_822627 prefixEnd_822627 := by exact prefixLift 822627
  have htrace : WordTrace (prefixWord ++ tailWord_822627) baseStart_822627 baseEnd_822627 := by
    simpa [prefixWord, tailWord_822627, baseEnd_822627] using wordTrace_append hprefix tailTrace_822627
  have hstable : (prefixWord ++ tailWord_822627).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822627).length < 2 ^ (prefixWord ++ tailWord_822627).sum := by decide
  have hdescent : baseEnd_822627 < baseStart_822627 := by decide
  rcases family_descends (prefixWord ++ tailWord_822627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822776 : List Nat := [2, 1, 2, 1, 1, 5, 1, 2, 6]
def baseStart_822776 : Nat := 118140960795 + 822776 * 2 ^ 59
def prefixEnd_822776 : Nat := 4983230072969 + 3 ^ 40 * 822776 * 2
def baseEnd_822776 : Nat := 187768692881679163918279

theorem tailTrace_822776 : CollatzResearch.WordTrace tailWord_822776 prefixEnd_822776 187768692881679163918279 := by
  unfold tailWord_822776
  simp only [CollatzResearch.WordTrace]
  refine ⟨15004553033615272899312091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20006070711487030532416121 15004553033615272899312091)
  ·
    refine ⟨22506829550422909348968137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15004553033615272899312091 22506829550422909348968137)
    ·
      refine ⟨16880122162817182011726103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22506829550422909348968137 16880122162817182011726103)
      ·
        refine ⟨25320183244225773017589155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16880122162817182011726103 25320183244225773017589155)
        ·
          refine ⟨37980274866338659526383733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25320183244225773017589155 37980274866338659526383733)
          ·
            refine ⟨3560650768719249330598475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37980274866338659526383733 3560650768719249330598475)
            ·
              refine ⟨5340976153078873995897713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3560650768719249330598475 5340976153078873995897713)
              ·
                refine ⟨4005732114809155496923285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5340976153078873995897713 4005732114809155496923285)
                ·
                  refine ⟨187768692881679163918279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4005732114809155496923285 187768692881679163918279)
                  ·
                    rfl

theorem cell21_822776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 6].length) (baseStart_822776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_822776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_822776 prefixEnd_822776 := by exact prefixLift 822776
  have htrace : WordTrace (prefixWord ++ tailWord_822776) baseStart_822776 baseEnd_822776 := by
    simpa [prefixWord, tailWord_822776, baseEnd_822776] using wordTrace_append hprefix tailTrace_822776
  have hstable : (prefixWord ++ tailWord_822776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822776).length < 2 ^ (prefixWord ++ tailWord_822776).sum := by decide
  have hdescent : baseEnd_822776 < baseStart_822776 := by decide
  rcases family_descends (prefixWord ++ tailWord_822776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822782 : List Nat := [4, 2, 2, 3, 2, 1, 7]
def baseStart_822782 : Nat := 118140960795 + 822782 * 2 ^ 59
def prefixEnd_822782 : Nat := 4983230072969 + 3 ^ 40 * 822782 * 2
def baseEnd_822782 : Nat := 20863340240380498535363

theorem tailTrace_822782 : CollatzResearch.WordTrace tailWord_822782 prefixEnd_822782 20863340240380498535363 := by
  unfold tailWord_822782
  simp only [CollatzResearch.WordTrace]
  refine ⟨3751165613151101102917825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20006216603472539215561733 3751165613151101102917825)
  ·
    refine ⟨2813374209863325827188369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3751165613151101102917825 2813374209863325827188369)
    ·
      refine ⟨2110030657397494370391277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2813374209863325827188369 2110030657397494370391277)
      ·
        refine ⟨791261496524060388896729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2110030657397494370391277 791261496524060388896729)
        ·
          refine ⟨593446122393045291672547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 791261496524060388896729 593446122393045291672547)
          ·
            refine ⟨890169183589567937508821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593446122393045291672547 890169183589567937508821)
            ·
              refine ⟨20863340240380498535363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 890169183589567937508821 20863340240380498535363)
              ·
                rfl

theorem cell21_822782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 7].length) (baseStart_822782 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_822782 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_822782 prefixEnd_822782 := by exact prefixLift 822782
  have htrace : WordTrace (prefixWord ++ tailWord_822782) baseStart_822782 baseEnd_822782 := by
    simpa [prefixWord, tailWord_822782, baseEnd_822782] using wordTrace_append hprefix tailTrace_822782
  have hstable : (prefixWord ++ tailWord_822782).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822782).length < 2 ^ (prefixWord ++ tailWord_822782).sum := by decide
  have hdescent : baseEnd_822782 < baseStart_822782 := by decide
  rcases family_descends (prefixWord ++ tailWord_822782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822796 : List Nat := [2, 2, 1, 2, 6, 1, 1, 1, 5]
def baseStart_822796 : Nat := 118140960795 + 822796 * 2 ^ 59
def prefixEnd_822796 : Nat := 4983230072969 + 3 ^ 40 * 822796 * 2
def baseEnd_822796 : Nat := 187773257154163573584905

theorem tailTrace_822796 : CollatzResearch.WordTrace tailWord_822796 prefixEnd_822796 187773257154163573584905 := by
  unfold tailWord_822796
  simp only [CollatzResearch.WordTrace]
  refine ⟨15004917763579044607176121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20006557018105392809568161 15004917763579044607176121)
  ·
    refine ⟨11253688322684283455382091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15004917763579044607176121 11253688322684283455382091)
    ·
      refine ⟨16880532484026425183073137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11253688322684283455382091 16880532484026425183073137)
      ·
        refine ⟨12660399363019818887304853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16880532484026425183073137 12660399363019818887304853)
        ·
          refine ⟨593456220141554010342415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12660399363019818887304853 593456220141554010342415)
          ·
            refine ⟨890184330212331015513623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593456220141554010342415 890184330212331015513623)
            ·
              refine ⟨1335276495318496523270435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 890184330212331015513623 1335276495318496523270435)
              ·
                refine ⟨2002914742977744784905653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1335276495318496523270435 2002914742977744784905653)
                ·
                  refine ⟨187773257154163573584905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2002914742977744784905653 187773257154163573584905)
                  ·
                    rfl

theorem cell21_822796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 5].length) (baseStart_822796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_822796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_822796 prefixEnd_822796 := by exact prefixLift 822796
  have htrace : WordTrace (prefixWord ++ tailWord_822796) baseStart_822796 baseEnd_822796 := by
    simpa [prefixWord, tailWord_822796, baseEnd_822796] using wordTrace_append hprefix tailTrace_822796
  have hstable : (prefixWord ++ tailWord_822796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822796).length < 2 ^ (prefixWord ++ tailWord_822796).sum := by decide
  have hdescent : baseEnd_822796 < baseStart_822796 := by decide
  rcases family_descends (prefixWord ++ tailWord_822796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822821 : List Nat := [1, 3, 1, 2, 2, 1, 1, 3, 7]
def baseStart_822821 : Nat := 118140960795 + 822821 * 2 ^ 59
def prefixEnd_822821 : Nat := 4983230072969 + 3 ^ 40 * 822821 * 2
def baseEnd_822821 : Nat := 187778962494769085668187

theorem tailTrace_822821 : CollatzResearch.WordTrace tailWord_822821 prefixEnd_822821 187778962494769085668187 := by
  unfold tailWord_822821
  simp only [CollatzResearch.WordTrace]
  refine ⟨30010747352067518484012317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20007164901378345656008211 30010747352067518484012317)
  ·
    refine ⟨11254030257025319431504619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30010747352067518484012317 11254030257025319431504619)
    ·
      refine ⟨16881045385537979147256929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11254030257025319431504619 16881045385537979147256929)
      ·
        refine ⟨12660784039153484360442697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16881045385537979147256929 12660784039153484360442697)
        ·
          refine ⟨9495588029365113270332023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12660784039153484360442697 9495588029365113270332023)
          ·
            refine ⟨14243382044047669905498035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9495588029365113270332023 14243382044047669905498035)
            ·
              refine ⟨21365073066071504858247053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14243382044047669905498035 21365073066071504858247053)
              ·
                refine ⟨8011902399776814321842645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21365073066071504858247053 8011902399776814321842645)
                ·
                  refine ⟨187778962494769085668187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8011902399776814321842645 187778962494769085668187)
                  ·
                    rfl

theorem cell21_822821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_822821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_822821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_822821 prefixEnd_822821 := by exact prefixLift 822821
  have htrace : WordTrace (prefixWord ++ tailWord_822821) baseStart_822821 baseEnd_822821 := by
    simpa [prefixWord, tailWord_822821, baseEnd_822821] using wordTrace_append hprefix tailTrace_822821
  have hstable : (prefixWord ++ tailWord_822821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822821).length < 2 ^ (prefixWord ++ tailWord_822821).sum := by decide
  have hdescent : baseEnd_822821 < baseStart_822821 := by decide
  rcases family_descends (prefixWord ++ tailWord_822821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822928 : List Nat := [2, 1, 1, 1, 1, 1, 3, 7, 4]
def baseStart_822928 : Nat := 118140960795 + 822928 * 2 ^ 59
def prefixEnd_822928 : Nat := 4983230072969 + 3 ^ 40 * 822928 * 2
def baseEnd_822928 : Nat := 187803381352560677384635

theorem tailTrace_822928 : CollatzResearch.WordTrace tailWord_822928 prefixEnd_822928 187803381352560677384635 := by
  unfold tailWord_822928
  simp only [CollatzResearch.WordTrace]
  refine ⟨15007324981339937879078719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20009766641786583838771625 15007324981339937879078719)
  ·
    refine ⟨22510987472009906818618079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15007324981339937879078719 22510987472009906818618079)
    ·
      refine ⟨33766481208014860227927119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22510987472009906818618079 33766481208014860227927119)
      ·
        refine ⟨50649721812022290341890679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33766481208014860227927119 50649721812022290341890679)
        ·
          refine ⟨75974582718033435512836019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50649721812022290341890679 75974582718033435512836019)
          ·
            refine ⟨113961874077050153269254029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75974582718033435512836019 113961874077050153269254029)
            ·
              refine ⟨42735702778893807475970261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113961874077050153269254029 42735702778893807475970261)
              ·
                refine ⟨1001618033880323612718053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 42735702778893807475970261 1001618033880323612718053)
                ·
                  refine ⟨187803381352560677384635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1001618033880323612718053 187803381352560677384635)
                  ·
                    rfl

theorem cell21_822928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7, 4].length) (baseStart_822928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_822928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_822928 prefixEnd_822928 := by exact prefixLift 822928
  have htrace : WordTrace (prefixWord ++ tailWord_822928) baseStart_822928 baseEnd_822928 := by
    simpa [prefixWord, tailWord_822928, baseEnd_822928] using wordTrace_append hprefix tailTrace_822928
  have hstable : (prefixWord ++ tailWord_822928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822928).length < 2 ^ (prefixWord ++ tailWord_822928).sum := by decide
  have hdescent : baseEnd_822928 < baseStart_822928 := by decide
  rcases family_descends (prefixWord ++ tailWord_822928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
