import V185TrunkScan23Chunk0802

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4749580 : List Nat := [2, 2, 1, 2, 2, 2, 2, 1, 4, 1, 4]
def baseStart_4749580 : Nat := 118140960795 + 4749580 * 2 ^ 59
def prefixEnd_4749580 : Nat := 4983230072969 + 3 ^ 40 * 4749580 * 2
def baseEnd_4749580 : Nat := 2438817446981632480107085

theorem tailTrace_4749580 : CollatzResearch.WordTrace tailWord_4749580 prefixEnd_4749580 2438817446981632480107085 := by
  unfold tailWord_4749580
  simp only [CollatzResearch.WordTrace]
  refine ⟨86615707066545149264535097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115487609422060199019380129 86615707066545149264535097)
  ·
    refine ⟨64961780299908861948401323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86615707066545149264535097 64961780299908861948401323)
    ·
      refine ⟨97442670449863292922601985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64961780299908861948401323 97442670449863292922601985)
      ·
        refine ⟨73082002837397469691951489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97442670449863292922601985 73082002837397469691951489)
        ·
          refine ⟨54811502128048102268963617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73082002837397469691951489 54811502128048102268963617)
          ·
            refine ⟨41108626596036076701722713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54811502128048102268963617 41108626596036076701722713)
            ·
              refine ⟨30831469947027057526292035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41108626596036076701722713 30831469947027057526292035)
              ·
                refine ⟨46247204920540586289438053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30831469947027057526292035 46247204920540586289438053)
                ·
                  refine ⟨8671350922601359929269635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46247204920540586289438053 8671350922601359929269635)
                  ·
                    refine ⟨13007026383902039893904453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8671350922601359929269635 13007026383902039893904453)
                    ·
                      refine ⟨2438817446981632480107085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13007026383902039893904453 2438817446981632480107085)
                      ·
                        rfl

theorem cell23_4749580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_4749580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749580 prefixEnd_4749580 := by exact prefixLift 4749580
  have htrace : WordTrace (prefixWord ++ tailWord_4749580) baseStart_4749580 baseEnd_4749580 := by
    simpa [prefixWord, tailWord_4749580, baseEnd_4749580] using wordTrace_append hprefix tailTrace_4749580
  have hstable : (prefixWord ++ tailWord_4749580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749580).length < 2 ^ (prefixWord ++ tailWord_4749580).sum := by decide
  have hdescent : baseEnd_4749580 < baseStart_4749580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749583 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 5]
def baseStart_4749583 : Nat := 118140960795 + 4749583 * 2 ^ 59
def prefixEnd_4749583 : Nat := 4983230072969 + 3 ^ 40 * 4749583 * 2
def baseEnd_4749583 : Nat := 2438818987423595968369571

theorem tailTrace_4749583 : CollatzResearch.WordTrace tailWord_4749583 prefixEnd_4749583 2438818987423595968369571 := by
  unfold tailWord_4749583
  simp only [CollatzResearch.WordTrace]
  refine ⟨173231523552079430041429403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115487682368052953360952935 173231523552079430041429403)
  ·
    refine ⟨259847285328119145062144105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173231523552079430041429403 259847285328119145062144105)
    ·
      refine ⟨194885463996089358796608079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259847285328119145062144105 194885463996089358796608079)
      ·
        refine ⟨292328195994134038194912119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194885463996089358796608079 292328195994134038194912119)
        ·
          refine ⟨438492293991201057292368179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292328195994134038194912119 438492293991201057292368179)
          ·
            refine ⟨657738440986801585938552269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 438492293991201057292368179 657738440986801585938552269)
            ·
              refine ⟨246651915370050594726957101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 657738440986801585938552269 246651915370050594726957101)
              ·
                refine ⟨92494468263768973022608913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 246651915370050594726957101 92494468263768973022608913)
                ·
                  refine ⟨69370851197826729766956685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92494468263768973022608913 69370851197826729766956685)
                  ·
                    refine ⟨26014069199185023662608757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 69370851197826729766956685 26014069199185023662608757)
                    ·
                      refine ⟨2438818987423595968369571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26014069199185023662608757 2438818987423595968369571)
                      ·
                        rfl

theorem cell23_4749583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 5].length) (baseStart_4749583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749583 prefixEnd_4749583 := by exact prefixLift 4749583
  have htrace : WordTrace (prefixWord ++ tailWord_4749583) baseStart_4749583 baseEnd_4749583 := by
    simpa [prefixWord, tailWord_4749583, baseEnd_4749583] using wordTrace_append hprefix tailTrace_4749583
  have hstable : (prefixWord ++ tailWord_4749583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749583).length < 2 ^ (prefixWord ++ tailWord_4749583).sum := by decide
  have hdescent : baseEnd_4749583 < baseStart_4749583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749624 : List Nat := [2, 1, 2, 1, 3, 1, 5, 3, 1, 4]
def baseStart_4749624 : Nat := 118140960795 + 4749624 * 2 ^ 59
def prefixEnd_4749624 : Nat := 4983230072969 + 3 ^ 40 * 4749624 * 2
def baseEnd_4749624 : Nat := 812946680043476769318961

theorem tailTrace_4749624 : CollatzResearch.WordTrace tailWord_4749624 prefixEnd_4749624 812946680043476769318961 := by
  unfold tailWord_4749624
  simp only [CollatzResearch.WordTrace]
  refine ⟨86616509472465447021835963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115488679296620596029114617 86616509472465447021835963)
  ·
    refine ⟨129924764208698170532753945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86616509472465447021835963 129924764208698170532753945)
    ·
      refine ⟨97443573156523627899565459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129924764208698170532753945 97443573156523627899565459)
      ·
        refine ⟨146165359734785441849348189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97443573156523627899565459 146165359734785441849348189)
        ·
          refine ⟨54812009900544540693505571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146165359734785441849348189 54812009900544540693505571)
          ·
            refine ⟨82218014850816811040258357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54812009900544540693505571 82218014850816811040258357)
            ·
              refine ⟨7707938892264076035024221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82218014850816811040258357 7707938892264076035024221)
              ·
                refine ⟨2890477084599028513134083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7707938892264076035024221 2890477084599028513134083)
                ·
                  refine ⟨4335715626898542769701125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2890477084599028513134083 4335715626898542769701125)
                  ·
                    refine ⟨812946680043476769318961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4335715626898542769701125 812946680043476769318961)
                    ·
                      rfl

theorem cell23_4749624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 3, 1, 4].length) (baseStart_4749624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749624 prefixEnd_4749624 := by exact prefixLift 4749624
  have htrace : WordTrace (prefixWord ++ tailWord_4749624) baseStart_4749624 baseEnd_4749624 := by
    simpa [prefixWord, tailWord_4749624, baseEnd_4749624] using wordTrace_append hprefix tailTrace_4749624
  have hstable : (prefixWord ++ tailWord_4749624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749624).length < 2 ^ (prefixWord ++ tailWord_4749624).sum := by decide
  have hdescent : baseEnd_4749624 < baseStart_4749624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749647 : List Nat := [1, 1, 2, 1, 1, 2, 1, 7, 3, 1, 3]
def baseStart_4749647 : Nat := 118140960795 + 4749647 * 2 ^ 59
def prefixEnd_4749647 : Nat := 4983230072969 + 3 ^ 40 * 4749647 * 2
def baseEnd_4749647 : Nat := 2438851850185483717969277

theorem tailTrace_4749647 : CollatzResearch.WordTrace tailWord_4749647 prefixEnd_4749647 2438851850185483717969277 := by
  unfold tailWord_4749647
  simp only [CollatzResearch.WordTrace]
  refine ⟨173233857823847568971759195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115489238549231712647839463 173233857823847568971759195)
  ·
    refine ⟨259850786735771353457638793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173233857823847568971759195 259850786735771353457638793)
    ·
      refine ⟨194888090051828515093229095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259850786735771353457638793 194888090051828515093229095)
      ·
        refine ⟨292332135077742772639843643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194888090051828515093229095 292332135077742772639843643)
        ·
          refine ⟨438498202616614158959765465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292332135077742772639843643 438498202616614158959765465)
          ·
            refine ⟨328873651962460619219824099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 438498202616614158959765465 328873651962460619219824099)
            ·
              refine ⟨493310477943690928829736149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 328873651962460619219824099 493310477943690928829736149)
              ·
                refine ⟨11561964326805256144446941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 493310477943690928829736149 11561964326805256144446941)
                ·
                  refine ⟨4335736622551971054167603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11561964326805256144446941 4335736622551971054167603)
                  ·
                    refine ⟨6503604933827956581251405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4335736622551971054167603 6503604933827956581251405)
                    ·
                      refine ⟨2438851850185483717969277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6503604933827956581251405 2438851850185483717969277)
                      ·
                        rfl

theorem cell23_4749647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 3, 1, 3].length) (baseStart_4749647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749647 prefixEnd_4749647 := by exact prefixLift 4749647
  have htrace : WordTrace (prefixWord ++ tailWord_4749647) baseStart_4749647 baseEnd_4749647 := by
    simpa [prefixWord, tailWord_4749647, baseEnd_4749647] using wordTrace_append hprefix tailTrace_4749647
  have hstable : (prefixWord ++ tailWord_4749647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749647).length < 2 ^ (prefixWord ++ tailWord_4749647).sum := by decide
  have hdescent : baseEnd_4749647 < baseStart_4749647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749657 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 6, 3, 2]
def baseStart_4749657 : Nat := 118140960795 + 4749657 * 2 ^ 59
def prefixEnd_4749657 : Nat := 4983230072969 + 3 ^ 40 * 4749657 * 2
def baseEnd_4749657 : Nat := 2438856984992028678844231

theorem tailTrace_4749657 : CollatzResearch.WordTrace tailWord_4749657 prefixEnd_4749657 2438856984992028678844231 := by
  unfold tailWord_4749657
  simp only [CollatzResearch.WordTrace]
  refine ⟨173234222553811340679623225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115489481702540893786415483 173234222553811340679623225)
  ·
    refine ⟨129925666915358505509717419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173234222553811340679623225 129925666915358505509717419)
    ·
      refine ⟨194888500373037758264576129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129925666915358505509717419 194888500373037758264576129)
      ·
        refine ⟨146166375279778318698432097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194888500373037758264576129 146166375279778318698432097)
        ·
          refine ⟨109624781459833739023824073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146166375279778318698432097 109624781459833739023824073)
          ·
            refine ⟨82218586094875304267868055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109624781459833739023824073 82218586094875304267868055)
            ·
              refine ⟨123327879142312956401802083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82218586094875304267868055 123327879142312956401802083)
              ·
                refine ⟨184991818713469434602703125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123327879142312956401802083 184991818713469434602703125)
                ·
                  refine ⟨8671491502193879747001709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 184991818713469434602703125 8671491502193879747001709)
                  ·
                    refine ⟨3251809313322704905125641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8671491502193879747001709 3251809313322704905125641)
                    ·
                      refine ⟨2438856984992028678844231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3251809313322704905125641 2438856984992028678844231)
                      ·
                        rfl

theorem cell23_4749657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6, 3, 2].length) (baseStart_4749657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749657 prefixEnd_4749657 := by exact prefixLift 4749657
  have htrace : WordTrace (prefixWord ++ tailWord_4749657) baseStart_4749657 baseEnd_4749657 := by
    simpa [prefixWord, tailWord_4749657, baseEnd_4749657] using wordTrace_append hprefix tailTrace_4749657
  have hstable : (prefixWord ++ tailWord_4749657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749657).length < 2 ^ (prefixWord ++ tailWord_4749657).sum := by decide
  have hdescent : baseEnd_4749657 < baseStart_4749657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749680 : List Nat := [2, 1, 1, 1, 4, 3, 1, 1, 3, 6]
def baseStart_4749680 : Nat := 118140960795 + 4749680 * 2 ^ 59
def prefixEnd_4749680 : Nat := 4983230072969 + 3 ^ 40 * 4749680 * 2
def baseEnd_4749680 : Nat := 812956265015694029618875

theorem tailTrace_4749680 : CollatzResearch.WordTrace tailWord_4749680 prefixEnd_4749680 812956265015694029618875 := by
  unfold tailWord_4749680
  simp only [CollatzResearch.WordTrace]
  refine ⟨86617530716364007803855247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115490040955152010405140329 86617530716364007803855247)
  ·
    refine ⟨129926296074546011705782871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86617530716364007803855247 129926296074546011705782871)
    ·
      refine ⟨194889444111819017558674307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129926296074546011705782871 194889444111819017558674307)
      ·
        refine ⟨292334166167728526338011461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194889444111819017558674307 292334166167728526338011461)
        ·
          refine ⟨54812656156449098688377149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 292334166167728526338011461 54812656156449098688377149)
          ·
            refine ⟨20554746058668412008141431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54812656156449098688377149 20554746058668412008141431)
            ·
              refine ⟨30832119088002618012212147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20554746058668412008141431 30832119088002618012212147)
              ·
                refine ⟨46248178632003927018318221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30832119088002618012212147 46248178632003927018318221)
                ·
                  refine ⟨17343066987001472631869333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46248178632003927018318221 17343066987001472631869333)
                  ·
                    refine ⟨812956265015694029618875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17343066987001472631869333 812956265015694029618875)
                    ·
                      rfl

theorem cell23_4749680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 3, 6].length) (baseStart_4749680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749680 prefixEnd_4749680 := by exact prefixLift 4749680
  have htrace : WordTrace (prefixWord ++ tailWord_4749680) baseStart_4749680 baseEnd_4749680 := by
    simpa [prefixWord, tailWord_4749680, baseEnd_4749680] using wordTrace_append hprefix tailTrace_4749680
  have hstable : (prefixWord ++ tailWord_4749680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749680).length < 2 ^ (prefixWord ++ tailWord_4749680).sum := by decide
  have hdescent : baseEnd_4749680 < baseStart_4749680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749707 : List Nat := [1, 1, 1, 1, 4, 4, 1, 2, 3, 2, 3]
def baseStart_4749707 : Nat := 118140960795 + 4749707 * 2 ^ 59
def prefixEnd_4749707 : Nat := 4983230072969 + 3 ^ 40 * 4749707 * 2
def baseEnd_4749707 : Nat := 2438882659024753483219001

theorem tailTrace_4749707 : CollatzResearch.WordTrace tailWord_4749707 prefixEnd_4749707 2438882659024753483219001 := by
  unfold tailWord_4749707
  simp only [CollatzResearch.WordTrace]
  refine ⟨173236046203630199218943375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115490697469086799479295583 173236046203630199218943375)
  ·
    refine ⟨259854069305445298828415063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173236046203630199218943375 259854069305445298828415063)
    ·
      refine ⟨389781103958167948242622595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259854069305445298828415063 389781103958167948242622595)
      ·
        refine ⟨584671655937251922363933893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 389781103958167948242622595 584671655937251922363933893)
        ·
          refine ⟨109625935488234735443237605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 584671655937251922363933893 109625935488234735443237605)
          ·
            refine ⟨20554862904044012895607051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109625935488234735443237605 20554862904044012895607051)
            ·
              refine ⟨30832294356066019343410577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20554862904044012895607051 30832294356066019343410577)
              ·
                refine ⟨23124220767049514507557933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30832294356066019343410577 23124220767049514507557933)
                ·
                  refine ⟨8671582787643567940334225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23124220767049514507557933 8671582787643567940334225)
                  ·
                    refine ⟨6503687090732675955250669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8671582787643567940334225 6503687090732675955250669)
                    ·
                      refine ⟨2438882659024753483219001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6503687090732675955250669 2438882659024753483219001)
                      ·
                        rfl

theorem cell23_4749707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3, 2, 3].length) (baseStart_4749707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749707 prefixEnd_4749707 := by exact prefixLift 4749707
  have htrace : WordTrace (prefixWord ++ tailWord_4749707) baseStart_4749707 baseEnd_4749707 := by
    simpa [prefixWord, tailWord_4749707, baseEnd_4749707] using wordTrace_append hprefix tailTrace_4749707
  have hstable : (prefixWord ++ tailWord_4749707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749707).length < 2 ^ (prefixWord ++ tailWord_4749707).sum := by decide
  have hdescent : baseEnd_4749707 < baseStart_4749707 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749727 : List Nat := [1, 1, 2, 5, 1, 1, 5, 7]
def baseStart_4749727 : Nat := 118140960795 + 4749727 * 2 ^ 59
def prefixEnd_4749727 : Nat := 4983230072969 + 3 ^ 40 * 4749727 * 2
def baseEnd_4749727 : Nat := 90329367727327533517367

theorem tailTrace_4749727 : CollatzResearch.WordTrace tailWord_4749727 prefixEnd_4749727 90329367727327533517367 := by
  unfold tailWord_4749727
  simp only [CollatzResearch.WordTrace]
  refine ⟨173236775663557742634671435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115491183775705161756447623 173236775663557742634671435)
  ·
    refine ⟨259855163495336613952007153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173236775663557742634671435 259855163495336613952007153)
    ·
      refine ⟨194891372621502460464005365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259855163495336613952007153 194891372621502460464005365)
      ·
        refine ⟨18271066183265855668500503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 194891372621502460464005365 18271066183265855668500503)
        ·
          refine ⟨27406599274898783502750755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18271066183265855668500503 27406599274898783502750755)
          ·
            refine ⟨41109898912348175254126133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27406599274898783502750755 41109898912348175254126133)
            ·
              refine ⟨3854053023032641430074325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41109898912348175254126133 3854053023032641430074325)
              ·
                refine ⟨90329367727327533517367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3854053023032641430074325 90329367727327533517367)
                ·
                  rfl

theorem cell23_4749727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 7].length) (baseStart_4749727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749727 prefixEnd_4749727 := by exact prefixLift 4749727
  have htrace : WordTrace (prefixWord ++ tailWord_4749727) baseStart_4749727 baseEnd_4749727 := by
    simpa [prefixWord, tailWord_4749727, baseEnd_4749727] using wordTrace_append hprefix tailTrace_4749727
  have hstable : (prefixWord ++ tailWord_4749727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749727).length < 2 ^ (prefixWord ++ tailWord_4749727).sum := by decide
  have hdescent : baseEnd_4749727 < baseStart_4749727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749748 : List Nat := [2, 5, 2, 2, 1, 1, 1, 1, 4, 4]
def baseStart_4749748 : Nat := 118140960795 + 4749748 * 2 ^ 59
def prefixEnd_4749748 : Nat := 4983230072969 + 3 ^ 40 * 4749748 * 2
def baseEnd_4749748 : Nat := 812967903910529274268771

theorem tailTrace_4749748 : CollatzResearch.WordTrace tailWord_4749748 prefixEnd_4749748 812967903910529274268771 := by
  unfold tailWord_4749748
  simp only [CollatzResearch.WordTrace]
  refine ⟨86618770798240831610592949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115491694397654442147457265 86618770798240831610592949)
  ·
    refine ⟨8120509762335077963493089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86618770798240831610592949 8120509762335077963493089)
    ·
      refine ⟨6090382321751308472619817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8120509762335077963493089 6090382321751308472619817)
      ·
        refine ⟨4567786741313481354464863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6090382321751308472619817 4567786741313481354464863)
        ·
          refine ⟨6851680111970222031697295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4567786741313481354464863 6851680111970222031697295)
          ·
            refine ⟨10277520167955333047545943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6851680111970222031697295 10277520167955333047545943)
            ·
              refine ⟨15416280251932999571318915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10277520167955333047545943 15416280251932999571318915)
              ·
                refine ⟨23124420377899499356978373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15416280251932999571318915 23124420377899499356978373)
                ·
                  refine ⟨4335828820856156129433445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23124420377899499356978373 4335828820856156129433445)
                  ·
                    refine ⟨812967903910529274268771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4335828820856156129433445 812967903910529274268771)
                    ·
                      rfl

theorem cell23_4749748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_4749748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749748 prefixEnd_4749748 := by exact prefixLift 4749748
  have htrace : WordTrace (prefixWord ++ tailWord_4749748) baseStart_4749748 baseEnd_4749748 := by
    simpa [prefixWord, tailWord_4749748, baseEnd_4749748] using wordTrace_append hprefix tailTrace_4749748
  have hstable : (prefixWord ++ tailWord_4749748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749748).length < 2 ^ (prefixWord ++ tailWord_4749748).sum := by decide
  have hdescent : baseEnd_4749748 < baseStart_4749748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749778 : List Nat := [3, 2, 2, 4, 2, 1, 2, 7]
def baseStart_4749778 : Nat := 118140960795 + 4749778 * 2 ^ 59
def prefixEnd_4749778 : Nat := 4983230072969 + 3 ^ 40 * 4749778 * 2
def baseEnd_4749778 : Nat := 90330337635230470571525

theorem tailTrace_4749778 : CollatzResearch.WordTrace tailWord_4749778 prefixEnd_4749778 90330337635230470571525 := by
  unfold tailWord_4749778
  simp only [CollatzResearch.WordTrace]
  refine ⟨43309658946593244586194497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115492423857581985563185325 43309658946593244586194497)
  ·
    refine ⟨32482244209944933439645873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43309658946593244586194497 32482244209944933439645873)
    ·
      refine ⟨24361683157458700079734405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32482244209944933439645873 24361683157458700079734405)
      ·
        refine ⟨4567815592023506264950201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24361683157458700079734405 4567815592023506264950201)
        ·
          refine ⟨3425861694017629698712651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4567815592023506264950201 3425861694017629698712651)
          ·
            refine ⟨5138792541026444548068977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3425861694017629698712651 5138792541026444548068977)
            ·
              refine ⟨3854094405769833411051733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5138792541026444548068977 3854094405769833411051733)
              ·
                refine ⟨90330337635230470571525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3854094405769833411051733 90330337635230470571525)
                ·
                  rfl

theorem cell23_4749778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 7].length) (baseStart_4749778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749778 prefixEnd_4749778 := by exact prefixLift 4749778
  have htrace : WordTrace (prefixWord ++ tailWord_4749778) baseStart_4749778 baseEnd_4749778 := by
    simpa [prefixWord, tailWord_4749778, baseEnd_4749778] using wordTrace_append hprefix tailTrace_4749778
  have hstable : (prefixWord ++ tailWord_4749778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749778).length < 2 ^ (prefixWord ++ tailWord_4749778).sum := by decide
  have hdescent : baseEnd_4749778 < baseStart_4749778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749781 : List Nat := [1, 3, 2, 3, 1, 2, 1, 4, 1, 3, 2]
def baseStart_4749781 : Nat := 118140960795 + 4749781 * 2 ^ 59
def prefixEnd_4749781 : Nat := 4983230072969 + 3 ^ 40 * 4749781 * 2
def baseEnd_4749781 : Nat := 2438920656593186193693661

theorem tailTrace_4749781 : CollatzResearch.WordTrace tailWord_4749781 prefixEnd_4749781 2438920656593186193693661 := by
  unfold tailWord_4749781
  simp only [CollatzResearch.WordTrace]
  refine ⟨173238745205362109857137197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115492496803574739904758131 173238745205362109857137197)
  ·
    refine ⟨64964529452010791196426449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173238745205362109857137197 64964529452010791196426449)
    ·
      refine ⟨48723397089008093397319837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64964529452010791196426449 48723397089008093397319837)
      ·
        refine ⟨18271273908378035023994939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48723397089008093397319837 18271273908378035023994939)
        ·
          refine ⟨27406910862567052535992409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18271273908378035023994939 27406910862567052535992409)
          ·
            refine ⟨20555183146925289401994307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27406910862567052535992409 20555183146925289401994307)
            ·
              refine ⟨30832774720387934102991461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20555183146925289401994307 30832774720387934102991461)
              ·
                refine ⟨5781145260072737644310899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30832774720387934102991461 5781145260072737644310899)
                ·
                  refine ⟨8671717890109106466466349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5781145260072737644310899 8671717890109106466466349)
                  ·
                    refine ⟨3251894208790914924924881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8671717890109106466466349 3251894208790914924924881)
                    ·
                      refine ⟨2438920656593186193693661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3251894208790914924924881 2438920656593186193693661)
                      ·
                        rfl

theorem cell23_4749781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_4749781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749781 prefixEnd_4749781 := by exact prefixLift 4749781
  have htrace : WordTrace (prefixWord ++ tailWord_4749781) baseStart_4749781 baseEnd_4749781 := by
    simpa [prefixWord, tailWord_4749781, baseEnd_4749781] using wordTrace_append hprefix tailTrace_4749781
  have hstable : (prefixWord ++ tailWord_4749781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749781).length < 2 ^ (prefixWord ++ tailWord_4749781).sum := by decide
  have hdescent : baseEnd_4749781 < baseStart_4749781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749811 : List Nat := [1, 1, 1, 2, 2, 2, 4, 4, 2, 2, 2]
def baseStart_4749811 : Nat := 118140960795 + 4749811 * 2 ^ 59
def prefixEnd_4749811 : Nat := 4983230072969 + 3 ^ 40 * 4749811 * 2
def baseEnd_4749811 : Nat := 2438936061012821076318523

theorem tailTrace_4749811 : CollatzResearch.WordTrace tailWord_4749811 prefixEnd_4749811 2438936061012821076318523 := by
  unfold tailWord_4749811
  simp only [CollatzResearch.WordTrace]
  refine ⟨173239839395253424980729287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115493226263502283320486191 173239839395253424980729287)
  ·
    refine ⟨259859759092880137471093931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173239839395253424980729287 259859759092880137471093931)
    ·
      refine ⟨389789638639320206206640897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259859759092880137471093931 389789638639320206206640897)
      ·
        refine ⟨292342228979490154654980673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 389789638639320206206640897 292342228979490154654980673)
        ·
          refine ⟨219256671734617615991235505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292342228979490154654980673 219256671734617615991235505)
          ·
            refine ⟨164442503800963211993426629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219256671734617615991235505 164442503800963211993426629)
            ·
              refine ⟨30832969462680602248767493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 164442503800963211993426629 30832969462680602248767493)
              ·
                refine ⟨5781181774252612921643905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30832969462680602248767493 5781181774252612921643905)
                ·
                  refine ⟨4335886330689459691232929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5781181774252612921643905 4335886330689459691232929)
                  ·
                    refine ⟨3251914748017094768424697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4335886330689459691232929 3251914748017094768424697)
                    ·
                      refine ⟨2438936061012821076318523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3251914748017094768424697 2438936061012821076318523)
                      ·
                        rfl

theorem cell23_4749811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 2, 2, 2].length) (baseStart_4749811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749811 prefixEnd_4749811 := by exact prefixLift 4749811
  have htrace : WordTrace (prefixWord ++ tailWord_4749811) baseStart_4749811 baseEnd_4749811 := by
    simpa [prefixWord, tailWord_4749811, baseEnd_4749811] using wordTrace_append hprefix tailTrace_4749811
  have hstable : (prefixWord ++ tailWord_4749811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749811).length < 2 ^ (prefixWord ++ tailWord_4749811).sum := by decide
  have hdescent : baseEnd_4749811 < baseStart_4749811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749814 : List Nat := [5, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3]
def baseStart_4749814 : Nat := 118140960795 + 4749814 * 2 ^ 59
def prefixEnd_4749814 : Nat := 4983230072969 + 3 ^ 40 * 4749814 * 2
def baseEnd_4749814 : Nat := 2438937601454784564581009

theorem tailTrace_4749814 : CollatzResearch.WordTrace tailWord_4749814 prefixEnd_4749814 2438937601454784564581009 := by
  unfold tailWord_4749814
  simp only [CollatzResearch.WordTrace]
  refine ⟨10827496800890159780818031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115493299209495037662058997 10827496800890159780818031)
  ·
    refine ⟨16241245201335239671227047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10827496800890159780818031 16241245201335239671227047)
    ·
      refine ⟨24361867802002859506840571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16241245201335239671227047 24361867802002859506840571)
      ·
        refine ⟨36542801703004289260260857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24361867802002859506840571 36542801703004289260260857)
        ·
          refine ⟨27407101277253216945195643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36542801703004289260260857 27407101277253216945195643)
          ·
            refine ⟨41110651915879825417793465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27407101277253216945195643 41110651915879825417793465)
            ·
              refine ⟨30832988936909869063345099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41110651915879825417793465 30832988936909869063345099)
              ·
                refine ⟨46249483405364803595017649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30832988936909869063345099 46249483405364803595017649)
                ·
                  refine ⟨34687112554023602696263237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46249483405364803595017649 34687112554023602696263237)
                  ·
                    refine ⟨6503833603879425505549357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34687112554023602696263237 6503833603879425505549357)
                    ·
                      refine ⟨2438937601454784564581009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6503833603879425505549357 2438937601454784564581009)
                      ·
                        rfl

theorem cell23_4749814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_4749814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749814 prefixEnd_4749814 := by exact prefixLift 4749814
  have htrace : WordTrace (prefixWord ++ tailWord_4749814) baseStart_4749814 baseEnd_4749814 := by
    simpa [prefixWord, tailWord_4749814, baseEnd_4749814] using wordTrace_append hprefix tailTrace_4749814
  have hstable : (prefixWord ++ tailWord_4749814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749814).length < 2 ^ (prefixWord ++ tailWord_4749814).sum := by decide
  have hdescent : baseEnd_4749814 < baseStart_4749814 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749817 : List Nat := [1, 2, 1, 3, 1, 2, 5, 1, 7]
def baseStart_4749817 : Nat := 118140960795 + 4749817 * 2 ^ 59
def prefixEnd_4749817 : Nat := 4983230072969 + 3 ^ 40 * 4749817 * 2
def baseEnd_4749817 : Nat := 270993237988527561427055

theorem tailTrace_4749817 : CollatzResearch.WordTrace tailWord_4749817 prefixEnd_4749817 270993237988527561427055 := by
  unfold tailWord_4749817
  simp only [CollatzResearch.WordTrace]
  refine ⟨173240058233231688005447705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115493372155487792003631803 173240058233231688005447705)
  ·
    refine ⟨129930043674923766004085779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173240058233231688005447705 129930043674923766004085779)
    ·
      refine ⟨194895065512385649006128669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129930043674923766004085779 194895065512385649006128669)
      ·
        refine ⟨73085649567144618377298251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194895065512385649006128669 73085649567144618377298251)
        ·
          refine ⟨109628474350716927565947377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73085649567144618377298251 109628474350716927565947377)
          ·
            refine ⟨82221355763037695674460533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109628474350716927565947377 82221355763037695674460533)
            ·
              refine ⟨7708252102784783969480675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82221355763037695674460533 7708252102784783969480675)
              ·
                refine ⟨11562378154177175954221013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7708252102784783969480675 11562378154177175954221013)
                ·
                  refine ⟨270993237988527561427055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11562378154177175954221013 270993237988527561427055)
                  ·
                    rfl

theorem cell23_4749817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 7].length) (baseStart_4749817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749817 prefixEnd_4749817 := by exact prefixLift 4749817
  have htrace : WordTrace (prefixWord ++ tailWord_4749817) baseStart_4749817 baseEnd_4749817 := by
    simpa [prefixWord, tailWord_4749817, baseEnd_4749817] using wordTrace_append hprefix tailTrace_4749817
  have hstable : (prefixWord ++ tailWord_4749817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749817).length < 2 ^ (prefixWord ++ tailWord_4749817).sum := by decide
  have hdescent : baseEnd_4749817 < baseStart_4749817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749827 : List Nat := [1, 1, 1, 3, 2, 1, 4, 1, 1, 5, 3]
def baseStart_4749827 : Nat := 118140960795 + 4749827 * 2 ^ 59
def prefixEnd_4749827 : Nat := 4983230072969 + 3 ^ 40 * 4749827 * 2
def baseEnd_4749827 : Nat := 2438944276703293013718449

theorem tailTrace_4749827 : CollatzResearch.WordTrace tailWord_4749827 prefixEnd_4749827 2438944276703293013718449 := by
  unfold tailWord_4749827
  simp only [CollatzResearch.WordTrace]
  refine ⟨173240422963195459713311735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115493615308796973142207823 173240422963195459713311735)
  ·
    refine ⟨259860634444793189569967603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173240422963195459713311735 259860634444793189569967603)
    ·
      refine ⟨389790951667189784354951405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259860634444793189569967603 389790951667189784354951405)
      ·
        refine ⟨146171606875196169133106777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 389790951667189784354951405 146171606875196169133106777)
        ·
          refine ⟨109628705156397126849830083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146171606875196169133106777 109628705156397126849830083)
          ·
            refine ⟨164443057734595690274745125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109628705156397126849830083 164443057734595690274745125)
            ·
              refine ⟨30833073325236691926514711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 164443057734595690274745125 30833073325236691926514711)
              ·
                refine ⟨46249609987855037889772067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30833073325236691926514711 46249609987855037889772067)
                ·
                  refine ⟨69374414981782556834658101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46249609987855037889772067 69374414981782556834658101)
                  ·
                    refine ⟨6503851404542114703249197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 69374414981782556834658101 6503851404542114703249197)
                    ·
                      refine ⟨2438944276703293013718449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6503851404542114703249197 2438944276703293013718449)
                      ·
                        rfl

theorem cell23_4749827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 5, 3].length) (baseStart_4749827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749827 prefixEnd_4749827 := by exact prefixLift 4749827
  have htrace : WordTrace (prefixWord ++ tailWord_4749827) baseStart_4749827 baseEnd_4749827 := by
    simpa [prefixWord, tailWord_4749827, baseEnd_4749827] using wordTrace_append hprefix tailTrace_4749827
  have hstable : (prefixWord ++ tailWord_4749827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749827).length < 2 ^ (prefixWord ++ tailWord_4749827).sum := by decide
  have hdescent : baseEnd_4749827 < baseStart_4749827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749857 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 3, 2, 5]
def baseStart_4749857 : Nat := 118140960795 + 4749857 * 2 ^ 59
def prefixEnd_4749857 : Nat := 4983230072969 + 3 ^ 40 * 4749857 * 2
def baseEnd_4749857 : Nat := 2438959681122927896343311

theorem tailTrace_4749857 : CollatzResearch.WordTrace tailWord_4749857 prefixEnd_4749857 2438959681122927896343311 := by
  unfold tailWord_4749857
  simp only [CollatzResearch.WordTrace]
  refine ⟨173241517153086774836903825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115494344768724516557935883 173241517153086774836903825)
  ·
    refine ⟨129931137864815081127677869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173241517153086774836903825 129931137864815081127677869)
    ·
      refine ⟨48724176699305655422879201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129931137864815081127677869 48724176699305655422879201)
      ·
        refine ⟨36543132524479241567159401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48724176699305655422879201 36543132524479241567159401)
        ·
          refine ⟨27407349393359431175369551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36543132524479241567159401 27407349393359431175369551)
          ·
            refine ⟨41111024090039146763054327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27407349393359431175369551 41111024090039146763054327)
            ·
              refine ⟨61666536135058720144581491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41111024090039146763054327 61666536135058720144581491)
              ·
                refine ⟨92499804202588080216872237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61666536135058720144581491 92499804202588080216872237)
                ·
                  refine ⟨34687426575970530081327089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92499804202588080216872237 34687426575970530081327089)
                  ·
                    refine ⟨26015569931977897560995317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34687426575970530081327089 26015569931977897560995317)
                    ·
                      refine ⟨2438959681122927896343311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26015569931977897560995317 2438959681122927896343311)
                      ·
                        rfl

theorem cell23_4749857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_4749857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749857 prefixEnd_4749857 := by exact prefixLift 4749857
  have htrace : WordTrace (prefixWord ++ tailWord_4749857) baseStart_4749857 baseEnd_4749857 := by
    simpa [prefixWord, tailWord_4749857, baseEnd_4749857] using wordTrace_append hprefix tailTrace_4749857
  have hstable : (prefixWord ++ tailWord_4749857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749857).length < 2 ^ (prefixWord ++ tailWord_4749857).sum := by decide
  have hdescent : baseEnd_4749857 < baseStart_4749857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749901 : List Nat := [1, 6, 1, 1, 2, 2, 1, 1, 1, 3, 4]
def baseStart_4749901 : Nat := 118140960795 + 4749901 * 2 ^ 59
def prefixEnd_4749901 : Nat := 4983230072969 + 3 ^ 40 * 4749901 * 2
def baseEnd_4749901 : Nat := 2438982274271725724193109

theorem tailTrace_4749901 : CollatzResearch.WordTrace tailWord_4749901 prefixEnd_4749901 2438982274271725724193109 := by
  unfold tailWord_4749901
  simp only [CollatzResearch.WordTrace]
  refine ⟨173243121964927370351505557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115495414643284913567670371 173243121964927370351505557)
  ·
    refine ⟨8120771342105970485226823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 173243121964927370351505557 8120771342105970485226823)
    ·
      refine ⟨12181157013158955727840235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8120771342105970485226823 12181157013158955727840235)
      ·
        refine ⟨18271735519738433591760353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12181157013158955727840235 18271735519738433591760353)
        ·
          refine ⟨13703801639803825193820265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18271735519738433591760353 13703801639803825193820265)
          ·
            refine ⟨10277851229852868895365199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13703801639803825193820265 10277851229852868895365199)
            ·
              refine ⟨15416776844779303343047799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10277851229852868895365199 15416776844779303343047799)
              ·
                refine ⟨23125165267168955014571699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15416776844779303343047799 23125165267168955014571699)
                ·
                  refine ⟨34687747900753432521857549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23125165267168955014571699 34687747900753432521857549)
                  ·
                    refine ⟨13007905462782537195696581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34687747900753432521857549 13007905462782537195696581)
                    ·
                      refine ⟨2438982274271725724193109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13007905462782537195696581 2438982274271725724193109)
                      ·
                        rfl

theorem cell23_4749901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_4749901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749901 prefixEnd_4749901 := by exact prefixLift 4749901
  have htrace : WordTrace (prefixWord ++ tailWord_4749901) baseStart_4749901 baseEnd_4749901 := by
    simpa [prefixWord, tailWord_4749901, baseEnd_4749901] using wordTrace_append hprefix tailTrace_4749901
  have hstable : (prefixWord ++ tailWord_4749901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749901).length < 2 ^ (prefixWord ++ tailWord_4749901).sum := by decide
  have hdescent : baseEnd_4749901 < baseStart_4749901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749904 : List Nat := [2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 3]
def baseStart_4749904 : Nat := 118140960795 + 4749904 * 2 ^ 59
def prefixEnd_4749904 : Nat := 4983230072969 + 3 ^ 40 * 4749904 * 2
def baseEnd_4749904 : Nat := 2438983814713689212455595

theorem tailTrace_4749904 : CollatzResearch.WordTrace tailWord_4749904 prefixEnd_4749904 2438983814713689212455595 := by
  unfold tailWord_4749904
  simp only [CollatzResearch.WordTrace]
  refine ⟨86621615691958250931932383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115495487589277667909243177 86621615691958250931932383)
  ·
    refine ⟨129932423537937376397898575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86621615691958250931932383 129932423537937376397898575)
    ·
      refine ⟨194898635306906064596847863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129932423537937376397898575 194898635306906064596847863)
      ·
        refine ⟨292347952960359096895271795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194898635306906064596847863 292347952960359096895271795)
        ·
          refine ⟨438521929440538645342907693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292347952960359096895271795 438521929440538645342907693)
          ·
            refine ⟨164445723540201992003590385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 438521929440538645342907693 164445723540201992003590385)
            ·
              refine ⟨123334292655151494002692789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164445723540201992003590385 123334292655151494002692789)
              ·
                refine ⟨11562589936420452562752449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 123334292655151494002692789 11562589936420452562752449)
                ·
                  refine ⟨8671942452315339422064337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11562589936420452562752449 8671942452315339422064337)
                  ·
                    refine ⟨6503956839236504566548253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8671942452315339422064337 6503956839236504566548253)
                    ·
                      refine ⟨2438983814713689212455595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6503956839236504566548253 2438983814713689212455595)
                      ·
                        rfl

theorem cell23_4749904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 3].length) (baseStart_4749904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749904 prefixEnd_4749904 := by exact prefixLift 4749904
  have htrace : WordTrace (prefixWord ++ tailWord_4749904) baseStart_4749904 baseEnd_4749904 := by
    simpa [prefixWord, tailWord_4749904, baseEnd_4749904] using wordTrace_append hprefix tailTrace_4749904
  have hstable : (prefixWord ++ tailWord_4749904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749904).length < 2 ^ (prefixWord ++ tailWord_4749904).sum := by decide
  have hdescent : baseEnd_4749904 < baseStart_4749904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749928 : List Nat := [2, 1, 4, 3, 2, 1, 2, 1, 3, 4]
def baseStart_4749928 : Nat := 118140960795 + 4749928 * 2 ^ 59
def prefixEnd_4749928 : Nat := 4983230072969 + 3 ^ 40 * 4749928 * 2
def baseEnd_4749928 : Nat := 812998712749799039518495

theorem tailTrace_4749928 : CollatzResearch.WordTrace tailWord_4749928 prefixEnd_4749928 812998712749799039518495 := by
  unfold tailWord_4749928
  simp only [CollatzResearch.WordTrace]
  refine ⟨86622053367914776981369219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115496071157219702641825625 86622053367914776981369219)
  ·
    refine ⟨129933080051872165472053829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86622053367914776981369219 129933080051872165472053829)
    ·
      refine ⟨24362452509726031026010093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129933080051872165472053829 24362452509726031026010093)
      ·
        refine ⟨9135919691147261634753785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24362452509726031026010093 9135919691147261634753785)
        ·
          refine ⟨6851939768360446226065339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9135919691147261634753785 6851939768360446226065339)
          ·
            refine ⟨10277909652540669339098009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6851939768360446226065339 10277909652540669339098009)
            ·
              refine ⟨7708432239405502004323507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10277909652540669339098009 7708432239405502004323507)
              ·
                refine ⟨11562648359108253006485261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7708432239405502004323507 11562648359108253006485261)
                ·
                  refine ⟨4335993134665594877431973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11562648359108253006485261 4335993134665594877431973)
                  ·
                    refine ⟨812998712749799039518495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4335993134665594877431973 812998712749799039518495)
                    ·
                      rfl

theorem cell23_4749928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_4749928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749928 prefixEnd_4749928 := by exact prefixLift 4749928
  have htrace : WordTrace (prefixWord ++ tailWord_4749928) baseStart_4749928 baseEnd_4749928 := by
    simpa [prefixWord, tailWord_4749928, baseEnd_4749928] using wordTrace_append hprefix tailTrace_4749928
  have hstable : (prefixWord ++ tailWord_4749928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749928).length < 2 ^ (prefixWord ++ tailWord_4749928).sum := by decide
  have hdescent : baseEnd_4749928 < baseStart_4749928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749961 : List Nat := [1, 2, 1, 1, 4, 1, 1, 5, 2, 3, 2]
def baseStart_4749961 : Nat := 118140960795 + 4749961 * 2 ^ 59
def prefixEnd_4749961 : Nat := 4983230072969 + 3 ^ 40 * 4749961 * 2
def baseEnd_4749961 : Nat := 2439013083110995489442833

theorem tailTrace_4749961 : CollatzResearch.WordTrace tailWord_4749961 prefixEnd_4749961 2439013083110995489442833 := by
  unfold tailWord_4749961
  simp only [CollatzResearch.WordTrace]
  refine ⟨173245310344710000598689737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115496873563140000399126491 173245310344710000598689737)
  ·
    refine ⟨129933982758532500449017303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173245310344710000598689737 129933982758532500449017303)
    ·
      refine ⟨194900974137798750673525955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129933982758532500449017303 194900974137798750673525955)
      ·
        refine ⟨292351461206698126010288933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194900974137798750673525955 292351461206698126010288933)
        ·
          refine ⟨54815898976255898626929175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 292351461206698126010288933 54815898976255898626929175)
          ·
            refine ⟨82223848464383847940393763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54815898976255898626929175 82223848464383847940393763)
            ·
              refine ⟨123335772696575771910590645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82223848464383847940393763 123335772696575771910590645)
              ·
                refine ⟨11562728690303978616617873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 123335772696575771910590645 11562728690303978616617873)
                ·
                  refine ⟨8672046517727983962463405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11562728690303978616617873 8672046517727983962463405)
                  ·
                    refine ⟨3252017444147993985923777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8672046517727983962463405 3252017444147993985923777)
                    ·
                      refine ⟨2439013083110995489442833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3252017444147993985923777 2439013083110995489442833)
                      ·
                        rfl

theorem cell23_4749961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2, 3, 2].length) (baseStart_4749961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749961 prefixEnd_4749961 := by exact prefixLift 4749961
  have htrace : WordTrace (prefixWord ++ tailWord_4749961) baseStart_4749961 baseEnd_4749961 := by
    simpa [prefixWord, tailWord_4749961, baseEnd_4749961] using wordTrace_append hprefix tailTrace_4749961
  have hstable : (prefixWord ++ tailWord_4749961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749961).length < 2 ^ (prefixWord ++ tailWord_4749961).sum := by decide
  have hdescent : baseEnd_4749961 < baseStart_4749961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749962 : List Nat := [3, 1, 2, 3, 4, 1, 1, 3, 1, 4]
def baseStart_4749962 : Nat := 118140960795 + 4749962 * 2 ^ 59
def prefixEnd_4749962 : Nat := 4983230072969 + 3 ^ 40 * 4749962 * 2
def baseEnd_4749962 : Nat := 813004532197216661843443

theorem tailTrace_4749962 : CollatzResearch.WordTrace tailWord_4749962 prefixEnd_4749962 813004532197216661843443 := by
  unfold tailWord_4749962
  simp only [CollatzResearch.WordTrace]
  refine ⟨43311336704426594442369035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115496897878470918512984093 43311336704426594442369035)
  ·
    refine ⟨64967005056639891663553553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43311336704426594442369035 64967005056639891663553553)
    ·
      refine ⟨48725253792479918747665165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64967005056639891663553553 48725253792479918747665165)
      ·
        refine ⟨18271970172179969530374437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48725253792479918747665165 18271970172179969530374437)
        ·
          refine ⟨3425994407283744286945207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18271970172179969530374437 3425994407283744286945207)
          ·
            refine ⟨5138991610925616430417811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3425994407283744286945207 5138991610925616430417811)
            ·
              refine ⟨7708487416388424645626717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5138991610925616430417811 7708487416388424645626717)
              ·
                refine ⟨2890682781145659242110019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7708487416388424645626717 2890682781145659242110019)
                ·
                  refine ⟨4336024171718488863165029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2890682781145659242110019 4336024171718488863165029)
                  ·
                    refine ⟨813004532197216661843443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4336024171718488863165029 813004532197216661843443)
                    ·
                      rfl

theorem cell23_4749962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 3, 1, 4].length) (baseStart_4749962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749962 prefixEnd_4749962 := by exact prefixLift 4749962
  have htrace : WordTrace (prefixWord ++ tailWord_4749962) baseStart_4749962 baseEnd_4749962 := by
    simpa [prefixWord, tailWord_4749962, baseEnd_4749962] using wordTrace_append hprefix tailTrace_4749962
  have hstable : (prefixWord ++ tailWord_4749962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749962).length < 2 ^ (prefixWord ++ tailWord_4749962).sum := by decide
  have hdescent : baseEnd_4749962 < baseStart_4749962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749985 : List Nat := [1, 2, 3, 3, 3, 2, 1, 1, 3, 1, 3]
def baseStart_4749985 : Nat := 118140960795 + 4749985 * 2 ^ 59
def prefixEnd_4749985 : Nat := 4983230072969 + 3 ^ 40 * 4749985 * 2
def baseEnd_4749985 : Nat := 2439025406646703395542723

theorem tailTrace_4749985 : CollatzResearch.WordTrace tailWord_4749985 prefixEnd_4749985 2439025406646703395542723 := by
  unfold tailWord_4749985
  simp only [CollatzResearch.WordTrace]
  refine ⟨173246185696623052697563409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115497457131082035131708939 173246185696623052697563409)
  ·
    refine ⟨129934639272467289523172557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173246185696623052697563409 129934639272467289523172557)
    ·
      refine ⟨48725489727175233571189709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129934639272467289523172557 48725489727175233571189709)
      ·
        refine ⟨18272058647690712589196141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48725489727175233571189709 18272058647690712589196141)
        ·
          refine ⟨6852021992884017220948553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18272058647690712589196141 6852021992884017220948553)
          ·
            refine ⟨5139016494663012915711415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6852021992884017220948553 5139016494663012915711415)
            ·
              refine ⟨7708524741994519373567123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5139016494663012915711415 7708524741994519373567123)
              ·
                refine ⟨11562787112991779060350685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7708524741994519373567123 11562787112991779060350685)
                ·
                  refine ⟨4336045167371917147631507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11562787112991779060350685 4336045167371917147631507)
                  ·
                    refine ⟨6504067751057875721447261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4336045167371917147631507 6504067751057875721447261)
                    ·
                      refine ⟨2439025406646703395542723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6504067751057875721447261 2439025406646703395542723)
                      ·
                        rfl

theorem cell23_4749985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_4749985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749985 prefixEnd_4749985 := by exact prefixLift 4749985
  have htrace : WordTrace (prefixWord ++ tailWord_4749985) baseStart_4749985 baseEnd_4749985 := by
    simpa [prefixWord, tailWord_4749985, baseEnd_4749985] using wordTrace_append hprefix tailTrace_4749985
  have hstable : (prefixWord ++ tailWord_4749985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749985).length < 2 ^ (prefixWord ++ tailWord_4749985).sum := by decide
  have hdescent : baseEnd_4749985 < baseStart_4749985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750014 : List Nat := [4, 2, 1, 1, 2, 1, 1, 11]
def baseStart_4750014 : Nat := 118140960795 + 4750014 * 2 ^ 59
def prefixEnd_4750014 : Nat := 4983230072969 + 3 ^ 40 * 4750014 * 2
def baseEnd_4750014 : Nat := 90334825836506806743707

theorem tailTrace_4750014 : CollatzResearch.WordTrace tailWord_4750014 prefixEnd_4750014 90334825836506806743707 := by
  unfold tailWord_4750014
  simp only [CollatzResearch.WordTrace]
  refine ⟨21655905426689748831296137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115498162275678660433579397 21655905426689748831296137)
  ·
    refine ⟨16241929070017311623472103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21655905426689748831296137 16241929070017311623472103)
    ·
      refine ⟨24362893605025967435208155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16241929070017311623472103 24362893605025967435208155)
      ·
        refine ⟨36544340407538951152812233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24362893605025967435208155 36544340407538951152812233)
        ·
          refine ⟨27408255305654213364609175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36544340407538951152812233 27408255305654213364609175)
          ·
            refine ⟨41112382958481320046913763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27408255305654213364609175 41112382958481320046913763)
            ·
              refine ⟨61668574437721980070370645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41112382958481320046913763 61668574437721980070370645)
              ·
                refine ⟨90334825836506806743707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 61668574437721980070370645 90334825836506806743707)
                ·
                  rfl

theorem cell23_4750014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 11].length) (baseStart_4750014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750014 prefixEnd_4750014 := by exact prefixLift 4750014
  have htrace : WordTrace (prefixWord ++ tailWord_4750014) baseStart_4750014 baseEnd_4750014 := by
    simpa [prefixWord, tailWord_4750014, baseEnd_4750014] using wordTrace_append hprefix tailTrace_4750014
  have hstable : (prefixWord ++ tailWord_4750014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750014).length < 2 ^ (prefixWord ++ tailWord_4750014).sum := by decide
  have hdescent : baseEnd_4750014 < baseStart_4750014 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750028 : List Nat := [2, 2, 1, 5, 1, 3, 1, 1, 1, 1, 5]
def baseStart_4750028 : Nat := 118140960795 + 4750028 * 2 ^ 59
def prefixEnd_4750028 : Nat := 4983230072969 + 3 ^ 40 * 4750028 * 2
def baseEnd_4750028 : Nat := 2439047486314846727305025

theorem tailTrace_4750028 : CollatzResearch.WordTrace tailWord_4750028 prefixEnd_4750028 2439047486314846727305025 := by
  unfold tailWord_4750028
  simp only [CollatzResearch.WordTrace]
  refine ⟨86623877017733635520689369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115498502690311514027585825 86623877017733635520689369)
  ·
    refine ⟨64967907763300226640517027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86623877017733635520689369 64967907763300226640517027)
    ·
      refine ⟨97451861644950339960775541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64967907763300226640517027 97451861644950339960775541)
      ·
        refine ⟨9136112029214094371322707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97451861644950339960775541 9136112029214094371322707)
        ·
          refine ⟨13704168043821141556984061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9136112029214094371322707 13704168043821141556984061)
          ·
            refine ⟨5139063016432928083869023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13704168043821141556984061 5139063016432928083869023)
            ·
              refine ⟨7708594524649392125803535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5139063016432928083869023 7708594524649392125803535)
              ·
                refine ⟨11562891786974088188705303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7708594524649392125803535 11562891786974088188705303)
                ·
                  refine ⟨17344337680461132283057955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11562891786974088188705303 17344337680461132283057955)
                  ·
                    refine ⟨26016506520691698424586933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17344337680461132283057955 26016506520691698424586933)
                    ·
                      refine ⟨2439047486314846727305025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26016506520691698424586933 2439047486314846727305025)
                      ·
                        rfl

theorem cell23_4750028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_4750028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750028 prefixEnd_4750028 := by exact prefixLift 4750028
  have htrace : WordTrace (prefixWord ++ tailWord_4750028) baseStart_4750028 baseEnd_4750028 := by
    simpa [prefixWord, tailWord_4750028, baseEnd_4750028] using wordTrace_append hprefix tailTrace_4750028
  have hstable : (prefixWord ++ tailWord_4750028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750028).length < 2 ^ (prefixWord ++ tailWord_4750028).sum := by decide
  have hdescent : baseEnd_4750028 < baseStart_4750028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750036 : List Nat := [2, 4, 1, 3, 3, 1, 2, 2, 1, 1, 3]
def baseStart_4750036 : Nat := 118140960795 + 4750036 * 2 ^ 59
def prefixEnd_4750036 : Nat := 4983230072969 + 3 ^ 40 * 4750036 * 2
def baseEnd_4750036 : Nat := 2439051594160082696004989

theorem tailTrace_4750036 : CollatzResearch.WordTrace tailWord_4750036 prefixEnd_4750036 2439051594160082696004989 := by
  unfold tailWord_4750036
  simp only [CollatzResearch.WordTrace]
  refine ⟨86624022909719144203834981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115498697212958858938446641 86624022909719144203834981)
  ·
    refine ⟨16242004295572339538219059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86624022909719144203834981 16242004295572339538219059)
    ·
      refine ⟨24363006443358509307328589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16242004295572339538219059 24363006443358509307328589)
      ·
        refine ⟨9136127416259440990248221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24363006443358509307328589 9136127416259440990248221)
        ·
          refine ⟨3426047781097290371343083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9136127416259440990248221 3426047781097290371343083)
          ·
            refine ⟨5139071671645935557014625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3426047781097290371343083 5139071671645935557014625)
            ·
              refine ⟨3854303753734451667760969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5139071671645935557014625 3854303753734451667760969)
              ·
                refine ⟨2890727815300838750820727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3854303753734451667760969 2890727815300838750820727)
                ·
                  refine ⟨4336091722951258126231091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2890727815300838750820727 4336091722951258126231091)
                  ·
                    refine ⟨6504137584426887189346637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4336091722951258126231091 6504137584426887189346637)
                    ·
                      refine ⟨2439051594160082696004989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6504137584426887189346637 2439051594160082696004989)
                      ·
                        rfl

theorem cell23_4750036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_4750036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750036 prefixEnd_4750036 := by exact prefixLift 4750036
  have htrace : WordTrace (prefixWord ++ tailWord_4750036) baseStart_4750036 baseEnd_4750036 := by
    simpa [prefixWord, tailWord_4750036, baseEnd_4750036] using wordTrace_append hprefix tailTrace_4750036
  have hstable : (prefixWord ++ tailWord_4750036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750036).length < 2 ^ (prefixWord ++ tailWord_4750036).sum := by decide
  have hdescent : baseEnd_4750036 < baseStart_4750036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750064 : List Nat := [2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 4]
def baseStart_4750064 : Nat := 118140960795 + 4750064 * 2 ^ 59
def prefixEnd_4750064 : Nat := 4983230072969 + 3 ^ 40 * 4750064 * 2
def baseEnd_4750064 : Nat := 2439065971618408586454859

theorem tailTrace_4750064 : CollatzResearch.WordTrace tailWord_4750064 prefixEnd_4750064 2439065971618408586454859 := by
  unfold tailWord_4750064
  simp only [CollatzResearch.WordTrace]
  refine ⟨86624533531668424594844623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115499378042224566126459497 86624533531668424594844623)
  ·
    refine ⟨129936800297502636892266935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86624533531668424594844623 129936800297502636892266935)
    ·
      refine ⟨194905200446253955338400403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129936800297502636892266935 194905200446253955338400403)
      ·
        refine ⟨292357800669380933007600605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194905200446253955338400403 292357800669380933007600605)
        ·
          refine ⟨109634175251017849877850227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 292357800669380933007600605 109634175251017849877850227)
          ·
            refine ⟨164451262876526774816775341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109634175251017849877850227 164451262876526774816775341)
            ·
              refine ⟨61669223578697540556290753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 164451262876526774816775341 61669223578697540556290753)
              ·
                refine ⟨46251917684023155417218065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61669223578697540556290753 46251917684023155417218065)
                ·
                  refine ⟨34688938263017366562913549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46251917684023155417218065 34688938263017366562913549)
                  ·
                    refine ⟨13008351848631512461092581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34688938263017366562913549 13008351848631512461092581)
                    ·
                      refine ⟨2439065971618408586454859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13008351848631512461092581 2439065971618408586454859)
                      ·
                        rfl

theorem cell23_4750064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 4].length) (baseStart_4750064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750064 prefixEnd_4750064 := by exact prefixLift 4750064
  have htrace : WordTrace (prefixWord ++ tailWord_4750064) baseStart_4750064 baseEnd_4750064 := by
    simpa [prefixWord, tailWord_4750064, baseEnd_4750064] using wordTrace_append hprefix tailTrace_4750064
  have hstable : (prefixWord ++ tailWord_4750064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750064).length < 2 ^ (prefixWord ++ tailWord_4750064).sum := by decide
  have hdescent : baseEnd_4750064 < baseStart_4750064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750109 : List Nat := [1, 4, 2, 4, 1, 1, 3, 1, 2, 1, 3]
def baseStart_4750109 : Nat := 118140960795 + 4750109 * 2 ^ 59
def prefixEnd_4750109 : Nat := 4983230072969 + 3 ^ 40 * 4750109 * 2
def baseEnd_4750109 : Nat := 2439089078247860910392153

theorem tailTrace_4750109 : CollatzResearch.WordTrace tailWord_4750109 prefixEnd_4750109 2439089078247860910392153 := by
  unfold tailWord_4750109
  simp only [CollatzResearch.WordTrace]
  refine ⟨173250708348173821875077381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115500472232115881250051587 173250708348173821875077381)
  ·
    refine ⟨32484507815282591601577009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173250708348173821875077381 32484507815282591601577009)
    ·
      refine ⟨24363380861461943701182757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32484507815282591601577009 24363380861461943701182757)
      ·
        refine ⟨4568133911524114443971767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24363380861461943701182757 4568133911524114443971767)
        ·
          refine ⟨6852200867286171665957651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4568133911524114443971767 6852200867286171665957651)
          ·
            refine ⟨10278301300929257498936477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6852200867286171665957651 10278301300929257498936477)
            ·
              refine ⟨3854362987848471562101179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10278301300929257498936477 3854362987848471562101179)
              ·
                refine ⟨5781544481772707343151769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3854362987848471562101179 5781544481772707343151769)
                ·
                  refine ⟨4336158361329530507363827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5781544481772707343151769 4336158361329530507363827)
                  ·
                    refine ⟨6504237541994295761045741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4336158361329530507363827 6504237541994295761045741)
                    ·
                      refine ⟨2439089078247860910392153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6504237541994295761045741 2439089078247860910392153)
                      ·
                        rfl

theorem cell23_4750109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_4750109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750109 prefixEnd_4750109 := by exact prefixLift 4750109
  have htrace : WordTrace (prefixWord ++ tailWord_4750109) baseStart_4750109 baseEnd_4750109 := by
    simpa [prefixWord, tailWord_4750109, baseEnd_4750109] using wordTrace_append hprefix tailTrace_4750109
  have hstable : (prefixWord ++ tailWord_4750109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750109).length < 2 ^ (prefixWord ++ tailWord_4750109).sum := by decide
  have hdescent : baseEnd_4750109 < baseStart_4750109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750111 : List Nat := [1, 1, 2, 4, 2, 2, 2, 1, 2, 2, 4]
def baseStart_4750111 : Nat := 118140960795 + 4750111 * 2 ^ 59
def prefixEnd_4750111 : Nat := 4983230072969 + 3 ^ 40 * 4750111 * 2
def baseEnd_4750111 : Nat := 2439090105209169902567143

theorem tailTrace_4750111 : CollatzResearch.WordTrace tailWord_4750111 prefixEnd_4750111 2439090105209169902567143 := by
  unfold tailWord_4750111
  simp only [CollatzResearch.WordTrace]
  refine ⟨173250781294166576216650187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115500520862777717477766791 173250781294166576216650187)
  ·
    refine ⟨259876171941249864324975281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173250781294166576216650187 259876171941249864324975281)
    ·
      refine ⟨194907128955937398243731461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259876171941249864324975281 194907128955937398243731461)
      ·
        refine ⟨36545086679238262170699649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 194907128955937398243731461 36545086679238262170699649)
        ·
          refine ⟨27408815009428696628024737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36545086679238262170699649 27408815009428696628024737)
          ·
            refine ⟨20556611257071522471018553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27408815009428696628024737 20556611257071522471018553)
            ·
              refine ⟨15417458442803641853263915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20556611257071522471018553 15417458442803641853263915)
              ·
                refine ⟨23126187664205462779895873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15417458442803641853263915 23126187664205462779895873)
                ·
                  refine ⟨17344640748154097084921905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23126187664205462779895873 17344640748154097084921905)
                  ·
                    refine ⟨13008480561115572813691429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17344640748154097084921905 13008480561115572813691429)
                    ·
                      refine ⟨2439090105209169902567143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13008480561115572813691429 2439090105209169902567143)
                      ·
                        rfl

theorem cell23_4750111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_4750111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750111 prefixEnd_4750111 := by exact prefixLift 4750111
  have htrace : WordTrace (prefixWord ++ tailWord_4750111) baseStart_4750111 baseEnd_4750111 := by
    simpa [prefixWord, tailWord_4750111, baseEnd_4750111] using wordTrace_append hprefix tailTrace_4750111
  have hstable : (prefixWord ++ tailWord_4750111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750111).length < 2 ^ (prefixWord ++ tailWord_4750111).sum := by decide
  have hdescent : baseEnd_4750111 < baseStart_4750111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750144 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 7]
def baseStart_4750144 : Nat := 118140960795 + 4750144 * 2 ^ 59
def prefixEnd_4750144 : Nat := 4983230072969 + 3 ^ 40 * 4750144 * 2
def baseEnd_4750144 : Nat := 2439107050070768273454491

theorem tailTrace_4750144 : CollatzResearch.WordTrace tailWord_4750144 prefixEnd_4750144 2439107050070768273454491 := by
  unfold tailWord_4750144
  simp only [CollatzResearch.WordTrace]
  refine ⟨86625992451523511426300743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115501323268698015235067657 86625992451523511426300743)
  ·
    refine ⟨129938988677285267139451115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86625992451523511426300743 129938988677285267139451115)
    ·
      refine ⟨194908483015927900709176673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129938988677285267139451115 194908483015927900709176673)
      ·
        refine ⟨146181362261945925531882505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194908483015927900709176673 146181362261945925531882505)
        ·
          refine ⟨109636021696459444148911879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146181362261945925531882505 109636021696459444148911879)
          ·
            refine ⟨164454032544689166223367819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109636021696459444148911879 164454032544689166223367819)
            ·
              refine ⟨246681048817033749335051729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164454032544689166223367819 246681048817033749335051729)
              ·
                refine ⟨185010786612775312001288797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 246681048817033749335051729 185010786612775312001288797)
                ·
                  refine ⟨69379044979790742000483299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 185010786612775312001288797 69379044979790742000483299)
                  ·
                    refine ⟨104068567469686113000724949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69379044979790742000483299 104068567469686113000724949)
                    ·
                      refine ⟨2439107050070768273454491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 104068567469686113000724949 2439107050070768273454491)
                      ·
                        rfl

theorem cell23_4750144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_4750144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750144 prefixEnd_4750144 := by exact prefixLift 4750144
  have htrace : WordTrace (prefixWord ++ tailWord_4750144) baseStart_4750144 baseEnd_4750144 := by
    simpa [prefixWord, tailWord_4750144, baseEnd_4750144] using wordTrace_append hprefix tailTrace_4750144
  have hstable : (prefixWord ++ tailWord_4750144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750144).length < 2 ^ (prefixWord ++ tailWord_4750144).sum := by decide
  have hdescent : baseEnd_4750144 < baseStart_4750144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750188 : List Nat := [2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 4]
def baseStart_4750188 : Nat := 118140960795 + 4750188 * 2 ^ 59
def prefixEnd_4750188 : Nat := 4983230072969 + 3 ^ 40 * 4750188 * 2
def baseEnd_4750188 : Nat := 2439129643219566101304289

theorem tailTrace_4750188 : CollatzResearch.WordTrace tailWord_4750188 prefixEnd_4750188 2439129643219566101304289 := by
  unfold tailWord_4750188
  simp only [CollatzResearch.WordTrace]
  refine ⟨86626794857443809183601609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115502393143258412244802145 86626794857443809183601609)
  ·
    refine ⟨64970096143082856887701207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86626794857443809183601609 64970096143082856887701207)
    ·
      refine ⟨97455144214624285331551811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64970096143082856887701207 97455144214624285331551811)
      ·
        refine ⟨146182716321936427997327717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97455144214624285331551811 146182716321936427997327717)
        ·
          refine ⟨27409259310363080249498947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 146182716321936427997327717 27409259310363080249498947)
          ·
            refine ⟨41113888965544620374248421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27409259310363080249498947 41113888965544620374248421)
            ·
              refine ⟨7708854181039616320171579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41113888965544620374248421 7708854181039616320171579)
              ·
                refine ⟨11563281271559424480257369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7708854181039616320171579 11563281271559424480257369)
                ·
                  refine ⟨8672460953669568360193027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11563281271559424480257369 8672460953669568360193027)
                  ·
                    refine ⟨13008691430504352540289541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8672460953669568360193027 13008691430504352540289541)
                    ·
                      refine ⟨2439129643219566101304289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13008691430504352540289541 2439129643219566101304289)
                      ·
                        rfl

theorem cell23_4750188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 4].length) (baseStart_4750188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750188 prefixEnd_4750188 := by exact prefixLift 4750188
  have htrace : WordTrace (prefixWord ++ tailWord_4750188) baseStart_4750188 baseEnd_4750188 := by
    simpa [prefixWord, tailWord_4750188, baseEnd_4750188] using wordTrace_append hprefix tailTrace_4750188
  have hstable : (prefixWord ++ tailWord_4750188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750188).length < 2 ^ (prefixWord ++ tailWord_4750188).sum := by decide
  have hdescent : baseEnd_4750188 < baseStart_4750188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750191 : List Nat := [1, 1, 2, 1, 3, 1, 1, 5, 1, 4, 3]
def baseStart_4750191 : Nat := 118140960795 + 4750191 * 2 ^ 59
def prefixEnd_4750191 : Nat := 4983230072969 + 3 ^ 40 * 4750191 * 2
def baseEnd_4750191 : Nat := 2439131183661529589566775

theorem tailTrace_4750191 : CollatzResearch.WordTrace tailWord_4750191 prefixEnd_4750191 2439131183661529589566775 := by
  unfold tailWord_4750191
  simp only [CollatzResearch.WordTrace]
  refine ⟨173253699133876749879562427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115502466089251166586374951 173253699133876749879562427)
  ·
    refine ⟨259880548700815124819343641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173253699133876749879562427 259880548700815124819343641)
    ·
      refine ⟨194910411525611343614507731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259880548700815124819343641 194910411525611343614507731)
      ·
        refine ⟨292365617288417015421761597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194910411525611343614507731 292365617288417015421761597)
        ·
          refine ⟨109637106483156380783160599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 292365617288417015421761597 109637106483156380783160599)
          ·
            refine ⟨164455659724734571174740899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109637106483156380783160599 164455659724734571174740899)
            ·
              refine ⟨246683489587101856762111349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164455659724734571174740899 246683489587101856762111349)
              ·
                refine ⟨23126577148790799071447939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 246683489587101856762111349 23126577148790799071447939)
                ·
                  refine ⟨34689865723186198607171909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23126577148790799071447939 34689865723186198607171909)
                  ·
                    refine ⟨6504349823097412238844733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34689865723186198607171909 6504349823097412238844733)
                    ·
                      refine ⟨2439131183661529589566775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6504349823097412238844733 2439131183661529589566775)
                      ·
                        rfl

theorem cell23_4750191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 4, 3].length) (baseStart_4750191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750191 prefixEnd_4750191 := by exact prefixLift 4750191
  have htrace : WordTrace (prefixWord ++ tailWord_4750191) baseStart_4750191 baseEnd_4750191 := by
    simpa [prefixWord, tailWord_4750191, baseEnd_4750191] using wordTrace_append hprefix tailTrace_4750191
  have hstable : (prefixWord ++ tailWord_4750191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750191).length < 2 ^ (prefixWord ++ tailWord_4750191).sum := by decide
  have hdescent : baseEnd_4750191 < baseStart_4750191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750206 : List Nat := [4, 2, 3, 1, 3, 1, 2, 2, 5]
def baseStart_4750206 : Nat := 118140960795 + 4750206 * 2 ^ 59
def prefixEnd_4750206 : Nat := 4983230072969 + 3 ^ 40 * 4750206 * 2
def baseEnd_4750206 : Nat := 271015431763483003431023

theorem tailTrace_4750206 : CollatzResearch.WordTrace tailWord_4750206 prefixEnd_4750206 271015431763483003431023 := by
  unfold tailWord_4750206
  simp only [CollatzResearch.WordTrace]
  refine ⟨21656780778602800930169809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115502830819214938294238981 21656780778602800930169809)
  ·
    refine ⟨16242585583952100697627357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21656780778602800930169809 16242585583952100697627357)
    ·
      refine ⟨6090969593982037761610259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16242585583952100697627357 6090969593982037761610259)
      ·
        refine ⟨9136454390973056642415389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6090969593982037761610259 9136454390973056642415389)
        ·
          refine ⟨3426170396614896240905771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9136454390973056642415389 3426170396614896240905771)
          ·
            refine ⟨5139255594922344361358657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3426170396614896240905771 5139255594922344361358657)
            ·
              refine ⟨3854441696191758271018993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5139255594922344361358657 3854441696191758271018993)
              ·
                refine ⟨2890831272143818703264245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3854441696191758271018993 2890831272143818703264245)
                ·
                  refine ⟨271015431763483003431023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2890831272143818703264245 271015431763483003431023)
                  ·
                    rfl

theorem cell23_4750206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_4750206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750206 prefixEnd_4750206 := by exact prefixLift 4750206
  have htrace : WordTrace (prefixWord ++ tailWord_4750206) baseStart_4750206 baseEnd_4750206 := by
    simpa [prefixWord, tailWord_4750206, baseEnd_4750206] using wordTrace_append hprefix tailTrace_4750206
  have hstable : (prefixWord ++ tailWord_4750206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750206).length < 2 ^ (prefixWord ++ tailWord_4750206).sum := by decide
  have hdescent : baseEnd_4750206 < baseStart_4750206 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750228 : List Nat := [2, 4, 2, 1, 1, 1, 1, 5, 6]
def baseStart_4750228 : Nat := 118140960795 + 4750228 * 2 ^ 59
def prefixEnd_4750228 : Nat := 4983230072969 + 3 ^ 40 * 4750228 * 2
def baseEnd_4750228 : Nat := 271016686938416216089345

theorem tailTrace_4750228 : CollatzResearch.WordTrace tailWord_4750228 prefixEnd_4750228 271016686938416216089345 := by
  unfold tailWord_4750228
  simp only [CollatzResearch.WordTrace]
  refine ⟨86627524317371352599329669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115503365756495136799106225 86627524317371352599329669)
  ·
    refine ⟨16242660809507128612374313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86627524317371352599329669 16242660809507128612374313)
    ·
      refine ⟨12181995607130346459280735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16242660809507128612374313 12181995607130346459280735)
      ·
        refine ⟨18272993410695519688921103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12181995607130346459280735 18272993410695519688921103)
        ·
          refine ⟨27409490116043279533381655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18272993410695519688921103 27409490116043279533381655)
          ·
            refine ⟨41114235174064919300072483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27409490116043279533381655 41114235174064919300072483)
            ·
              refine ⟨61671352761097378950108725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41114235174064919300072483 61671352761097378950108725)
              ·
                refine ⟨5781689321352879276572693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61671352761097378950108725 5781689321352879276572693)
                ·
                  refine ⟨271016686938416216089345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5781689321352879276572693 271016686938416216089345)
                  ·
                    rfl

theorem cell23_4750228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_4750228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750228 prefixEnd_4750228 := by exact prefixLift 4750228
  have htrace : WordTrace (prefixWord ++ tailWord_4750228) baseStart_4750228 baseEnd_4750228 := by
    simpa [prefixWord, tailWord_4750228, baseEnd_4750228] using wordTrace_append hprefix tailTrace_4750228
  have hstable : (prefixWord ++ tailWord_4750228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750228).length < 2 ^ (prefixWord ++ tailWord_4750228).sum := by decide
  have hdescent : baseEnd_4750228 < baseStart_4750228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750242 : List Nat := [3, 3, 1, 2, 2, 3, 1, 1, 2, 2, 3]
def baseStart_4750242 : Nat := 118140960795 + 4750242 * 2 ^ 59
def prefixEnd_4750242 : Nat := 4983230072969 + 3 ^ 40 * 4750242 * 2
def baseEnd_4750242 : Nat := 2439157371174908890029041

theorem tailTrace_4750242 : CollatzResearch.WordTrace tailWord_4750242 prefixEnd_4750242 2439157371174908890029041 := by
  unfold tailWord_4750242
  simp only [CollatzResearch.WordTrace]
  refine ⟨43313889814172996397417245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115503706171127990393112653 43313889814172996397417245)
  ·
    refine ⟨16242708680314873649031467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43313889814172996397417245 16242708680314873649031467)
    ·
      refine ⟨24364063020472310473547201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16242708680314873649031467 24364063020472310473547201)
      ·
        refine ⟨18273047265354232855160401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24364063020472310473547201 18273047265354232855160401)
        ·
          refine ⟨13704785449015674641370301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18273047265354232855160401 13704785449015674641370301)
          ·
            refine ⟨5139294543380877990513863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13704785449015674641370301 5139294543380877990513863)
            ·
              refine ⟨7708941815071316985770795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5139294543380877990513863 7708941815071316985770795)
              ·
                refine ⟨11563412722606975478656193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7708941815071316985770795 11563412722606975478656193)
                ·
                  refine ⟨8672559541955231608992145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11563412722606975478656193 8672559541955231608992145)
                  ·
                    refine ⟨6504419656466423706744109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8672559541955231608992145 6504419656466423706744109)
                    ·
                      refine ⟨2439157371174908890029041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6504419656466423706744109 2439157371174908890029041)
                      ·
                        rfl

theorem cell23_4750242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_4750242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750242 prefixEnd_4750242 := by exact prefixLift 4750242
  have htrace : WordTrace (prefixWord ++ tailWord_4750242) baseStart_4750242 baseEnd_4750242 := by
    simpa [prefixWord, tailWord_4750242, baseEnd_4750242] using wordTrace_append hprefix tailTrace_4750242
  have hstable : (prefixWord ++ tailWord_4750242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750242).length < 2 ^ (prefixWord ++ tailWord_4750242).sum := by decide
  have hdescent : baseEnd_4750242 < baseStart_4750242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750272 : List Nat := [2, 1, 1, 2, 3, 3, 2, 4, 1, 1, 3]
def baseStart_4750272 : Nat := 118140960795 + 4750272 * 2 ^ 59
def prefixEnd_4750272 : Nat := 4983230072969 + 3 ^ 40 * 4750272 * 2
def baseEnd_4750272 : Nat := 2439172775594543772653903

theorem tailTrace_4750272 : CollatzResearch.WordTrace tailWord_4750272 prefixEnd_4750272 2439172775594543772653903 := by
  unfold tailWord_4750272
  simp only [CollatzResearch.WordTrace]
  refine ⟨86628326723291650356630535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115504435631055533808840713 86628326723291650356630535)
  ·
    refine ⟨129942490084937475534945803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86628326723291650356630535 129942490084937475534945803)
    ·
      refine ⟨194913735127406213302418705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129942490084937475534945803 194913735127406213302418705)
      ·
        refine ⟨146185301345554659976814029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194913735127406213302418705 146185301345554659976814029)
        ·
          refine ⟨54819488004582997491305261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146185301345554659976814029 54819488004582997491305261)
          ·
            refine ⟨20557308001718624059239473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54819488004582997491305261 20557308001718624059239473)
            ·
              refine ⟨15417981001288968044429605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20557308001718624059239473 15417981001288968044429605)
              ·
                refine ⟨2890871437741681508330551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15417981001288968044429605 2890871437741681508330551)
                ·
                  refine ⟨4336307156612522262495827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2890871437741681508330551 4336307156612522262495827)
                  ·
                    refine ⟨6504460734918783393743741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4336307156612522262495827 6504460734918783393743741)
                    ·
                      refine ⟨2439172775594543772653903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6504460734918783393743741 2439172775594543772653903)
                      ·
                        rfl

theorem cell23_4750272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 4, 1, 1, 3].length) (baseStart_4750272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750272 prefixEnd_4750272 := by exact prefixLift 4750272
  have htrace : WordTrace (prefixWord ++ tailWord_4750272) baseStart_4750272 baseEnd_4750272 := by
    simpa [prefixWord, tailWord_4750272, baseEnd_4750272] using wordTrace_append hprefix tailTrace_4750272
  have hstable : (prefixWord ++ tailWord_4750272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750272).length < 2 ^ (prefixWord ++ tailWord_4750272).sum := by decide
  have hdescent : baseEnd_4750272 < baseStart_4750272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750295 : List Nat := [1, 1, 3, 2, 1, 1, 2, 3, 5, 2, 2]
def baseStart_4750295 : Nat := 118140960795 + 4750295 * 2 ^ 59
def prefixEnd_4750295 : Nat := 4983230072969 + 3 ^ 40 * 4750295 * 2
def baseEnd_4750295 : Nat := 2439184585649597182666297

theorem tailTrace_4750295 : CollatzResearch.WordTrace tailWord_4750295 prefixEnd_4750295 2439184585649597182666297 := by
  unfold tailWord_4750295
  simp only [CollatzResearch.WordTrace]
  refine ⟨173257492325499975641348339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115504994883666650427565559 173257492325499975641348339)
  ·
    refine ⟨259886238488249963462022509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173257492325499975641348339 259886238488249963462022509)
    ·
      refine ⟨97457339433093736298258441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 259886238488249963462022509 97457339433093736298258441)
      ·
        refine ⟨73093004574820302223693831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97457339433093736298258441 73093004574820302223693831)
        ·
          refine ⟨109639506862230453335540747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73093004574820302223693831 109639506862230453335540747)
          ·
            refine ⟨164459260293345680003311121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109639506862230453335540747 164459260293345680003311121)
            ·
              refine ⟨123344445220009260002483341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164459260293345680003311121 123344445220009260002483341)
              ·
                refine ⟨46254166957503472500931253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123344445220009260002483341 46254166957503472500931253)
                ·
                  refine ⟨4336328152265950546962305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46254166957503472500931253 4336328152265950546962305)
                  ·
                    refine ⟨3252246114199462910221729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4336328152265950546962305 3252246114199462910221729)
                    ·
                      refine ⟨2439184585649597182666297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3252246114199462910221729 2439184585649597182666297)
                      ·
                        rfl

theorem cell23_4750295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 5, 2, 2].length) (baseStart_4750295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750295 prefixEnd_4750295 := by exact prefixLift 4750295
  have htrace : WordTrace (prefixWord ++ tailWord_4750295) baseStart_4750295 baseEnd_4750295 := by
    simpa [prefixWord, tailWord_4750295, baseEnd_4750295] using wordTrace_append hprefix tailTrace_4750295
  have hstable : (prefixWord ++ tailWord_4750295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750295).length < 2 ^ (prefixWord ++ tailWord_4750295).sum := by decide
  have hdescent : baseEnd_4750295 < baseStart_4750295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750306 : List Nat := [3, 3, 3, 1, 1, 1, 3, 3, 1, 1, 3]
def baseStart_4750306 : Nat := 118140960795 + 4750306 * 2 ^ 59
def prefixEnd_4750306 : Nat := 4983230072969 + 3 ^ 40 * 4750306 * 2
def baseEnd_4750306 : Nat := 2439190233936796639628747

theorem tailTrace_4750306 : CollatzResearch.WordTrace tailWord_4750306 prefixEnd_4750306 2439190233936796639628747 := by
  unfold tailWord_4750306
  simp only [CollatzResearch.WordTrace]
  refine ⟨43314473382115031129999693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115505262352306749679999181 43314473382115031129999693)
  ·
    refine ⟨16242927518293136673749885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43314473382115031129999693 16242927518293136673749885)
    ·
      refine ⟨6091097819359926252656207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16242927518293136673749885 6091097819359926252656207)
      ·
        refine ⟨9136646729039889378984311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6091097819359926252656207 9136646729039889378984311)
        ·
          refine ⟨13704970093559834068476467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9136646729039889378984311 13704970093559834068476467)
          ·
            refine ⟨20557455140339751102714701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13704970093559834068476467 20557455140339751102714701)
            ·
              refine ⟨7709045677627406663518013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20557455140339751102714701 7709045677627406663518013)
              ·
                refine ⟨2890892129110277498819255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7709045677627406663518013 2890892129110277498819255)
                ·
                  refine ⟨4336338193665416248228883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2890892129110277498819255 4336338193665416248228883)
                  ·
                    refine ⟨6504507290498124372343325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4336338193665416248228883 6504507290498124372343325)
                    ·
                      refine ⟨2439190233936796639628747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6504507290498124372343325 2439190233936796639628747)
                      ·
                        rfl

theorem cell23_4750306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_4750306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750306 prefixEnd_4750306 := by exact prefixLift 4750306
  have htrace : WordTrace (prefixWord ++ tailWord_4750306) baseStart_4750306 baseEnd_4750306 := by
    simpa [prefixWord, tailWord_4750306, baseEnd_4750306] using wordTrace_append hprefix tailTrace_4750306
  have hstable : (prefixWord ++ tailWord_4750306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750306).length < 2 ^ (prefixWord ++ tailWord_4750306).sum := by decide
  have hdescent : baseEnd_4750306 < baseStart_4750306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750331 : List Nat := [1, 1, 1, 1, 1, 3, 3, 3, 2, 7]
def baseStart_4750331 : Nat := 118140960795 + 4750331 * 2 ^ 59
def prefixEnd_4750331 : Nat := 4983230072969 + 3 ^ 40 * 4750331 * 2
def baseEnd_4750331 : Nat := 813067690317719680605377

theorem tailTrace_4750331 : CollatzResearch.WordTrace tailWord_4750331 prefixEnd_4750331 813067690317719680605377 := by
  unfold tailWord_4750331
  simp only [CollatzResearch.WordTrace]
  refine ⟨173258805353369553789658847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115505870235579702526439231 173258805353369553789658847)
  ·
    refine ⟨259888208030054330684488271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173258805353369553789658847 259888208030054330684488271)
    ·
      refine ⟨389832312045081496026732407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259888208030054330684488271 389832312045081496026732407)
      ·
        refine ⟨584748468067622244040098611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 389832312045081496026732407 584748468067622244040098611)
        ·
          refine ⟨877122702101433366060147917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 584748468067622244040098611 877122702101433366060147917)
          ·
            refine ⟨328921013288037512272555469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 877122702101433366060147917 328921013288037512272555469)
            ·
              refine ⟨123345379983014067102208301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 328921013288037512272555469 123345379983014067102208301)
              ·
                refine ⟨46254517493630275163328113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123345379983014067102208301 46254517493630275163328113)
                ·
                  refine ⟨34690888120222706372496085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46254517493630275163328113 34690888120222706372496085)
                  ·
                    refine ⟨813067690317719680605377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34690888120222706372496085 813067690317719680605377)
                    ·
                      rfl

theorem cell23_4750331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 7].length) (baseStart_4750331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750331 prefixEnd_4750331 := by exact prefixLift 4750331
  have htrace : WordTrace (prefixWord ++ tailWord_4750331) baseStart_4750331 baseEnd_4750331 := by
    simpa [prefixWord, tailWord_4750331, baseEnd_4750331] using wordTrace_append hprefix tailTrace_4750331
  have hstable : (prefixWord ++ tailWord_4750331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750331).length < 2 ^ (prefixWord ++ tailWord_4750331).sum := by decide
  have hdescent : baseEnd_4750331 < baseStart_4750331 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750385 : List Nat := [1, 2, 2, 3, 1, 2, 1, 2, 3, 4, 2]
def baseStart_4750385 : Nat := 118140960795 + 4750385 * 2 ^ 59
def prefixEnd_4750385 : Nat := 4983230072969 + 3 ^ 40 * 4750385 * 2
def baseEnd_4750385 : Nat := 2439230798908501830540883

theorem tailTrace_4750385 : CollatzResearch.WordTrace tailWord_4750385 prefixEnd_4750385 2439230798908501830540883 := by
  unfold tailWord_4750385
  simp only [CollatzResearch.WordTrace]
  refine ⟨173260774895173921012124609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115507183263449280674749739 173260774895173921012124609)
  ·
    refine ⟨129945581171380440759093457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173260774895173921012124609 129945581171380440759093457)
    ·
      refine ⟨97459185878535330569320093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129945581171380440759093457 97459185878535330569320093)
      ·
        refine ⟨36547194704450748963495035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97459185878535330569320093 36547194704450748963495035)
        ·
          refine ⟨54820792056676123445242553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36547194704450748963495035 54820792056676123445242553)
          ·
            refine ⟨41115594042507092583931915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54820792056676123445242553 41115594042507092583931915)
            ·
              refine ⟨61673391063760638875897873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41115594042507092583931915 61673391063760638875897873)
              ·
                refine ⟨46255043297820479156923405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61673391063760638875897873 46255043297820479156923405)
                ·
                  refine ⟨17345641236682679683846277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46255043297820479156923405 17345641236682679683846277)
                  ·
                    refine ⟨3252307731878002440721177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17345641236682679683846277 3252307731878002440721177)
                    ·
                      refine ⟨2439230798908501830540883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3252307731878002440721177 2439230798908501830540883)
                      ·
                        rfl

theorem cell23_4750385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 4, 2].length) (baseStart_4750385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750385 prefixEnd_4750385 := by exact prefixLift 4750385
  have htrace : WordTrace (prefixWord ++ tailWord_4750385) baseStart_4750385 baseEnd_4750385 := by
    simpa [prefixWord, tailWord_4750385, baseEnd_4750385] using wordTrace_append hprefix tailTrace_4750385
  have hstable : (prefixWord ++ tailWord_4750385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750385).length < 2 ^ (prefixWord ++ tailWord_4750385).sum := by decide
  have hdescent : baseEnd_4750385 < baseStart_4750385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750408 : List Nat := [2, 1, 3, 1, 1, 1, 5, 2, 7]
def baseStart_4750408 : Nat := 118140960795 + 4750408 * 2 ^ 59
def prefixEnd_4750408 : Nat := 4983230072969 + 3 ^ 40 * 4750408 * 2
def baseEnd_4750408 : Nat := 271026956551506137839253

theorem tailTrace_4750408 : CollatzResearch.WordTrace tailWord_4750408 prefixEnd_4750408 271026956551506137839253 := by
  unfold tailWord_4750408
  simp only [CollatzResearch.WordTrace]
  refine ⟨86630806887045297970105939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115507742516060397293474585 86630806887045297970105939)
  ·
    refine ⟨129946210330567946955158909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86630806887045297970105939 129946210330567946955158909)
    ·
      refine ⟨48729828873962980108184591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129946210330567946955158909 48729828873962980108184591)
      ·
        refine ⟨73094743310944470162276887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48729828873962980108184591 73094743310944470162276887)
        ·
          refine ⟨109642114966416705243415331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73094743310944470162276887 109642114966416705243415331)
          ·
            refine ⟨164463172449625057865122997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109642114966416705243415331 164463172449625057865122997)
            ·
              refine ⟨15418422417152349174855281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 164463172449625057865122997 15418422417152349174855281)
              ·
                refine ⟨11563816812864261881141461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15418422417152349174855281 11563816812864261881141461)
                ·
                  refine ⟨271026956551506137839253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11563816812864261881141461 271026956551506137839253)
                  ·
                    rfl

theorem cell23_4750408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 7].length) (baseStart_4750408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750408 prefixEnd_4750408 := by exact prefixLift 4750408
  have htrace : WordTrace (prefixWord ++ tailWord_4750408) baseStart_4750408 baseEnd_4750408 := by
    simpa [prefixWord, tailWord_4750408, baseEnd_4750408] using wordTrace_append hprefix tailTrace_4750408
  have hstable : (prefixWord ++ tailWord_4750408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750408).length < 2 ^ (prefixWord ++ tailWord_4750408).sum := by decide
  have hdescent : baseEnd_4750408 < baseStart_4750408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750442 : List Nat := [3, 1, 3, 2, 2, 1, 2, 4, 5]
def baseStart_4750442 : Nat := 118140960795 + 4750442 * 2 ^ 59
def prefixEnd_4750442 : Nat := 4983230072969 + 3 ^ 40 * 4750442 * 2
def baseEnd_4750442 : Nat := 271028896367312011947569

theorem tailTrace_4750442 : CollatzResearch.WordTrace tailWord_4750442 prefixEnd_4750442 271028896367312011947569 := by
  unfold tailWord_4750442
  simp only [CollatzResearch.WordTrace]
  refine ⟨43315713463991854936737395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115508569237311613164633053 43315713463991854936737395)
  ·
    refine ⟨64973570195987782405106093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43315713463991854936737395 64973570195987782405106093)
    ·
      refine ⟨24365088823495418401914785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64973570195987782405106093 24365088823495418401914785)
      ·
        refine ⟨18273816617621563801436089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24365088823495418401914785 18273816617621563801436089)
        ·
          refine ⟨13705362463216172851077067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18273816617621563801436089 13705362463216172851077067)
          ·
            refine ⟨20558043694824259276615601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13705362463216172851077067 20558043694824259276615601)
            ·
              refine ⟨15418532771118194457461701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20558043694824259276615601 15418532771118194457461701)
              ·
                refine ⟨2890974894584661460774069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15418532771118194457461701 2890974894584661460774069)
                ·
                  refine ⟨271028896367312011947569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2890974894584661460774069 271028896367312011947569)
                  ·
                    rfl

theorem cell23_4750442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 4, 5].length) (baseStart_4750442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750442 prefixEnd_4750442 := by exact prefixLift 4750442
  have htrace : WordTrace (prefixWord ++ tailWord_4750442) baseStart_4750442 baseEnd_4750442 := by
    simpa [prefixWord, tailWord_4750442, baseEnd_4750442] using wordTrace_append hprefix tailTrace_4750442
  have hstable : (prefixWord ++ tailWord_4750442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750442).length < 2 ^ (prefixWord ++ tailWord_4750442).sum := by decide
  have hdescent : baseEnd_4750442 < baseStart_4750442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750448 : List Nat := [2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 7]
def baseStart_4750448 : Nat := 118140960795 + 4750448 * 2 ^ 59
def prefixEnd_4750448 : Nat := 4983230072969 + 3 ^ 40 * 4750448 * 2
def baseEnd_4750448 : Nat := 2439263148189735084053093

theorem tailTrace_4750448 : CollatzResearch.WordTrace tailWord_4750448 prefixEnd_4750448 2439263148189735084053093 := by
  unfold tailWord_4750448
  simp only [CollatzResearch.WordTrace]
  refine ⟨86631536346972841385833999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115508715129297121847778665 86631536346972841385833999)
  ·
    refine ⟨129947304520459262078750999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86631536346972841385833999 129947304520459262078750999)
    ·
      refine ⟨194920956780688893118126499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129947304520459262078750999 194920956780688893118126499)
      ·
        refine ⟨292381435171033339677189749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194920956780688893118126499 292381435171033339677189749)
        ·
          refine ⟨27410759547284375594736539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 292381435171033339677189749 27410759547284375594736539)
          ·
            refine ⟨41116139320926563392104809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27410759547284375594736539 41116139320926563392104809)
            ·
              refine ⟨30837104490694922544078607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41116139320926563392104809 30837104490694922544078607)
              ·
                refine ⟨46255656736042383816117911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30837104490694922544078607 46255656736042383816117911)
                ·
                  refine ⟨69383485104063575724176867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46255656736042383816117911 69383485104063575724176867)
                  ·
                    refine ⟨104075227656095363586265301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69383485104063575724176867 104075227656095363586265301)
                    ·
                      refine ⟨2439263148189735084053093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 104075227656095363586265301 2439263148189735084053093)
                      ·
                        rfl

theorem cell23_4750448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 7].length) (baseStart_4750448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750448 prefixEnd_4750448 := by exact prefixLift 4750448
  have htrace : WordTrace (prefixWord ++ tailWord_4750448) baseStart_4750448 baseEnd_4750448 := by
    simpa [prefixWord, tailWord_4750448, baseEnd_4750448] using wordTrace_append hprefix tailTrace_4750448
  have hstable : (prefixWord ++ tailWord_4750448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750448).length < 2 ^ (prefixWord ++ tailWord_4750448).sum := by decide
  have hdescent : baseEnd_4750448 < baseStart_4750448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750453 : List Nat := [1, 3, 4, 3, 2, 1, 1, 1, 1, 4, 2]
def baseStart_4750453 : Nat := 118140960795 + 4750453 * 2 ^ 59
def prefixEnd_4750453 : Nat := 4983230072969 + 3 ^ 40 * 4750453 * 2
def baseEnd_4750453 : Nat := 2439265715593007564490571

theorem tailTrace_4750453 : CollatzResearch.WordTrace tailWord_4750453 prefixEnd_4750453 2439265715593007564490571 := by
  unfold tailWord_4750453
  simp only [CollatzResearch.WordTrace]
  refine ⟨173263255058927568625600013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115508836705951712417066675 173263255058927568625600013)
  ·
    refine ⟨64973720647097838234600005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173263255058927568625600013 64973720647097838234600005)
    ·
      refine ⟨12182572621330844668987501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64973720647097838234600005 12182572621330844668987501)
      ·
        refine ⟨4568464732999066750870313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12182572621330844668987501 4568464732999066750870313)
        ·
          refine ⟨3426348549749300063152735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4568464732999066750870313 3426348549749300063152735)
          ·
            refine ⟨5139522824623950094729103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3426348549749300063152735 5139522824623950094729103)
            ·
              refine ⟨7709284236935925142093655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5139522824623950094729103 7709284236935925142093655)
              ·
                refine ⟨11563926355403887713140483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7709284236935925142093655 11563926355403887713140483)
                ·
                  refine ⟨17345889533105831569710725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11563926355403887713140483 17345889533105831569710725)
                  ·
                    refine ⟨3252354287457343419320761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17345889533105831569710725 3252354287457343419320761)
                    ·
                      refine ⟨2439265715593007564490571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3252354287457343419320761 2439265715593007564490571)
                      ·
                        rfl

theorem cell23_4750453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_4750453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750453 prefixEnd_4750453 := by exact prefixLift 4750453
  have htrace : WordTrace (prefixWord ++ tailWord_4750453) baseStart_4750453 baseEnd_4750453 := by
    simpa [prefixWord, tailWord_4750453, baseEnd_4750453] using wordTrace_append hprefix tailTrace_4750453
  have hstable : (prefixWord ++ tailWord_4750453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750453).length < 2 ^ (prefixWord ++ tailWord_4750453).sum := by decide
  have hdescent : baseEnd_4750453 < baseStart_4750453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750475 : List Nat := [1, 1, 1, 1, 4, 1, 1, 4, 1, 6, 2]
def baseStart_4750475 : Nat := 118140960795 + 4750475 * 2 ^ 59
def prefixEnd_4750475 : Nat := 4983230072969 + 3 ^ 40 * 4750475 * 2
def baseEnd_4750475 : Nat := 2439277012167406478415469

theorem tailTrace_4750475 : CollatzResearch.WordTrace tailWord_4750475 prefixEnd_4750475 2439277012167406478415469 := by
  unfold tailWord_4750475
  simp only [CollatzResearch.WordTrace]
  refine ⟨173264057464847866382900879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115509371643231910921933919 173264057464847866382900879)
  ·
    refine ⟨259896086197271799574351319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173264057464847866382900879 259896086197271799574351319)
    ·
      refine ⟨389844129295907699361526979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259896086197271799574351319 389844129295907699361526979)
      ·
        refine ⟨584766193943861549042290469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 389844129295907699361526979 584766193943861549042290469)
        ·
          refine ⟨109643661364474040445429463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 584766193943861549042290469 109643661364474040445429463)
          ·
            refine ⟨164465492046711060668144195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109643661364474040445429463 164465492046711060668144195)
            ·
              refine ⟨246698238070066591002216293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164465492046711060668144195 246698238070066591002216293)
              ·
                refine ⟨46255919638137485812915555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 246698238070066591002216293 46255919638137485812915555)
                ·
                  refine ⟨69383879457206228719373333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46255919638137485812915555 69383879457206228719373333)
                  ·
                    refine ⟨3252369349556541971220625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 69383879457206228719373333 3252369349556541971220625)
                    ·
                      refine ⟨2439277012167406478415469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3252369349556541971220625 2439277012167406478415469)
                      ·
                        rfl

theorem cell23_4750475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 6, 2].length) (baseStart_4750475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750475 prefixEnd_4750475 := by exact prefixLift 4750475
  have htrace : WordTrace (prefixWord ++ tailWord_4750475) baseStart_4750475 baseEnd_4750475 := by
    simpa [prefixWord, tailWord_4750475, baseEnd_4750475] using wordTrace_append hprefix tailTrace_4750475
  have hstable : (prefixWord ++ tailWord_4750475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750475).length < 2 ^ (prefixWord ++ tailWord_4750475).sum := by decide
  have hdescent : baseEnd_4750475 < baseStart_4750475 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750492 : List Nat := [2, 2, 3, 2, 1, 3, 1, 2, 2, 1, 4]
def baseStart_4750492 : Nat := 118140960795 + 4750492 * 2 ^ 59
def prefixEnd_4750492 : Nat := 4983230072969 + 3 ^ 40 * 4750492 * 2
def baseEnd_4750492 : Nat := 2439285741338532911902891

theorem tailTrace_4750492 : CollatzResearch.WordTrace tailWord_4750492 prefixEnd_4750492 2439285741338532911902891 := by
  unfold tailWord_4750492
  simp only [CollatzResearch.WordTrace]
  refine ⟨86632338752893139143134865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115509785003857518857513153 86632338752893139143134865)
  ·
    refine ⟨64974254064669854357351149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86632338752893139143134865 64974254064669854357351149)
    ·
      refine ⟨24365345274251195384006681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64974254064669854357351149 24365345274251195384006681)
      ·
        refine ⟨18274008955688396538005011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24365345274251195384006681 18274008955688396538005011)
        ·
          refine ⟨27411013433532594807007517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18274008955688396538005011 27411013433532594807007517)
          ·
            refine ⟨10279130037574723052627819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27411013433532594807007517 10279130037574723052627819)
            ·
              refine ⟨15418695056362084578941729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10279130037574723052627819 15418695056362084578941729)
              ·
                refine ⟨11564021292271563434206297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15418695056362084578941729 11564021292271563434206297)
                ·
                  refine ⟨8673015969203672575654723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11564021292271563434206297 8673015969203672575654723)
                  ·
                    refine ⟨13009523953805508863482085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8673015969203672575654723 13009523953805508863482085)
                    ·
                      refine ⟨2439285741338532911902891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13009523953805508863482085 2439285741338532911902891)
                      ·
                        rfl

theorem cell23_4750492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_4750492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750492 prefixEnd_4750492 := by exact prefixLift 4750492
  have htrace : WordTrace (prefixWord ++ tailWord_4750492) baseStart_4750492 baseEnd_4750492 := by
    simpa [prefixWord, tailWord_4750492, baseEnd_4750492] using wordTrace_append hprefix tailTrace_4750492
  have hstable : (prefixWord ++ tailWord_4750492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750492).length < 2 ^ (prefixWord ++ tailWord_4750492).sum := by decide
  have hdescent : baseEnd_4750492 < baseStart_4750492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750525 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 2, 5, 3]
def baseStart_4750525 : Nat := 118140960795 + 4750525 * 2 ^ 59
def prefixEnd_4750525 : Nat := 4983230072969 + 3 ^ 40 * 4750525 * 2
def baseEnd_4750525 : Nat := 2439302686200131282790239

theorem tailTrace_4750525 : CollatzResearch.WordTrace tailWord_4750525 prefixEnd_4750525 2439302686200131282790239 := by
  unfold tailWord_4750525
  simp only [CollatzResearch.WordTrace]
  refine ⟨173265881114666724922221029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115510587409777816614814019 173265881114666724922221029)
  ·
    refine ⟨32487352709000010922916443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173265881114666724922221029 32487352709000010922916443)
    ·
      refine ⟨48731029063500016384374665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32487352709000010922916443 48731029063500016384374665)
      ·
        refine ⟨36548271797625012288280999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48731029063500016384374665 36548271797625012288280999)
        ·
          refine ⟨54822407696437518432421499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36548271797625012288280999 54822407696437518432421499)
          ·
            refine ⟨82233611544656277648632249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54822407696437518432421499 82233611544656277648632249)
            ·
              refine ⟨61675208658492208236474187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82233611544656277648632249 61675208658492208236474187)
              ·
                refine ⟨92512812987738312354711281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61675208658492208236474187 92512812987738312354711281)
                ·
                  refine ⟨69384609740803734266033461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92512812987738312354711281 69384609740803734266033461)
                  ·
                    refine ⟨6504807163200350087440637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 69384609740803734266033461 6504807163200350087440637)
                    ·
                      refine ⟨2439302686200131282790239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6504807163200350087440637 2439302686200131282790239)
                      ·
                        rfl

theorem cell23_4750525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_4750525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750525 prefixEnd_4750525 := by exact prefixLift 4750525
  have htrace : WordTrace (prefixWord ++ tailWord_4750525) baseStart_4750525 baseEnd_4750525 := by
    simpa [prefixWord, tailWord_4750525, baseEnd_4750525] using wordTrace_append hprefix tailTrace_4750525
  have hstable : (prefixWord ++ tailWord_4750525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750525).length < 2 ^ (prefixWord ++ tailWord_4750525).sum := by decide
  have hdescent : baseEnd_4750525 < baseStart_4750525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750529 : List Nat := [1, 2, 6, 1, 1, 1, 1, 3, 2, 2, 3]
def baseStart_4750529 : Nat := 118140960795 + 4750529 * 2 ^ 59
def prefixEnd_4750529 : Nat := 4983230072969 + 3 ^ 40 * 4750529 * 2
def baseEnd_4750529 : Nat := 2439304740122749267140221

theorem tailTrace_4750529 : CollatzResearch.WordTrace tailWord_4750529 prefixEnd_4750529 2439304740122749267140221 := by
  unfold tailWord_4750529
  simp only [CollatzResearch.WordTrace]
  refine ⟨173266027006652233605366641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115510684671101489070244427 173266027006652233605366641)
  ·
    refine ⟨129949520254989175204024981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173266027006652233605366641 129949520254989175204024981)
    ·
      refine ⟨6091383761952617587688671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 129949520254989175204024981 6091383761952617587688671)
      ·
        refine ⟨9137075642928926381533007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6091383761952617587688671 9137075642928926381533007)
        ·
          refine ⟨13705613464393389572299511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9137075642928926381533007 13705613464393389572299511)
          ·
            refine ⟨20558420196590084358449267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13705613464393389572299511 20558420196590084358449267)
            ·
              refine ⟨30837630294885126537673901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20558420196590084358449267 30837630294885126537673901)
              ·
                refine ⟨11564111360581922451627713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30837630294885126537673901 11564111360581922451627713)
                ·
                  refine ⟨8673083520436441838720785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11564111360581922451627713 8673083520436441838720785)
                  ·
                    refine ⟨6504812640327331379040589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8673083520436441838720785 6504812640327331379040589)
                    ·
                      refine ⟨2439304740122749267140221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6504812640327331379040589 2439304740122749267140221)
                      ·
                        rfl

theorem cell23_4750529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_4750529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750529 prefixEnd_4750529 := by exact prefixLift 4750529
  have htrace : WordTrace (prefixWord ++ tailWord_4750529) baseStart_4750529 baseEnd_4750529 := by
    simpa [prefixWord, tailWord_4750529, baseEnd_4750529] using wordTrace_append hprefix tailTrace_4750529
  have hstable : (prefixWord ++ tailWord_4750529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750529).length < 2 ^ (prefixWord ++ tailWord_4750529).sum := by decide
  have hdescent : baseEnd_4750529 < baseStart_4750529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750580 : List Nat := [2, 6, 1, 2, 1, 2, 1, 1, 2, 2, 3]
def baseStart_4750580 : Nat := 118140960795 + 4750580 * 2 ^ 59
def prefixEnd_4750580 : Nat := 4983230072969 + 3 ^ 40 * 4750580 * 2
def baseEnd_4750580 : Nat := 2439330927636128567602487

theorem tailTrace_4750580 : CollatzResearch.WordTrace tailWord_4750580 prefixEnd_4750580 2439330927636128567602487 := by
  unfold tailWord_4750580
  simp only [CollatzResearch.WordTrace]
  refine ⟨86633943564733734657736597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115511924752978312876982129 86633943564733734657736597)
  ·
    refine ⟨4060966104596893812081403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 86633943564733734657736597 4060966104596893812081403)
    ·
      refine ⟨6091449156895340718122105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4060966104596893812081403 6091449156895340718122105)
      ·
        refine ⟨4568586867671505538591579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6091449156895340718122105 4568586867671505538591579)
        ·
          refine ⟨6852880301507258307887369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4568586867671505538591579 6852880301507258307887369)
          ·
            refine ⟨5139660226130443730915527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6852880301507258307887369 5139660226130443730915527)
            ·
              refine ⟨7709490339195665596373291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5139660226130443730915527 7709490339195665596373291)
              ·
                refine ⟨11564235508793498394559937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7709490339195665596373291 11564235508793498394559937)
                ·
                  refine ⟨8673176631595123795919953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11564235508793498394559937 8673176631595123795919953)
                  ·
                    refine ⟨6504882473696342846939965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8673176631595123795919953 6504882473696342846939965)
                    ·
                      refine ⟨2439330927636128567602487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6504882473696342846939965 2439330927636128567602487)
                      ·
                        rfl

theorem cell23_4750580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_4750580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750580 prefixEnd_4750580 := by exact prefixLift 4750580
  have htrace : WordTrace (prefixWord ++ tailWord_4750580) baseStart_4750580 baseEnd_4750580 := by
    simpa [prefixWord, tailWord_4750580, baseEnd_4750580] using wordTrace_append hprefix tailTrace_4750580
  have hstable : (prefixWord ++ tailWord_4750580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750580).length < 2 ^ (prefixWord ++ tailWord_4750580).sum := by decide
  have hdescent : baseEnd_4750580 < baseStart_4750580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750596 : List Nat := [2, 3, 2, 2, 2, 3, 2, 1, 1, 5]
def baseStart_4750596 : Nat := 118140960795 + 4750596 * 2 ^ 59
def prefixEnd_4750596 : Nat := 4983230072969 + 3 ^ 40 * 4750596 * 2
def baseEnd_4750596 : Nat := 813113047775533501667471

theorem tailTrace_4750596 : CollatzResearch.WordTrace tailWord_4750596 prefixEnd_4750596 813113047775533501667471 := by
  unfold tailWord_4750596
  simp only [CollatzResearch.WordTrace]
  refine ⟨86634235348704752024027821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115512313798273002698703761 86634235348704752024027821)
  ·
    refine ⟨32487838255764282009010433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86634235348704752024027821 32487838255764282009010433)
    ·
      refine ⟨24365878691823211506757825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32487838255764282009010433 24365878691823211506757825)
      ·
        refine ⟨18274409018867408630068369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24365878691823211506757825 18274409018867408630068369)
        ·
          refine ⟨13705806764150556472551277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18274409018867408630068369 13705806764150556472551277)
          ·
            refine ⟨5139677536556458677206729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13705806764150556472551277 5139677536556458677206729)
            ·
              refine ⟨3854758152417344007905047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5139677536556458677206729 3854758152417344007905047)
              ·
                refine ⟨5782137228626016011857571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3854758152417344007905047 5782137228626016011857571)
                ·
                  refine ⟨8673205842939024017786357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5782137228626016011857571 8673205842939024017786357)
                  ·
                    refine ⟨813113047775533501667471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8673205842939024017786357 813113047775533501667471)
                    ·
                      rfl

theorem cell23_4750596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_4750596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750596 prefixEnd_4750596 := by exact prefixLift 4750596
  have htrace : WordTrace (prefixWord ++ tailWord_4750596) baseStart_4750596 baseEnd_4750596 := by
    simpa [prefixWord, tailWord_4750596, baseEnd_4750596] using wordTrace_append hprefix tailTrace_4750596
  have hstable : (prefixWord ++ tailWord_4750596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750596).length < 2 ^ (prefixWord ++ tailWord_4750596).sum := by decide
  have hdescent : baseEnd_4750596 < baseStart_4750596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750616 : List Nat := [2, 1, 2, 3, 1, 4, 2, 1, 3, 2, 2]
def baseStart_4750616 : Nat := 118140960795 + 4750616 * 2 ^ 59
def prefixEnd_4750616 : Nat := 4983230072969 + 3 ^ 40 * 4750616 * 2
def baseEnd_4750616 : Nat := 2439349412939690426752321

theorem tailTrace_4750616 : CollatzResearch.WordTrace tailWord_4750616 prefixEnd_4750616 2439349412939690426752321 := by
  unfold tailWord_4750616
  simp only [CollatzResearch.WordTrace]
  refine ⟨86634600078668523731891851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115512800104891364975855801 86634600078668523731891851)
  ·
    refine ⟨129951900118002785597837777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86634600078668523731891851 129951900118002785597837777)
    ·
      refine ⟨97463925088502089198378333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129951900118002785597837777 97463925088502089198378333)
      ·
        refine ⟨36548971908188283449391875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97463925088502089198378333 36548971908188283449391875)
        ·
          refine ⟨54823457862282425174087813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36548971908188283449391875 54823457862282425174087813)
          ·
            refine ⟨10279398349177954720141465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54823457862282425174087813 10279398349177954720141465)
            ·
              refine ⟨7709548761883466040106099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10279398349177954720141465 7709548761883466040106099)
              ·
                refine ⟨11564323142825199060159149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7709548761883466040106099 11564323142825199060159149)
                ·
                  refine ⟨4336621178559449647559681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11564323142825199060159149 4336621178559449647559681)
                  ·
                    refine ⟨3252465883919587235669761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4336621178559449647559681 3252465883919587235669761)
                    ·
                      refine ⟨2439349412939690426752321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3252465883919587235669761 2439349412939690426752321)
                      ·
                        rfl

theorem cell23_4750616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 3, 2, 2].length) (baseStart_4750616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750616 prefixEnd_4750616 := by exact prefixLift 4750616
  have htrace : WordTrace (prefixWord ++ tailWord_4750616) baseStart_4750616 baseEnd_4750616 := by
    simpa [prefixWord, tailWord_4750616, baseEnd_4750616] using wordTrace_append hprefix tailTrace_4750616
  have hstable : (prefixWord ++ tailWord_4750616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750616).length < 2 ^ (prefixWord ++ tailWord_4750616).sum := by decide
  have hdescent : baseEnd_4750616 < baseStart_4750616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750626 : List Nat := [3, 3, 1, 1, 5, 1, 1, 1, 1, 6]
def baseStart_4750626 : Nat := 118140960795 + 4750626 * 2 ^ 59
def prefixEnd_4750626 : Nat := 4983230072969 + 3 ^ 40 * 4750626 * 2
def baseEnd_4750626 : Nat := 813118182582078462542425

theorem tailTrace_4750626 : CollatzResearch.WordTrace tailWord_4750626 prefixEnd_4750626 813118182582078462542425 := by
  unfold tailWord_4750626
  simp only [CollatzResearch.WordTrace]
  refine ⟨43317391221825204792911933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115513043258200546114431821 43317391221825204792911933)
  ·
    refine ⟨16244021708184451797341975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43317391221825204792911933 16244021708184451797341975)
    ·
      refine ⟨24366032562276677696012963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16244021708184451797341975 24366032562276677696012963)
      ·
        refine ⟨36549048843415016544019445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24366032562276677696012963 36549048843415016544019445)
        ·
          refine ⟨3426473329070157801001823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36549048843415016544019445 3426473329070157801001823)
          ·
            refine ⟨5139709993605236701502735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3426473329070157801001823 5139709993605236701502735)
            ·
              refine ⟨7709564990407855052254103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5139709993605236701502735 7709564990407855052254103)
              ·
                refine ⟨11564347485611782578381155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7709564990407855052254103 11564347485611782578381155)
                ·
                  refine ⟨17346521228417673867571733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11564347485611782578381155 17346521228417673867571733)
                  ·
                    refine ⟨813118182582078462542425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17346521228417673867571733 813118182582078462542425)
                    ·
                      rfl

theorem cell23_4750626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_4750626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750626 prefixEnd_4750626 := by exact prefixLift 4750626
  have htrace : WordTrace (prefixWord ++ tailWord_4750626) baseStart_4750626 baseEnd_4750626 := by
    simpa [prefixWord, tailWord_4750626, baseEnd_4750626] using wordTrace_append hprefix tailTrace_4750626
  have hstable : (prefixWord ++ tailWord_4750626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750626).length < 2 ^ (prefixWord ++ tailWord_4750626).sum := by decide
  have hdescent : baseEnd_4750626 < baseStart_4750626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750629 : List Nat := [1, 3, 1, 2, 4, 3, 1, 1, 1, 2, 4]
def baseStart_4750629 : Nat := 118140960795 + 4750629 * 2 ^ 59
def prefixEnd_4750629 : Nat := 4983230072969 + 3 ^ 40 * 4750629 * 2
def baseEnd_4750629 : Nat := 2439356088188198875889761

theorem tailTrace_4750629 : CollatzResearch.WordTrace tailWord_4750629 prefixEnd_4750629 2439356088188198875889761 := by
  unfold tailWord_4750629
  simp only [CollatzResearch.WordTrace]
  refine ⟨173269674306289950684006941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115513116204193300456004627 173269674306289950684006941)
  ·
    refine ⟨64976127864858731506502603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173269674306289950684006941 64976127864858731506502603)
    ·
      refine ⟨97464191797288097259753905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64976127864858731506502603 97464191797288097259753905)
      ·
        refine ⟨73098143847966072944815429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97464191797288097259753905 73098143847966072944815429)
        ·
          refine ⟨13705901971493638677152893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73098143847966072944815429 13705901971493638677152893)
          ·
            refine ⟨5139713239310114503932335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13705901971493638677152893 5139713239310114503932335)
            ·
              refine ⟨7709569858965171755898503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5139713239310114503932335 7709569858965171755898503)
              ·
                refine ⟨11564354788447757633847755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7709569858965171755898503 11564354788447757633847755)
                ·
                  refine ⟨17346532182671636450771633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11564354788447757633847755 17346532182671636450771633)
                  ·
                    refine ⟨13009899137003727338078725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17346532182671636450771633 13009899137003727338078725)
                    ·
                      refine ⟨2439356088188198875889761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13009899137003727338078725 2439356088188198875889761)
                      ·
                        rfl

theorem cell23_4750629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 2, 4].length) (baseStart_4750629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750629 prefixEnd_4750629 := by exact prefixLift 4750629
  have htrace : WordTrace (prefixWord ++ tailWord_4750629) baseStart_4750629 baseEnd_4750629 := by
    simpa [prefixWord, tailWord_4750629, baseEnd_4750629] using wordTrace_append hprefix tailTrace_4750629
  have hstable : (prefixWord ++ tailWord_4750629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750629).length < 2 ^ (prefixWord ++ tailWord_4750629).sum := by decide
  have hdescent : baseEnd_4750629 < baseStart_4750629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750665 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 4, 6]
def baseStart_4750665 : Nat := 118140960795 + 4750665 * 2 ^ 59
def prefixEnd_4750665 : Nat := 4983230072969 + 3 ^ 40 * 4750665 * 2
def baseEnd_4750665 : Nat := 813124857830586911679865

theorem tailTrace_4750665 : CollatzResearch.WordTrace tailWord_4750665 prefixEnd_4750665 813124857830586911679865 := by
  unfold tailWord_4750665
  simp only [CollatzResearch.WordTrace]
  refine ⟨173270987334159528832317449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115513991556106352554878299 173270987334159528832317449)
  ·
    refine ⟨129953240500619646624238087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173270987334159528832317449 129953240500619646624238087)
    ·
      refine ⟨194929860750929469936357131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129953240500619646624238087 194929860750929469936357131)
      ·
        refine ⟨292394791126394204904535697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194929860750929469936357131 292394791126394204904535697)
        ·
          refine ⟨219296093344795653678401773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292394791126394204904535697 219296093344795653678401773)
          ·
            refine ⟨82236035004298370129400665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 219296093344795653678401773 82236035004298370129400665)
            ·
              refine ⟨61677026253223777597050499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82236035004298370129400665 61677026253223777597050499)
              ·
                refine ⟨92515539379835666395575749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61677026253223777597050499 92515539379835666395575749)
                ·
                  refine ⟨17346663633719187449170453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92515539379835666395575749 17346663633719187449170453)
                  ·
                    refine ⟨813124857830586911679865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17346663633719187449170453 813124857830586911679865)
                    ·
                      rfl

theorem cell23_4750665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 6].length) (baseStart_4750665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750665 prefixEnd_4750665 := by exact prefixLift 4750665
  have htrace : WordTrace (prefixWord ++ tailWord_4750665) baseStart_4750665 baseEnd_4750665 := by
    simpa [prefixWord, tailWord_4750665, baseEnd_4750665] using wordTrace_append hprefix tailTrace_4750665
  have hstable : (prefixWord ++ tailWord_4750665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750665).length < 2 ^ (prefixWord ++ tailWord_4750665).sum := by decide
  have hdescent : baseEnd_4750665 < baseStart_4750665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750675 : List Nat := [1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 5]
def baseStart_4750675 : Nat := 118140960795 + 4750675 * 2 ^ 59
def prefixEnd_4750675 : Nat := 4983230072969 + 3 ^ 40 * 4750675 * 2
def baseEnd_4750675 : Nat := 2439379708298305695914549

theorem tailTrace_4750675 : CollatzResearch.WordTrace tailWord_4750675 prefixEnd_4750675 2439379708298305695914549 := by
  unfold tailWord_4750675
  simp only [CollatzResearch.WordTrace]
  refine ⟨173271352064123300540181479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115514234709415533693454319 173271352064123300540181479)
  ·
    refine ⟨259907028096184950810272219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173271352064123300540181479 259907028096184950810272219)
    ·
      refine ⟨389860542144277426215408329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259907028096184950810272219 389860542144277426215408329)
      ·
        refine ⟨292395406608208069661556247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 389860542144277426215408329 292395406608208069661556247)
        ·
          refine ⟨438593109912312104492334371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292395406608208069661556247 438593109912312104492334371)
          ·
            refine ⟨657889664868468156738501557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 438593109912312104492334371 657889664868468156738501557)
            ·
              refine ⟨61677156081418889694234521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 657889664868468156738501557 61677156081418889694234521)
              ·
                refine ⟨46257867061064167270675891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61677156081418889694234521 46257867061064167270675891)
                ·
                  refine ⟨69386800591596250906013837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46257867061064167270675891 69386800591596250906013837)
                  ·
                    refine ⟨26020050221848594089755189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 69386800591596250906013837 26020050221848594089755189)
                    ·
                      refine ⟨2439379708298305695914549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26020050221848594089755189 2439379708298305695914549)
                      ·
                        rfl

theorem cell23_4750675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 5].length) (baseStart_4750675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750675 prefixEnd_4750675 := by exact prefixLift 4750675
  have htrace : WordTrace (prefixWord ++ tailWord_4750675) baseStart_4750675 baseEnd_4750675 := by
    simpa [prefixWord, tailWord_4750675, baseEnd_4750675] using wordTrace_append hprefix tailTrace_4750675
  have hstable : (prefixWord ++ tailWord_4750675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750675).length < 2 ^ (prefixWord ++ tailWord_4750675).sum := by decide
  have hdescent : baseEnd_4750675 < baseStart_4750675 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750692 : List Nat := [2, 3, 1, 1, 3, 2, 1, 2, 2, 1, 5]
def baseStart_4750692 : Nat := 118140960795 + 4750692 * 2 ^ 59
def prefixEnd_4750692 : Nat := 4983230072969 + 3 ^ 40 * 4750692 * 2
def baseEnd_4750692 : Nat := 2439388437469432129401971

theorem tailTrace_4750692 : CollatzResearch.WordTrace tailWord_4750692 prefixEnd_4750692 2439388437469432129401971 := by
  unfold tailWord_4750692
  simp only [CollatzResearch.WordTrace]
  refine ⟨86635986052530856221775165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115514648070041141629033553 86635986052530856221775165)
  ·
    refine ⟨32488494769699071083165687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86635986052530856221775165 32488494769699071083165687)
    ·
      refine ⟨48732742154548606624748531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32488494769699071083165687 48732742154548606624748531)
      ·
        refine ⟨73099113231822909937122797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48732742154548606624748531 73099113231822909937122797)
        ·
          refine ⟨27412167461933591226421049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73099113231822909937122797 27412167461933591226421049)
          ·
            refine ⟨20559125596450193419815787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27412167461933591226421049 20559125596450193419815787)
            ·
              refine ⟨30838688394675290129723681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20559125596450193419815787 30838688394675290129723681)
              ·
                refine ⟨23129016296006467597292761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30838688394675290129723681 23129016296006467597292761)
                ·
                  refine ⟨17346762222004850697969571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23129016296006467597292761 17346762222004850697969571)
                  ·
                    refine ⟨26020143333007276046954357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17346762222004850697969571 26020143333007276046954357)
                    ·
                      refine ⟨2439388437469432129401971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26020143333007276046954357 2439388437469432129401971)
                      ·
                        rfl

theorem cell23_4750692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_4750692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750692 prefixEnd_4750692 := by exact prefixLift 4750692
  have htrace : WordTrace (prefixWord ++ tailWord_4750692) baseStart_4750692 baseEnd_4750692 := by
    simpa [prefixWord, tailWord_4750692, baseEnd_4750692] using wordTrace_append hprefix tailTrace_4750692
  have hstable : (prefixWord ++ tailWord_4750692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750692).length < 2 ^ (prefixWord ++ tailWord_4750692).sum := by decide
  have hdescent : baseEnd_4750692 < baseStart_4750692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750723 : List Nat := [1, 1, 1, 3, 5, 2, 2, 2, 2, 2, 2]
def baseStart_4750723 : Nat := 118140960795 + 4750723 * 2 ^ 59
def prefixEnd_4750723 : Nat := 4983230072969 + 3 ^ 40 * 4750723 * 2
def baseEnd_4750723 : Nat := 2439404355369721508114329

theorem tailTrace_4750723 : CollatzResearch.WordTrace tailWord_4750723 prefixEnd_4750723 2439404355369721508114329 := by
  unfold tailWord_4750723
  simp only [CollatzResearch.WordTrace]
  refine ⟨173273102767949404737928823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115515401845299603158619215 173273102767949404737928823)
  ·
    refine ⟨259909654151924107106893235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173273102767949404737928823 259909654151924107106893235)
    ·
      refine ⟨389864481227886160660339853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259909654151924107106893235 389864481227886160660339853)
      ·
        refine ⟨146199180460457310247627445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 389864481227886160660339853 146199180460457310247627445)
        ·
          refine ⟨13706173168167872835715073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 146199180460457310247627445 13706173168167872835715073)
          ·
            refine ⟨10279629876125904626786305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13706173168167872835715073 10279629876125904626786305)
            ·
              refine ⟨7709722407094428470089729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10279629876125904626786305 7709722407094428470089729)
              ·
                refine ⟨5782291805320821352567297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7709722407094428470089729 5782291805320821352567297)
                ·
                  refine ⟨4336718853990616014425473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5782291805320821352567297 4336718853990616014425473)
                  ·
                    refine ⟨3252539140492962010819105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4336718853990616014425473 3252539140492962010819105)
                    ·
                      refine ⟨2439404355369721508114329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3252539140492962010819105 2439404355369721508114329)
                      ·
                        rfl

theorem cell23_4750723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2, 2, 2, 2].length) (baseStart_4750723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750723 prefixEnd_4750723 := by exact prefixLift 4750723
  have htrace : WordTrace (prefixWord ++ tailWord_4750723) baseStart_4750723 baseEnd_4750723 := by
    simpa [prefixWord, tailWord_4750723, baseEnd_4750723] using wordTrace_append hprefix tailTrace_4750723
  have hstable : (prefixWord ++ tailWord_4750723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750723).length < 2 ^ (prefixWord ++ tailWord_4750723).sum := by decide
  have hdescent : baseEnd_4750723 < baseStart_4750723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750792 : List Nat := [2, 1, 3, 1, 3, 1, 1, 2, 2, 1, 6]
def baseStart_4750792 : Nat := 118140960795 + 4750792 * 2 ^ 59
def prefixEnd_4750792 : Nat := 4983230072969 + 3 ^ 40 * 4750792 * 2
def baseEnd_4750792 : Nat := 2439439785534881738151511

theorem tailTrace_4750792 : CollatzResearch.WordTrace tailWord_4750792 prefixEnd_4750792 2439439785534881738151511 := by
  unfold tailWord_4750792
  simp only [CollatzResearch.WordTrace]
  refine ⟨86637809702349714761095315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115517079603132953014793753 86637809702349714761095315)
  ·
    refine ⟨129956714553524572141642973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86637809702349714761095315 129956714553524572141642973)
    ·
      refine ⟨48733767957571714553116115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129956714553524572141642973 48733767957571714553116115)
      ·
        refine ⟨73100651936357571829674173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48733767957571714553116115 73100651936357571829674173)
        ·
          refine ⟨27412744476134089436127815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73100651936357571829674173 27412744476134089436127815)
          ·
            refine ⟨41119116714201134154191723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27412744476134089436127815 41119116714201134154191723)
            ·
              refine ⟨61678675071301701231287585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41119116714201134154191723 61678675071301701231287585)
              ·
                refine ⟨46259006303476275923465689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61678675071301701231287585 46259006303476275923465689)
                ·
                  refine ⟨34694254727607206942599267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46259006303476275923465689 34694254727607206942599267)
                  ·
                    refine ⟨52041382091410810413898901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34694254727607206942599267 52041382091410810413898901)
                    ·
                      refine ⟨2439439785534881738151511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52041382091410810413898901 2439439785534881738151511)
                      ·
                        rfl

theorem cell23_4750792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_4750792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750792 prefixEnd_4750792 := by exact prefixLift 4750792
  have htrace : WordTrace (prefixWord ++ tailWord_4750792) baseStart_4750792 baseEnd_4750792 := by
    simpa [prefixWord, tailWord_4750792, baseEnd_4750792] using wordTrace_append hprefix tailTrace_4750792
  have hstable : (prefixWord ++ tailWord_4750792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750792).length < 2 ^ (prefixWord ++ tailWord_4750792).sum := by decide
  have hdescent : baseEnd_4750792 < baseStart_4750792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750796 : List Nat := [2, 2, 1, 4, 2, 1, 2, 1, 2, 4, 2]
def baseStart_4750796 : Nat := 118140960795 + 4750796 * 2 ^ 59
def prefixEnd_4750796 : Nat := 4983230072969 + 3 ^ 40 * 4750796 * 2
def baseEnd_4750796 : Nat := 2439441839457499722501493

theorem tailTrace_4750796 : CollatzResearch.WordTrace tailWord_4750796 prefixEnd_4750796 2439441839457499722501493 := by
  unfold tailWord_4750796
  simp only [CollatzResearch.WordTrace]
  refine ⟨86637882648342469102668121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115517176864456625470224161 86637882648342469102668121)
  ·
    refine ⟨64978411986256851827001091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86637882648342469102668121 64978411986256851827001091)
    ·
      refine ⟨97467617979385277740501637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64978411986256851827001091 97467617979385277740501637)
      ·
        refine ⟨18275178371134739576344057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97467617979385277740501637 18275178371134739576344057)
        ·
          refine ⟨13706383778351054682258043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18275178371134739576344057 13706383778351054682258043)
          ·
            refine ⟨20559575667526582023387065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13706383778351054682258043 20559575667526582023387065)
            ·
              refine ⟨15419681750644936517540299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20559575667526582023387065 15419681750644936517540299)
              ·
                refine ⟨23129522625967404776310449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15419681750644936517540299 23129522625967404776310449)
                ·
                  refine ⟨17347141969475553582232837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23129522625967404776310449 17347141969475553582232837)
                  ·
                    refine ⟨3252589119276666296668657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17347141969475553582232837 3252589119276666296668657)
                    ·
                      refine ⟨2439441839457499722501493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3252589119276666296668657 2439441839457499722501493)
                      ·
                        rfl

theorem cell23_4750796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_4750796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750796 prefixEnd_4750796 := by exact prefixLift 4750796
  have htrace : WordTrace (prefixWord ++ tailWord_4750796) baseStart_4750796 baseEnd_4750796 := by
    simpa [prefixWord, tailWord_4750796, baseEnd_4750796] using wordTrace_append hprefix tailTrace_4750796
  have hstable : (prefixWord ++ tailWord_4750796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750796).length < 2 ^ (prefixWord ++ tailWord_4750796).sum := by decide
  have hdescent : baseEnd_4750796 < baseStart_4750796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750823 : List Nat := [1, 1, 5, 2, 1, 2, 3, 3, 1, 4]
def baseStart_4750823 : Nat := 118140960795 + 4750823 * 2 ^ 59
def prefixEnd_4750823 : Nat := 4983230072969 + 3 ^ 40 * 4750823 * 2
def baseEnd_4750823 : Nat := 813151901145057038954623

theorem tailTrace_4750823 : CollatzResearch.WordTrace tailWord_4750823 prefixEnd_4750823 813151901145057038954623 := by
  unfold tailWord_4750823
  simp only [CollatzResearch.WordTrace]
  refine ⟨173276750067587121816569123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115517833378391414544379415 173276750067587121816569123)
  ·
    refine ⟨259915125101380682724853685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173276750067587121816569123 259915125101380682724853685)
    ·
      refine ⟨24367042978254439005455033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 259915125101380682724853685 24367042978254439005455033)
      ·
        refine ⟨18275282233690829254091275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24367042978254439005455033 18275282233690829254091275)
        ·
          refine ⟨27412923350536243881136913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18275282233690829254091275 27412923350536243881136913)
          ·
            refine ⟨20559692512902182910852685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27412923350536243881136913 20559692512902182910852685)
            ·
              refine ⟨7709884692338318591569757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20559692512902182910852685 7709884692338318591569757)
              ·
                refine ⟨2891206759626869471838659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7709884692338318591569757 2891206759626869471838659)
                ·
                  refine ⟨4336810139440304207757989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2891206759626869471838659 4336810139440304207757989)
                  ·
                    refine ⟨813151901145057038954623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4336810139440304207757989 813151901145057038954623)
                    ·
                      rfl

theorem cell23_4750823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_4750823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750823 prefixEnd_4750823 := by exact prefixLift 4750823
  have htrace : WordTrace (prefixWord ++ tailWord_4750823) baseStart_4750823 baseEnd_4750823 := by
    simpa [prefixWord, tailWord_4750823, baseEnd_4750823] using wordTrace_append hprefix tailTrace_4750823
  have hstable : (prefixWord ++ tailWord_4750823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750823).length < 2 ^ (prefixWord ++ tailWord_4750823).sum := by decide
  have hdescent : baseEnd_4750823 < baseStart_4750823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750839 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 3, 5, 2]
def baseStart_4750839 : Nat := 118140960795 + 4750839 * 2 ^ 59
def prefixEnd_4750839 : Nat := 4983230072969 + 3 ^ 40 * 4750839 * 2
def baseEnd_4750839 : Nat := 2439463919125643054263795

theorem tailTrace_4750839 : CollatzResearch.WordTrace tailWord_4750839 prefixEnd_4750839 2439463919125643054263795 := by
  unfold tailWord_4750839
  simp only [CollatzResearch.WordTrace]
  refine ⟨173277333635529156549151571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115518222423686104366101047 173277333635529156549151571)
  ·
    refine ⟨259916000453293734823727357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173277333635529156549151571 259916000453293734823727357)
    ·
      refine ⟨97468500169985150558897759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 259916000453293734823727357 97468500169985150558897759)
      ·
        refine ⟨146202750254977725838346639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97468500169985150558897759 146202750254977725838346639)
        ·
          refine ⟨219304125382466588757519959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146202750254977725838346639 219304125382466588757519959)
          ·
            refine ⟨328956188073699883136279939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219304125382466588757519959 328956188073699883136279939)
            ·
              refine ⟨493434282110549824704419909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 328956188073699883136279939 493434282110549824704419909)
              ·
                refine ⟨92518927895728092132078733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 493434282110549824704419909 92518927895728092132078733)
                ·
                  refine ⟨34694597960898034549529525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92518927895728092132078733 34694597960898034549529525)
                  ·
                    refine ⟨3252618558834190739018393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34694597960898034549529525 3252618558834190739018393)
                    ·
                      refine ⟨2439463919125643054263795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3252618558834190739018393 2439463919125643054263795)
                      ·
                        rfl

theorem cell23_4750839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 5, 2].length) (baseStart_4750839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750839 prefixEnd_4750839 := by exact prefixLift 4750839
  have htrace : WordTrace (prefixWord ++ tailWord_4750839) baseStart_4750839 baseEnd_4750839 := by
    simpa [prefixWord, tailWord_4750839, baseEnd_4750839] using wordTrace_append hprefix tailTrace_4750839
  have hstable : (prefixWord ++ tailWord_4750839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750839).length < 2 ^ (prefixWord ++ tailWord_4750839).sum := by decide
  have hdescent : baseEnd_4750839 < baseStart_4750839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750879 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 6, 4]
def baseStart_4750879 : Nat := 118140960795 + 4750879 * 2 ^ 59
def prefixEnd_4750879 : Nat := 4983230072969 + 3 ^ 40 * 4750879 * 2
def baseEnd_4750879 : Nat := 813161486117274299254537

theorem tailTrace_4750879 : CollatzResearch.WordTrace tailWord_4750879 prefixEnd_4750879 813161486117274299254537 := by
  unfold tailWord_4750879
  simp only [CollatzResearch.WordTrace]
  refine ⟨173278792555384243380607691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115519195036922828920405127 173278792555384243380607691)
  ·
    refine ⟨259918188833076365070911537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173278792555384243380607691 259918188833076365070911537)
    ·
      refine ⟨194938641624807273803183653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259918188833076365070911537 194938641624807273803183653)
      ·
        refine ⟨36550995304651363838096935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 194938641624807273803183653 36550995304651363838096935)
        ·
          refine ⟨54826492956977045757145403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36550995304651363838096935 54826492956977045757145403)
          ·
            refine ⟨82239739435465568635718105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54826492956977045757145403 82239739435465568635718105)
            ·
              refine ⟨61679804576599176476788579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82239739435465568635718105 61679804576599176476788579)
              ·
                refine ⟨92519706864898764715182869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61679804576599176476788579 92519706864898764715182869)
                ·
                  refine ⟨4336861259292129596024197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 92519706864898764715182869 4336861259292129596024197)
                  ·
                    refine ⟨813161486117274299254537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4336861259292129596024197 813161486117274299254537)
                    ·
                      rfl

theorem cell23_4750879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 6, 4].length) (baseStart_4750879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750879 prefixEnd_4750879 := by exact prefixLift 4750879
  have htrace : WordTrace (prefixWord ++ tailWord_4750879) baseStart_4750879 baseEnd_4750879 := by
    simpa [prefixWord, tailWord_4750879, baseEnd_4750879] using wordTrace_append hprefix tailTrace_4750879
  have hstable : (prefixWord ++ tailWord_4750879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750879).length < 2 ^ (prefixWord ++ tailWord_4750879).sum := by decide
  have hdescent : baseEnd_4750879 < baseStart_4750879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750883 : List Nat := [1, 1, 1, 4, 5, 1, 3, 1, 1, 5]
def baseStart_4750883 : Nat := 118140960795 + 4750883 * 2 ^ 59
def prefixEnd_4750883 : Nat := 4983230072969 + 3 ^ 40 * 4750883 * 2
def baseEnd_4750883 : Nat := 813162170758146960704531

theorem tailTrace_4750883 : CollatzResearch.WordTrace tailWord_4750883 prefixEnd_4750883 813162170758146960704531 := by
  unfold tailWord_4750883
  simp only [CollatzResearch.WordTrace]
  refine ⟨173278938447369752063753303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115519292298246501375835535 173278938447369752063753303)
  ·
    refine ⟨259918407671054628095629955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173278938447369752063753303 259918407671054628095629955)
    ·
      refine ⟨389877611506581942143444933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259918407671054628095629955 389877611506581942143444933)
      ·
        refine ⟨73102052157484114151895925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 389877611506581942143444933 73102052157484114151895925)
        ·
          refine ⟨6853317389764135701740243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73102052157484114151895925 6853317389764135701740243)
          ·
            refine ⟨10279976084646203552610365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6853317389764135701740243 10279976084646203552610365)
            ·
              refine ⟨3854991031742326332228887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10279976084646203552610365 3854991031742326332228887)
              ·
                refine ⟨5782486547613489498343331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3854991031742326332228887 5782486547613489498343331)
                ·
                  refine ⟨8673729821420234247514997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5782486547613489498343331 8673729821420234247514997)
                  ·
                    refine ⟨813162170758146960704531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8673729821420234247514997 813162170758146960704531)
                    ·
                      rfl

theorem cell23_4750883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 1, 1, 5].length) (baseStart_4750883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750883 prefixEnd_4750883 := by exact prefixLift 4750883
  have htrace : WordTrace (prefixWord ++ tailWord_4750883) baseStart_4750883 baseEnd_4750883 := by
    simpa [prefixWord, tailWord_4750883, baseEnd_4750883] using wordTrace_append hprefix tailTrace_4750883
  have hstable : (prefixWord ++ tailWord_4750883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750883).length < 2 ^ (prefixWord ++ tailWord_4750883).sum := by decide
  have hdescent : baseEnd_4750883 < baseStart_4750883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750934 : List Nat := [5, 2, 2, 2, 1, 2, 2, 1, 1, 5]
def baseStart_4750934 : Nat := 118140960795 + 4750934 * 2 ^ 59
def prefixEnd_4750934 : Nat := 4983230072969 + 3 ^ 40 * 4750934 * 2
def baseEnd_4750934 : Nat := 813170899929273394191953

theorem tailTrace_4750934 : CollatzResearch.WordTrace tailWord_4750934 prefixEnd_4750934 813170899929273394191953 := by
  unfold tailWord_4750934
  simp only [CollatzResearch.WordTrace]
  refine ⟨10830049910636561735866241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115520532380123325182573237 10830049910636561735866241)
  ·
    refine ⟨8122537432977421301899681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10830049910636561735866241 8122537432977421301899681)
    ·
      refine ⟨6091903074733065976424761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8122537432977421301899681 6091903074733065976424761)
      ·
        refine ⟨4568927306049799482318571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6091903074733065976424761 4568927306049799482318571)
        ·
          refine ⟨6853390959074699223477857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4568927306049799482318571 6853390959074699223477857)
          ·
            refine ⟨5140043219306024417608393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6853390959074699223477857 5140043219306024417608393)
            ·
              refine ⟨3855032414479518313206295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5140043219306024417608393 3855032414479518313206295)
              ·
                refine ⟨5782548621719277469809443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3855032414479518313206295 5782548621719277469809443)
                ·
                  refine ⟨8673822932578916204714165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5782548621719277469809443 8673822932578916204714165)
                  ·
                    refine ⟨813170899929273394191953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8673822932578916204714165 813170899929273394191953)
                    ·
                      rfl

theorem cell23_4750934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_4750934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750934 prefixEnd_4750934 := by exact prefixLift 4750934
  have htrace : WordTrace (prefixWord ++ tailWord_4750934) baseStart_4750934 baseEnd_4750934 := by
    simpa [prefixWord, tailWord_4750934, baseEnd_4750934] using wordTrace_append hprefix tailTrace_4750934
  have hstable : (prefixWord ++ tailWord_4750934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750934).length < 2 ^ (prefixWord ++ tailWord_4750934).sum := by decide
  have hdescent : baseEnd_4750934 < baseStart_4750934 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750936 : List Nat := [2, 1, 2, 2, 1, 2, 1, 4, 4, 1, 3]
def baseStart_4750936 : Nat := 118140960795 + 4750936 * 2 ^ 59
def prefixEnd_4750936 : Nat := 4983230072969 + 3 ^ 40 * 4750936 * 2
def baseEnd_4750936 : Nat := 2439513726749129174750849

theorem tailTrace_4750936 : CollatzResearch.WordTrace tailWord_4750936 prefixEnd_4750936 2439513726749129174750849 := by
  unfold tailWord_4750936
  simp only [CollatzResearch.WordTrace]
  refine ⟨86640435758088871057716331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115520581010785161410288441 86640435758088871057716331)
  ·
    refine ⟨129960653637133306586574497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86640435758088871057716331 129960653637133306586574497)
    ·
      refine ⟨97470490227849979939930873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129960653637133306586574497 97470490227849979939930873)
      ·
        refine ⟨73102867670887484954948155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97470490227849979939930873 73102867670887484954948155)
        ·
          refine ⟨109654301506331227432422233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73102867670887484954948155 109654301506331227432422233)
          ·
            refine ⟨82240726129748420574316675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109654301506331227432422233 82240726129748420574316675)
            ·
              refine ⟨123361089194622630861475013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82240726129748420574316675 123361089194622630861475013)
              ·
                refine ⟨23130204223991743286526565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123361089194622630861475013 23130204223991743286526565)
                ·
                  refine ⟨4336913291998451866223731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23130204223991743286526565 4336913291998451866223731)
                  ·
                    refine ⟨6505369937997677799335597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4336913291998451866223731 6505369937997677799335597)
                    ·
                      refine ⟨2439513726749129174750849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6505369937997677799335597 2439513726749129174750849)
                      ·
                        rfl

theorem cell23_4750936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 4, 1, 3].length) (baseStart_4750936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750936 prefixEnd_4750936 := by exact prefixLift 4750936
  have htrace : WordTrace (prefixWord ++ tailWord_4750936) baseStart_4750936 baseEnd_4750936 := by
    simpa [prefixWord, tailWord_4750936, baseEnd_4750936] using wordTrace_append hprefix tailTrace_4750936
  have hstable : (prefixWord ++ tailWord_4750936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750936).length < 2 ^ (prefixWord ++ tailWord_4750936).sum := by decide
  have hdescent : baseEnd_4750936 < baseStart_4750936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750940 : List Nat := [2, 2, 4, 1, 2, 1, 4, 1, 1, 2, 3]
def baseStart_4750940 : Nat := 118140960795 + 4750940 * 2 ^ 59
def prefixEnd_4750940 : Nat := 4983230072969 + 3 ^ 40 * 4750940 * 2
def baseEnd_4750940 : Nat := 2439515780671747159100831

theorem tailTrace_4750940 : CollatzResearch.WordTrace tailWord_4750940 prefixEnd_4750940 2439515780671747159100831 := by
  unfold tailWord_4750940
  simp only [CollatzResearch.WordTrace]
  refine ⟨86640508704081625399289137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115520678272108833865718849 86640508704081625399289137)
  ·
    refine ⟨64980381528061219049466853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86640508704081625399289137 64980381528061219049466853)
    ·
      refine ⟨12183821536511478571775035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64980381528061219049466853 12183821536511478571775035)
      ·
        refine ⟨18275732304767217857662553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12183821536511478571775035 18275732304767217857662553)
        ·
          refine ⟨13706799228575413393246915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18275732304767217857662553 13706799228575413393246915)
          ·
            refine ⟨20560198842863120089870373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13706799228575413393246915 20560198842863120089870373)
            ·
              refine ⟨3855037283036835016850695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20560198842863120089870373 3855037283036835016850695)
              ·
                refine ⟨5782555924555252525276043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3855037283036835016850695 5782555924555252525276043)
                ·
                  refine ⟨8673833886832878787914065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5782555924555252525276043 8673833886832878787914065)
                  ·
                    refine ⟨6505375415124659090935549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8673833886832878787914065 6505375415124659090935549)
                    ·
                      refine ⟨2439515780671747159100831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6505375415124659090935549 2439515780671747159100831)
                      ·
                        rfl

theorem cell23_4750940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_4750940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750940 prefixEnd_4750940 := by exact prefixLift 4750940
  have htrace : WordTrace (prefixWord ++ tailWord_4750940) baseStart_4750940 baseEnd_4750940 := by
    simpa [prefixWord, tailWord_4750940, baseEnd_4750940] using wordTrace_append hprefix tailTrace_4750940
  have hstable : (prefixWord ++ tailWord_4750940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750940).length < 2 ^ (prefixWord ++ tailWord_4750940).sum := by decide
  have hdescent : baseEnd_4750940 < baseStart_4750940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750953 : List Nat := [1, 2, 1, 1, 1, 4, 5, 2, 2, 1, 3]
def baseStart_4750953 : Nat := 118140960795 + 4750953 * 2 ^ 59
def prefixEnd_4750953 : Nat := 4983230072969 + 3 ^ 40 * 4750953 * 2
def baseEnd_4750953 : Nat := 2439522455920255608238271

theorem tailTrace_4750953 : CollatzResearch.WordTrace tailWord_4750953 prefixEnd_4750953 2439522455920255608238271 := by
  unfold tailWord_4750953
  simp only [CollatzResearch.WordTrace]
  refine ⟨173281491557116154018801513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115520994371410769345867675 173281491557116154018801513)
  ·
    refine ⟨129961118667837115514101135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173281491557116154018801513 129961118667837115514101135)
    ·
      refine ⟨194941678001755673271151703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129961118667837115514101135 194941678001755673271151703)
      ·
        refine ⟨292412517002633509906727555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194941678001755673271151703 292412517002633509906727555)
        ·
          refine ⟨438618775503950264860091333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292412517002633509906727555 438618775503950264860091333)
          ·
            refine ⟨82241020406990674661267125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 438618775503950264860091333 82241020406990674661267125)
            ·
              refine ⟨7710095663155375749493793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82241020406990674661267125 7710095663155375749493793)
              ·
                refine ⟨5782571747366531812120345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7710095663155375749493793 5782571747366531812120345)
                ·
                  refine ⟨4336928810524898859090259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5782571747366531812120345 4336928810524898859090259)
                  ·
                    refine ⟨6505393215787348288635389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4336928810524898859090259 6505393215787348288635389)
                    ·
                      refine ⟨2439522455920255608238271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6505393215787348288635389 2439522455920255608238271)
                      ·
                        rfl

theorem cell23_4750953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2, 2, 1, 3].length) (baseStart_4750953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750953 prefixEnd_4750953 := by exact prefixLift 4750953
  have htrace : WordTrace (prefixWord ++ tailWord_4750953) baseStart_4750953 baseEnd_4750953 := by
    simpa [prefixWord, tailWord_4750953, baseEnd_4750953] using wordTrace_append hprefix tailTrace_4750953
  have hstable : (prefixWord ++ tailWord_4750953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750953).length < 2 ^ (prefixWord ++ tailWord_4750953).sum := by decide
  have hdescent : baseEnd_4750953 < baseStart_4750953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750969 : List Nat := [1, 2, 1, 3, 3, 1, 1, 3, 2, 6]
def baseStart_4750969 : Nat := 118140960795 + 4750969 * 2 ^ 59
def prefixEnd_4750969 : Nat := 4983230072969 + 3 ^ 40 * 4750969 * 2
def baseEnd_4750969 : Nat := 813176890536909181879399

theorem tailTrace_4750969 : CollatzResearch.WordTrace tailWord_4750969 prefixEnd_4750969 813176890536909181879399 := by
  unfold tailWord_4750969
  simp only [CollatzResearch.WordTrace]
  refine ⟨173282075125058188751383961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115521383416705459167589307 173282075125058188751383961)
  ·
    refine ⟨129961556343793641563537971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173282075125058188751383961 129961556343793641563537971)
    ·
      refine ⟨194942334515690462345306957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129961556343793641563537971 194942334515690462345306957)
      ·
        refine ⟨73103375443383923379490109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194942334515690462345306957 73103375443383923379490109)
        ·
          refine ⟨27413765791268971267308791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73103375443383923379490109 27413765791268971267308791)
          ·
            refine ⟨41120648686903456900963187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27413765791268971267308791 41120648686903456900963187)
            ·
              refine ⟨61680973030355185351444781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41120648686903456900963187 61680973030355185351444781)
              ·
                refine ⟨23130364886383194506791793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61680973030355185351444781 23130364886383194506791793)
                ·
                  refine ⟨17347773664787395880093845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23130364886383194506791793 17347773664787395880093845)
                  ·
                    refine ⟨813176890536909181879399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17347773664787395880093845 813176890536909181879399)
                    ·
                      rfl

theorem cell23_4750969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 6].length) (baseStart_4750969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750969 prefixEnd_4750969 := by exact prefixLift 4750969
  have htrace : WordTrace (prefixWord ++ tailWord_4750969) baseStart_4750969 baseEnd_4750969 := by
    simpa [prefixWord, tailWord_4750969, baseEnd_4750969] using wordTrace_append hprefix tailTrace_4750969
  have hstable : (prefixWord ++ tailWord_4750969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750969).length < 2 ^ (prefixWord ++ tailWord_4750969).sum := by decide
  have hdescent : baseEnd_4750969 < baseStart_4750969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4750979 : List Nat := [1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 5]
def baseStart_4750979 : Nat := 118140960795 + 4750979 * 2 ^ 59
def prefixEnd_4750979 : Nat := 4983230072969 + 3 ^ 40 * 4750979 * 2
def baseEnd_4750979 : Nat := 2439535806417272506513151

theorem tailTrace_4750979 : CollatzResearch.WordTrace tailWord_4750979 prefixEnd_4750979 2439535806417272506513151 := by
  unfold tailWord_4750979
  simp only [CollatzResearch.WordTrace]
  refine ⟨173282439855021960459247991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115521626570014640306165327 173282439855021960459247991)
  ·
    refine ⟨259923659782532940688871987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173282439855021960459247991 259923659782532940688871987)
    ·
      refine ⟨389885489673799411033307981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259923659782532940688871987 389885489673799411033307981)
      ·
        refine ⟨146207058627674779137490493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 389885489673799411033307981 146207058627674779137490493)
        ·
          refine ⟨54827646985378042176558935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146207058627674779137490493 54827646985378042176558935)
          ·
            refine ⟨82241470478067063264838403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54827646985378042176558935 82241470478067063264838403)
            ·
              refine ⟨123362205717100594897257605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82241470478067063264838403 123362205717100594897257605)
              ·
                refine ⟨23130413571956361543235801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123362205717100594897257605 23130413571956361543235801)
                ·
                  refine ⟨17347810178967271157426851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23130413571956361543235801 17347810178967271157426851)
                  ·
                    refine ⟨26021715268450906736140277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17347810178967271157426851 26021715268450906736140277)
                    ·
                      refine ⟨2439535806417272506513151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26021715268450906736140277 2439535806417272506513151)
                      ·
                        rfl

theorem cell23_4750979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 5].length) (baseStart_4750979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4750979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4750979 prefixEnd_4750979 := by exact prefixLift 4750979
  have htrace : WordTrace (prefixWord ++ tailWord_4750979) baseStart_4750979 baseEnd_4750979 := by
    simpa [prefixWord, tailWord_4750979, baseEnd_4750979] using wordTrace_append hprefix tailTrace_4750979
  have hstable : (prefixWord ++ tailWord_4750979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4750979).length < 2 ^ (prefixWord ++ tailWord_4750979).sum := by decide
  have hdescent : baseEnd_4750979 < baseStart_4750979 := by decide
  rcases family_descends (prefixWord ++ tailWord_4750979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4751026 : List Nat := [3, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3]
def baseStart_4751026 : Nat := 118140960795 + 4751026 * 2 ^ 59
def prefixEnd_4751026 : Nat := 4983230072969 + 3 ^ 40 * 4751026 * 2
def baseEnd_4751026 : Nat := 2439559940008033822625435

theorem tailTrace_4751026 : CollatzResearch.WordTrace tailWord_4751026 prefixEnd_4751026 2439559940008033822625435 := by
  unfold tailWord_4751026
  simp only [CollatzResearch.WordTrace]
  refine ⟨43321038521462921871552233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115522769390567791657472621 43321038521462921871552233)
  ·
    refine ⟨32490778891097191403664175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43321038521462921871552233 32490778891097191403664175)
    ·
      refine ⟨48736168336645787105496263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32490778891097191403664175 48736168336645787105496263)
      ·
        refine ⟨73104252504968680658244395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48736168336645787105496263 73104252504968680658244395)
        ·
          refine ⟨109656378757453020987366593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73104252504968680658244395 109656378757453020987366593)
          ·
            refine ⟨82242284068089765740524945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109656378757453020987366593 82242284068089765740524945)
            ·
              refine ⟨61681713051067324305393709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82242284068089765740524945 61681713051067324305393709)
              ·
                refine ⟨23130642394150246614522641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61681713051067324305393709 23130642394150246614522641)
                ·
                  refine ⟨17347981795612684960891981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23130642394150246614522641 17347981795612684960891981)
                  ·
                    refine ⟨6505493173354756860334493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17347981795612684960891981 6505493173354756860334493)
                    ·
                      refine ⟨2439559940008033822625435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6505493173354756860334493 2439559940008033822625435)
                      ·
                        rfl

theorem cell23_4751026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3].length) (baseStart_4751026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4751026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4751026 prefixEnd_4751026 := by exact prefixLift 4751026
  have htrace : WordTrace (prefixWord ++ tailWord_4751026) baseStart_4751026 baseEnd_4751026 := by
    simpa [prefixWord, tailWord_4751026, baseEnd_4751026] using wordTrace_append hprefix tailTrace_4751026
  have hstable : (prefixWord ++ tailWord_4751026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4751026).length < 2 ^ (prefixWord ++ tailWord_4751026).sum := by decide
  have hdescent : baseEnd_4751026 < baseStart_4751026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4751026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4751039 : List Nat := [1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 7]
def baseStart_4751039 : Nat := 118140960795 + 4751039 * 2 ^ 59
def prefixEnd_4751039 : Nat := 4983230072969 + 3 ^ 40 * 4751039 * 2
def baseEnd_4751039 : Nat := 2439566615256542271762875

theorem tailTrace_4751039 : CollatzResearch.WordTrace tailWord_4751039 prefixEnd_4751039 2439566615256542271762875 := by
  unfold tailWord_4751039
  simp only [CollatzResearch.WordTrace]
  refine ⟨173284628234804590706432171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115523085489869727137621447 173284628234804590706432171)
  ·
    refine ⟨259926942352206886059648257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173284628234804590706432171 259926942352206886059648257)
    ·
      refine ⟨194945206764155164544736193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259926942352206886059648257 194945206764155164544736193)
      ·
        refine ⟨146208905073116373408552145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194945206764155164544736193 146208905073116373408552145)
        ·
          refine ⟨109656678804837280056414109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146208905073116373408552145 109656678804837280056414109)
          ·
            refine ⟨41121254551813980021155291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109656678804837280056414109 41121254551813980021155291)
            ·
              refine ⟨61681881827720970031732937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41121254551813980021155291 61681881827720970031732937)
              ·
                refine ⟨46261411370790727523799703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61681881827720970031732937 46261411370790727523799703)
                ·
                  refine ⟨69392117056186091285699555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46261411370790727523799703 69392117056186091285699555)
                  ·
                    refine ⟨104088175584279136928549333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69392117056186091285699555 104088175584279136928549333)
                    ·
                      refine ⟨2439566615256542271762875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 104088175584279136928549333 2439566615256542271762875)
                      ·
                        rfl

theorem cell23_4751039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_4751039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4751039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4751039 prefixEnd_4751039 := by exact prefixLift 4751039
  have htrace : WordTrace (prefixWord ++ tailWord_4751039) baseStart_4751039 baseEnd_4751039 := by
    simpa [prefixWord, tailWord_4751039, baseEnd_4751039] using wordTrace_append hprefix tailTrace_4751039
  have hstable : (prefixWord ++ tailWord_4751039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4751039).length < 2 ^ (prefixWord ++ tailWord_4751039).sum := by decide
  have hdescent : baseEnd_4751039 < baseStart_4751039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4751039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4751103 : List Nat := [1, 1, 2, 2, 1, 3, 5, 1, 2, 2, 3]
def baseStart_4751103 : Nat := 118140960795 + 4751103 * 2 ^ 59
def prefixEnd_4751103 : Nat := 4983230072969 + 3 ^ 40 * 4751103 * 2
def baseEnd_4751103 : Nat := 2439599478018430021362581

theorem tailTrace_4751103 : CollatzResearch.WordTrace tailWord_4751103 prefixEnd_4751103 2439599478018430021362581 := by
  unfold tailWord_4751103
  simp only [CollatzResearch.WordTrace]
  refine ⟨173286962506572729636761963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115524641671048486424507975 173286962506572729636761963)
  ·
    refine ⟨259930443759859094455142945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173286962506572729636761963 259930443759859094455142945)
    ·
      refine ⟨194947832819894320841357209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259930443759859094455142945 194947832819894320841357209)
      ·
        refine ⟨146210874614920740631017907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194947832819894320841357209 146210874614920740631017907)
        ·
          refine ⟨219316311922381110946526861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146210874614920740631017907 219316311922381110946526861)
          ·
            refine ⟨82243616970892916604947573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 219316311922381110946526861 82243616970892916604947573)
            ·
              refine ⟨7710339091021210931713835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82243616970892916604947573 7710339091021210931713835)
              ·
                refine ⟨11565508636531816397570753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7710339091021210931713835 11565508636531816397570753)
                ·
                  refine ⟨8674131477398862298178065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11565508636531816397570753 8674131477398862298178065)
                  ·
                    refine ⟨6505598608049146723633549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8674131477398862298178065 6505598608049146723633549)
                    ·
                      refine ⟨2439599478018430021362581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6505598608049146723633549 2439599478018430021362581)
                      ·
                        rfl

theorem cell23_4751103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 2, 2, 3].length) (baseStart_4751103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4751103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4751103 prefixEnd_4751103 := by exact prefixLift 4751103
  have htrace : WordTrace (prefixWord ++ tailWord_4751103) baseStart_4751103 baseEnd_4751103 := by
    simpa [prefixWord, tailWord_4751103, baseEnd_4751103] using wordTrace_append hprefix tailTrace_4751103
  have hstable : (prefixWord ++ tailWord_4751103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4751103).length < 2 ^ (prefixWord ++ tailWord_4751103).sum := by decide
  have hdescent : baseEnd_4751103 < baseStart_4751103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4751103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4751140 : List Nat := [2, 3, 1, 3, 2, 2, 3, 1, 6]
def baseStart_4751140 : Nat := 118140960795 + 4751140 * 2 ^ 59
def prefixEnd_4751140 : Nat := 4983230072969 + 3 ^ 40 * 4751140 * 2
def baseEnd_4751140 : Nat := 271068719644738486288879

theorem tailTrace_4751140 : CollatzResearch.WordTrace tailWord_4751140 prefixEnd_4751140 271068719644738486288879 := by
  unfold tailWord_4751140
  simp only [CollatzResearch.WordTrace]
  refine ⟨86644156003719342477929437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115525541338292456637239249 86644156003719342477929437)
  ·
    refine ⟨32491558501394753429223539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86644156003719342477929437 32491558501394753429223539)
    ·
      refine ⟨48737337752092130143835309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32491558501394753429223539 48737337752092130143835309)
      ·
        refine ⟨18276501657034548803938241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48737337752092130143835309 18276501657034548803938241)
        ·
          refine ⟨13707376242775911602953681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18276501657034548803938241 13707376242775911602953681)
          ·
            refine ⟨10280532182081933702215261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13707376242775911602953681 10280532182081933702215261)
            ·
              refine ⟨3855199568280725138330723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10280532182081933702215261 3855199568280725138330723)
              ·
                refine ⟨5782799352421087707496085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3855199568280725138330723 5782799352421087707496085)
                ·
                  refine ⟨271068719644738486288879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5782799352421087707496085 271068719644738486288879)
                  ·
                    rfl

theorem cell23_4751140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 1, 6].length) (baseStart_4751140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4751140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4751140 prefixEnd_4751140 := by exact prefixLift 4751140
  have htrace : WordTrace (prefixWord ++ tailWord_4751140) baseStart_4751140 baseEnd_4751140 := by
    simpa [prefixWord, tailWord_4751140, baseEnd_4751140] using wordTrace_append hprefix tailTrace_4751140
  have hstable : (prefixWord ++ tailWord_4751140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4751140).length < 2 ^ (prefixWord ++ tailWord_4751140).sum := by decide
  have hdescent : baseEnd_4751140 < baseStart_4751140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4751140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4751153 : List Nat := [1, 2, 2, 3, 2, 2, 1, 4, 1, 5]
def baseStart_4751153 : Nat := 118140960795 + 4751153 * 2 ^ 59
def prefixEnd_4751153 : Nat := 4983230072969 + 3 ^ 40 * 4751153 * 2
def baseEnd_4751153 : Nat := 813208384017051608579117

theorem tailTrace_4751153 : CollatzResearch.WordTrace tailWord_4751153 prefixEnd_4751153 813208384017051608579117 := by
  unfold tailWord_4751153
  simp only [CollatzResearch.WordTrace]
  refine ⟨173288786156391588176082113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115525857437594392117388075 173288786156391588176082113)
  ·
    refine ⟨129966589617293691132061585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173288786156391588176082113 129966589617293691132061585)
    ·
      refine ⟨97474942212970268349046189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129966589617293691132061585 97474942212970268349046189)
      ·
        refine ⟨36553103329863850630892321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97474942212970268349046189 36553103329863850630892321)
        ·
          refine ⟨27414827497397887973169241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36553103329863850630892321 27414827497397887973169241)
          ·
            refine ⟨20561120623048415979876931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27414827497397887973169241 20561120623048415979876931)
            ·
              refine ⟨30841680934572623969815397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20561120623048415979876931 30841680934572623969815397)
              ·
                refine ⟨5782815175232366994340387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30841680934572623969815397 5782815175232366994340387)
                ·
                  refine ⟨8674222762848550491510581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5782815175232366994340387 8674222762848550491510581)
                  ·
                    refine ⟨813208384017051608579117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8674222762848550491510581 813208384017051608579117)
                    ·
                      rfl

theorem cell23_4751153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4, 1, 5].length) (baseStart_4751153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4751153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4751153 prefixEnd_4751153 := by exact prefixLift 4751153
  have htrace : WordTrace (prefixWord ++ tailWord_4751153) baseStart_4751153 baseEnd_4751153 := by
    simpa [prefixWord, tailWord_4751153, baseEnd_4751153] using wordTrace_append hprefix tailTrace_4751153
  have hstable : (prefixWord ++ tailWord_4751153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4751153).length < 2 ^ (prefixWord ++ tailWord_4751153).sum := by decide
  have hdescent : baseEnd_4751153 < baseStart_4751153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4751153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4751161 : List Nat := [1, 2, 1, 7, 2, 1, 1, 3, 1, 4]
def baseStart_4751161 : Nat := 118140960795 + 4751161 * 2 ^ 59
def prefixEnd_4751161 : Nat := 4983230072969 + 3 ^ 40 * 4751161 * 2
def baseEnd_4751161 : Nat := 813209753298796931479105

theorem tailTrace_4751161 : CollatzResearch.WordTrace tailWord_4751161 prefixEnd_4751161 813209753298796931479105 := by
  unfold tailWord_4751161
  simp only [CollatzResearch.WordTrace]
  refine ⟨173289077940362605542373337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115526051960241737028248891 173289077940362605542373337)
  ·
    refine ⟨129966808455271954156780003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173289077940362605542373337 129966808455271954156780003)
    ·
      refine ⟨194950212682907931235170005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129966808455271954156780003 194950212682907931235170005)
      ·
        refine ⟨4569145609755654638324297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 194950212682907931235170005 4569145609755654638324297)
        ·
          refine ⟨3426859207316740978743223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4569145609755654638324297 3426859207316740978743223)
          ·
            refine ⟨5140288810975111468114835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3426859207316740978743223 5140288810975111468114835)
            ·
              refine ⟨7710433216462667202172253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5140288810975111468114835 7710433216462667202172253)
              ·
                refine ⟨2891412456173500200814595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7710433216462667202172253 2891412456173500200814595)
                ·
                  refine ⟨4337118684260250301221893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2891412456173500200814595 4337118684260250301221893)
                  ·
                    refine ⟨813209753298796931479105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4337118684260250301221893 813209753298796931479105)
                    ·
                      rfl

theorem cell23_4751161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 3, 1, 4].length) (baseStart_4751161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4751161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4751161 prefixEnd_4751161 := by exact prefixLift 4751161
  have htrace : WordTrace (prefixWord ++ tailWord_4751161) baseStart_4751161 baseEnd_4751161 := by
    simpa [prefixWord, tailWord_4751161, baseEnd_4751161] using wordTrace_append hprefix tailTrace_4751161
  have hstable : (prefixWord ++ tailWord_4751161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4751161).length < 2 ^ (prefixWord ++ tailWord_4751161).sum := by decide
  have hdescent : baseEnd_4751161 < baseStart_4751161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4751161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4751173 : List Nat := [1, 3, 1, 1, 1, 2, 3, 5, 1, 1, 4]
def baseStart_4751173 : Nat := 118140960795 + 4751173 * 2 ^ 59
def prefixEnd_4751173 : Nat := 4983230072969 + 3 ^ 40 * 4751173 * 2
def baseEnd_4751173 : Nat := 2439635421664244747487259

theorem tailTrace_4751173 : CollatzResearch.WordTrace tailWord_4751173 prefixEnd_4751173 2439635421664244747487259 := by
  unfold tailWord_4751173
  simp only [CollatzResearch.WordTrace]
  refine ⟨173289515616319131591810173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115526343744212754394540115 173289515616319131591810173)
  ·
    refine ⟨64983568356119674346928815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173289515616319131591810173 64983568356119674346928815)
    ·
      refine ⟨97475352534179511520393223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64983568356119674346928815 97475352534179511520393223)
      ·
        refine ⟨146213028801269267280589835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97475352534179511520393223 146213028801269267280589835)
        ·
          refine ⟨219319543201903900920884753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146213028801269267280589835 219319543201903900920884753)
          ·
            refine ⟨164489657401427925690663565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219319543201903900920884753 164489657401427925690663565)
            ·
              refine ⟨61683621525535472133998837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 164489657401427925690663565 61683621525535472133998837)
              ·
                refine ⟨5782839518018950512562391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61683621525535472133998837 5782839518018950512562391)
                ·
                  refine ⟨8674259277028425768843587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5782839518018950512562391 8674259277028425768843587)
                  ·
                    refine ⟨13011388915542638653265381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8674259277028425768843587 13011388915542638653265381)
                    ·
                      refine ⟨2439635421664244747487259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13011388915542638653265381 2439635421664244747487259)
                      ·
                        rfl

theorem cell23_4751173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5, 1, 1, 4].length) (baseStart_4751173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4751173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4751173 prefixEnd_4751173 := by exact prefixLift 4751173
  have htrace : WordTrace (prefixWord ++ tailWord_4751173) baseStart_4751173 baseEnd_4751173 := by
    simpa [prefixWord, tailWord_4751173, baseEnd_4751173] using wordTrace_append hprefix tailTrace_4751173
  have hstable : (prefixWord ++ tailWord_4751173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4751173).length < 2 ^ (prefixWord ++ tailWord_4751173).sum := by decide
  have hdescent : baseEnd_4751173 < baseStart_4751173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4751173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4751193 : List Nat := [1, 2, 1, 2, 2, 3, 2, 2, 3, 2, 3]
def baseStart_4751193 : Nat := 118140960795 + 4751193 * 2 ^ 59
def prefixEnd_4751193 : Nat := 4983230072969 + 3 ^ 40 * 4751193 * 2
def baseEnd_4751193 : Nat := 2439645691277334669237167

theorem tailTrace_4751193 : CollatzResearch.WordTrace tailWord_4751193 prefixEnd_4751193 2439645691277334669237167 := by
  unfold tailWord_4751193
  simp only [CollatzResearch.WordTrace]
  refine ⟨173290245076246675007538233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115526830050831116671692155 173290245076246675007538233)
  ·
    refine ⟨129967683807185006255653675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173290245076246675007538233 129967683807185006255653675)
    ·
      refine ⟨194951525710777509383480513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129967683807185006255653675 194951525710777509383480513)
      ·
        refine ⟨146213644283083132037610385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194951525710777509383480513 146213644283083132037610385)
        ·
          refine ⟨109660233212312349028207789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146213644283083132037610385 109660233212312349028207789)
          ·
            refine ⟨41122587454617130885577921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109660233212312349028207789 41122587454617130885577921)
            ·
              refine ⟨30841940590962848164183441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41122587454617130885577921 30841940590962848164183441)
              ·
                refine ⟨23131455443222136123137581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30841940590962848164183441 23131455443222136123137581)
                ·
                  refine ⟨8674295791208301046176593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23131455443222136123137581 8674295791208301046176593)
                  ·
                    refine ⟨6505721843406225784632445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8674295791208301046176593 6505721843406225784632445)
                    ·
                      refine ⟨2439645691277334669237167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6505721843406225784632445 2439645691277334669237167)
                      ·
                        rfl

theorem cell23_4751193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 2, 3].length) (baseStart_4751193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4751193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4751193 prefixEnd_4751193 := by exact prefixLift 4751193
  have htrace : WordTrace (prefixWord ++ tailWord_4751193) baseStart_4751193 baseEnd_4751193 := by
    simpa [prefixWord, tailWord_4751193, baseEnd_4751193] using wordTrace_append hprefix tailTrace_4751193
  have hstable : (prefixWord ++ tailWord_4751193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4751193).length < 2 ^ (prefixWord ++ tailWord_4751193).sum := by decide
  have hdescent : baseEnd_4751193 < baseStart_4751193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4751193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4751200 : List Nat := [2, 1, 1, 3, 3, 3, 1, 3, 2, 4]
def baseStart_4751200 : Nat := 118140960795 + 4751200 * 2 ^ 59
def prefixEnd_4751200 : Nat := 4983230072969 + 3 ^ 40 * 4751200 * 2
def baseEnd_4751200 : Nat := 813216428547305380616545

theorem tailTrace_4751200 : CollatzResearch.WordTrace tailWord_4751200 prefixEnd_4751200 813216428547305380616545 := by
  unfold tailWord_4751200
  simp only [CollatzResearch.WordTrace]
  refine ⟨86645250193610657601521527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115527000258147543468695369 86645250193610657601521527)
  ·
    refine ⟨129967875290415986402282291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86645250193610657601521527 129967875290415986402282291)
    ·
      refine ⟨194951812935623979603423437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129967875290415986402282291 194951812935623979603423437)
      ·
        refine ⟨73106929850858992351283789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194951812935623979603423437 73106929850858992351283789)
        ·
          refine ⟨27415098694072122131731421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73106929850858992351283789 27415098694072122131731421)
          ·
            refine ⟨10280662010277045799399283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27415098694072122131731421 10280662010277045799399283)
            ·
              refine ⟨15420993015415568699098925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10280662010277045799399283 15420993015415568699098925)
              ·
                refine ⟨5782872380780838262162097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15420993015415568699098925 5782872380780838262162097)
                ·
                  refine ⟨4337154285585628696621573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5782872380780838262162097 4337154285585628696621573)
                  ·
                    refine ⟨813216428547305380616545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4337154285585628696621573 813216428547305380616545)
                    ·
                      rfl

theorem cell23_4751200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3, 2, 4].length) (baseStart_4751200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4751200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4751200 prefixEnd_4751200 := by exact prefixLift 4751200
  have htrace : WordTrace (prefixWord ++ tailWord_4751200) baseStart_4751200 baseEnd_4751200 := by
    simpa [prefixWord, tailWord_4751200, baseEnd_4751200] using wordTrace_append hprefix tailTrace_4751200
  have hstable : (prefixWord ++ tailWord_4751200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4751200).length < 2 ^ (prefixWord ++ tailWord_4751200).sum := by decide
  have hdescent : baseEnd_4751200 < baseStart_4751200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4751200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4751313 : List Nat := [1, 2, 2, 1, 2, 1, 2, 3, 1, 5, 3]
def baseStart_4751313 : Nat := 118140960795 + 4751313 * 2 ^ 59
def prefixEnd_4751313 : Nat := 4983230072969 + 3 ^ 40 * 4751313 * 2
def baseEnd_4751313 : Nat := 2439707308955874199736615

theorem tailTrace_4751313 : CollatzResearch.WordTrace tailWord_4751313 prefixEnd_4751313 2439707308955874199736615 := by
  unfold tailWord_4751313
  simp only [CollatzResearch.WordTrace]
  refine ⟨173294621835811935501906593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115529747890541290334604395 173294621835811935501906593)
  ·
    refine ⟨129970966376858951626429945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173294621835811935501906593 129970966376858951626429945)
    ·
      refine ⟨97478224782644213719822459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129970966376858951626429945 97478224782644213719822459)
      ·
        refine ⟨146217337173966320579733689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97478224782644213719822459 146217337173966320579733689)
        ·
          refine ⟨109663002880474740434800267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146217337173966320579733689 109663002880474740434800267)
          ·
            refine ⟨164494504320712110652200401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109663002880474740434800267 164494504320712110652200401)
            ·
              refine ⟨123370878240534082989150301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164494504320712110652200401 123370878240534082989150301)
              ·
                refine ⟨46264079340200281120931363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123370878240534082989150301 46264079340200281120931363)
                ·
                  refine ⟨69396119010300421681397045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46264079340200281120931363 69396119010300421681397045)
                  ·
                    refine ⟨6505886157215664532630973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 69396119010300421681397045 6505886157215664532630973)
                    ·
                      refine ⟨2439707308955874199736615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6505886157215664532630973 2439707308955874199736615)
                      ·
                        rfl

theorem cell23_4751313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 5, 3].length) (baseStart_4751313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4751313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4751313 prefixEnd_4751313 := by exact prefixLift 4751313
  have htrace : WordTrace (prefixWord ++ tailWord_4751313) baseStart_4751313 baseEnd_4751313 := by
    simpa [prefixWord, tailWord_4751313, baseEnd_4751313] using wordTrace_append hprefix tailTrace_4751313
  have hstable : (prefixWord ++ tailWord_4751313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4751313).length < 2 ^ (prefixWord ++ tailWord_4751313).sum := by decide
  have hdescent : baseEnd_4751313 < baseStart_4751313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4751313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4751343 : List Nat := [1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 5]
def baseStart_4751343 : Nat := 118140960795 + 4751343 * 2 ^ 59
def prefixEnd_4751343 : Nat := 4983230072969 + 3 ^ 40 * 4751343 * 2
def baseEnd_4751343 : Nat := 2439722713375509082361477

theorem tailTrace_4751343 : CollatzResearch.WordTrace tailWord_4751343 prefixEnd_4751343 2439722713375509082361477 := by
  unfold tailWord_4751343
  simp only [CollatzResearch.WordTrace]
  refine ⟨173295716025703250625498683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115530477350468833750332455 173295716025703250625498683)
  ·
    refine ⟨259943574038554875938248025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173295716025703250625498683 259943574038554875938248025)
    ·
      refine ⟨194957680528916156953686019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259943574038554875938248025 194957680528916156953686019)
      ·
        refine ⟨292436520793374235430529029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194957680528916156953686019 292436520793374235430529029)
        ·
          refine ⟨54831847648757669143224193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 292436520793374235430529029 54831847648757669143224193)
          ·
            refine ⟨41123885736568251857418145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54831847648757669143224193 41123885736568251857418145)
            ·
              refine ⟨30842914302426188893063609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41123885736568251857418145 30842914302426188893063609)
              ·
                refine ⟨23132185726819641669797707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30842914302426188893063609 23132185726819641669797707)
                ·
                  refine ⟨34698278590229462504696561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23132185726819641669797707 34698278590229462504696561)
                  ·
                    refine ⟨26023708942672096878522421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34698278590229462504696561 26023708942672096878522421)
                    ·
                      refine ⟨2439722713375509082361477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26023708942672096878522421 2439722713375509082361477)
                      ·
                        rfl

theorem cell23_4751343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 5].length) (baseStart_4751343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4751343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4751343 prefixEnd_4751343 := by exact prefixLift 4751343
  have htrace : WordTrace (prefixWord ++ tailWord_4751343) baseStart_4751343 baseEnd_4751343 := by
    simpa [prefixWord, tailWord_4751343, baseEnd_4751343] using wordTrace_append hprefix tailTrace_4751343
  have hstable : (prefixWord ++ tailWord_4751343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4751343).length < 2 ^ (prefixWord ++ tailWord_4751343).sum := by decide
  have hdescent : baseEnd_4751343 < baseStart_4751343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4751343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4751410 : List Nat := [3, 2, 1, 1, 2, 3, 1, 4, 6]
def baseStart_4751410 : Nat := 118140960795 + 4751410 * 2 ^ 59
def prefixEnd_4751410 : Nat := 4983230072969 + 3 ^ 40 * 4751410 * 2
def baseEnd_4751410 : Nat := 271084124064373368913741

theorem tailTrace_4751410 : CollatzResearch.WordTrace tailWord_4751410 prefixEnd_4751410 271084124064373368913741 := by
  unfold tailWord_4751410
  simp only [CollatzResearch.WordTrace]
  refine ⟨43324539929115130267046921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115532106477640347378791789 43324539929115130267046921)
  ·
    refine ⟨32493404946836347700285191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43324539929115130267046921 32493404946836347700285191)
    ·
      refine ⟨48740107420254521550427787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32493404946836347700285191 48740107420254521550427787)
      ·
        refine ⟨73110161130381782325641681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48740107420254521550427787 73110161130381782325641681)
        ·
          refine ⟨54832620847786336744231261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73110161130381782325641681 54832620847786336744231261)
          ·
            refine ⟨20562232817919876279086723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54832620847786336744231261 20562232817919876279086723)
            ·
              refine ⟨30843349226879814418630085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20562232817919876279086723 30843349226879814418630085)
              ·
                refine ⟨5783127980039965203493141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30843349226879814418630085 5783127980039965203493141)
                ·
                  refine ⟨271084124064373368913741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5783127980039965203493141 271084124064373368913741)
                  ·
                    rfl

theorem cell23_4751410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4, 6].length) (baseStart_4751410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4751410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4751410 prefixEnd_4751410 := by exact prefixLift 4751410
  have htrace : WordTrace (prefixWord ++ tailWord_4751410) baseStart_4751410 baseEnd_4751410 := by
    simpa [prefixWord, tailWord_4751410, baseEnd_4751410] using wordTrace_append hprefix tailTrace_4751410
  have hstable : (prefixWord ++ tailWord_4751410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4751410).length < 2 ^ (prefixWord ++ tailWord_4751410).sum := by decide
  have hdescent : baseEnd_4751410 < baseStart_4751410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4751410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4751433 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 2, 1, 7]
def baseStart_4751433 : Nat := 118140960795 + 4751433 * 2 ^ 59
def prefixEnd_4751433 : Nat := 4983230072969 + 3 ^ 40 * 4751433 * 2
def baseEnd_4751433 : Nat := 2439768926634413730236063

theorem tailTrace_4751433 : CollatzResearch.WordTrace tailWord_4751433 prefixEnd_4751433 2439768926634413730236063 := by
  unfold tailWord_4751433
  simp only [CollatzResearch.WordTrace]
  refine ⟨173298998595377195996274953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115532665730251463997516635 173298998595377195996274953)
  ·
    refine ⟨129974248946532896997206215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173298998595377195996274953 129974248946532896997206215)
    ·
      refine ⟨194961373419799345495809323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129974248946532896997206215 194961373419799345495809323)
      ·
        refine ⟨292442060129699018243713985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194961373419799345495809323 292442060129699018243713985)
        ·
          refine ⟨219331545097274263682785489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292442060129699018243713985 219331545097274263682785489)
          ·
            refine ⟨164498658822955697762089117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219331545097274263682785489 164498658822955697762089117)
            ·
              refine ⟨61686997058608386660783419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 164498658822955697762089117 61686997058608386660783419)
              ·
                refine ⟨92530495587912579991175129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61686997058608386660783419 92530495587912579991175129)
                ·
                  refine ⟨69397871690934434993381347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92530495587912579991175129 69397871690934434993381347)
                  ·
                    refine ⟨104096807536401652490072021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69397871690934434993381347 104096807536401652490072021)
                    ·
                      refine ⟨2439768926634413730236063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 104096807536401652490072021 2439768926634413730236063)
                      ·
                        rfl

theorem cell23_4751433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 1, 7].length) (baseStart_4751433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4751433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4751433 prefixEnd_4751433 := by exact prefixLift 4751433
  have htrace : WordTrace (prefixWord ++ tailWord_4751433) baseStart_4751433 baseEnd_4751433 := by
    simpa [prefixWord, tailWord_4751433, baseEnd_4751433] using wordTrace_append hprefix tailTrace_4751433
  have hstable : (prefixWord ++ tailWord_4751433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4751433).length < 2 ^ (prefixWord ++ tailWord_4751433).sum := by decide
  have hdescent : baseEnd_4751433 < baseStart_4751433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4751433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4751514 : List Nat := [3, 1, 1, 5, 2, 1, 2, 1, 1, 1, 5]
def baseStart_4751514 : Nat := 118140960795 + 4751514 * 2 ^ 59
def prefixEnd_4751514 : Nat := 4983230072969 + 3 ^ 40 * 4751514 * 2
def baseEnd_4751514 : Nat := 2439810518567427913323191

theorem tailTrace_4751514 : CollatzResearch.WordTrace tailWord_4751514 prefixEnd_4751514 2439810518567427913323191 := by
  unfold tailWord_4751514
  simp only [CollatzResearch.WordTrace]
  refine ⟨43325488227020936707493399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115534635272055831219982397 43325488227020936707493399)
  ·
    refine ⟨64988232340531405061240099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43325488227020936707493399 64988232340531405061240099)
    ·
      refine ⟨97482348510797107591860149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64988232340531405061240099 97482348510797107591860149)
      ·
        refine ⟨9138970172887228836736889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97482348510797107591860149 9138970172887228836736889)
        ·
          refine ⟨6854227629665421627552667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9138970172887228836736889 6854227629665421627552667)
          ·
            refine ⟨10281341444498132441329001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6854227629665421627552667 10281341444498132441329001)
            ·
              refine ⟨7711006083373599330996751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10281341444498132441329001 7711006083373599330996751)
              ·
                refine ⟨11566509125060398996495127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7711006083373599330996751 11566509125060398996495127)
                ·
                  refine ⟨17349763687590598494742691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11566509125060398996495127 17349763687590598494742691)
                  ·
                    refine ⟨26024645531385897742114037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17349763687590598494742691 26024645531385897742114037)
                    ·
                      refine ⟨2439810518567427913323191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26024645531385897742114037 2439810518567427913323191)
                      ·
                        rfl

theorem cell23_4751514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_4751514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4751514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4751514 prefixEnd_4751514 := by exact prefixLift 4751514
  have htrace : WordTrace (prefixWord ++ tailWord_4751514) baseStart_4751514 baseEnd_4751514 := by
    simpa [prefixWord, tailWord_4751514, baseEnd_4751514] using wordTrace_append hprefix tailTrace_4751514
  have hstable : (prefixWord ++ tailWord_4751514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4751514).length < 2 ^ (prefixWord ++ tailWord_4751514).sum := by decide
  have hdescent : baseEnd_4751514 < baseStart_4751514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4751514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4751544 : List Nat := [2, 1, 2, 1, 2, 1, 5, 3, 2, 1, 3]
def baseStart_4751544 : Nat := 118140960795 + 4751544 * 2 ^ 59
def prefixEnd_4751544 : Nat := 4983230072969 + 3 ^ 40 * 4751544 * 2
def baseEnd_4751544 : Nat := 2439825922987062795948053

theorem tailTrace_4751544 : CollatzResearch.WordTrace tailWord_4751544 prefixEnd_4751544 2439825922987062795948053 := by
  unfold tailWord_4751544
  simp only [CollatzResearch.WordTrace]
  refine ⟨86651523548987530976782843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115535364731983374635710457 86651523548987530976782843)
  ·
    refine ⟨129977285323481296465174265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86651523548987530976782843 129977285323481296465174265)
    ·
      refine ⟨97482963992610972348880699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129977285323481296465174265 97482963992610972348880699)
      ·
        refine ⟨146224445988916458523321049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97482963992610972348880699 146224445988916458523321049)
        ·
          refine ⟨109668334491687343892490787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146224445988916458523321049 109668334491687343892490787)
          ·
            refine ⟨164502501737531015838736181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109668334491687343892490787 164502501737531015838736181)
            ·
              refine ⟨15422109537893532734881517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 164502501737531015838736181 15422109537893532734881517)
              ·
                refine ⟨5783291076710074775580569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15422109537893532734881517 5783291076710074775580569)
                ·
                  refine ⟨4337468307532556081685427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5783291076710074775580569 4337468307532556081685427)
                  ·
                    refine ⟨6506202461298834122528141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4337468307532556081685427 6506202461298834122528141)
                    ·
                      refine ⟨2439825922987062795948053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6506202461298834122528141 2439825922987062795948053)
                      ·
                        rfl

theorem cell23_4751544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3, 2, 1, 3].length) (baseStart_4751544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4751544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4751544 prefixEnd_4751544 := by exact prefixLift 4751544
  have htrace : WordTrace (prefixWord ++ tailWord_4751544) baseStart_4751544 baseEnd_4751544 := by
    simpa [prefixWord, tailWord_4751544, baseEnd_4751544] using wordTrace_append hprefix tailTrace_4751544
  have hstable : (prefixWord ++ tailWord_4751544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4751544).length < 2 ^ (prefixWord ++ tailWord_4751544).sum := by decide
  have hdescent : baseEnd_4751544 < baseStart_4751544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4751544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4751548 : List Nat := [2, 2, 2, 3, 4, 1, 1, 2, 1, 2, 3]
def baseStart_4751548 : Nat := 118140960795 + 4751548 * 2 ^ 59
def prefixEnd_4751548 : Nat := 4983230072969 + 3 ^ 40 * 4751548 * 2
def baseEnd_4751548 : Nat := 2439827976909680780298035

theorem tailTrace_4751548 : CollatzResearch.WordTrace tailWord_4751548 prefixEnd_4751548 2439827976909680780298035 := by
  unfold tailWord_4751548
  simp only [CollatzResearch.WordTrace]
  refine ⟨86651596494980285318355649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115535461993307047091140865 86651596494980285318355649)
  ·
    refine ⟨64988697371235213988766737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86651596494980285318355649 64988697371235213988766737)
    ·
      refine ⟨48741523028426410491575053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64988697371235213988766737 48741523028426410491575053)
      ·
        refine ⟨18278071135659903934340645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48741523028426410491575053 18278071135659903934340645)
        ·
          refine ⟨3427138337936231987688871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18278071135659903934340645 3427138337936231987688871)
          ·
            refine ⟨5140707506904347981533307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3427138337936231987688871 5140707506904347981533307)
            ·
              refine ⟨7711061260356521972299961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5140707506904347981533307 7711061260356521972299961)
              ·
                refine ⟨5783295945267391479224971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7711061260356521972299961 5783295945267391479224971)
                ·
                  refine ⟨8674943917901087218837457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5783295945267391479224971 8674943917901087218837457)
                  ·
                    refine ⟨6506207938425815414128093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8674943917901087218837457 6506207938425815414128093)
                    ·
                      refine ⟨2439827976909680780298035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6506207938425815414128093 2439827976909680780298035)
                      ·
                        rfl

theorem cell23_4751548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_4751548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4751548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4751548 prefixEnd_4751548 := by exact prefixLift 4751548
  have htrace : WordTrace (prefixWord ++ tailWord_4751548) baseStart_4751548 baseEnd_4751548 := by
    simpa [prefixWord, tailWord_4751548, baseEnd_4751548] using wordTrace_append hprefix tailTrace_4751548
  have hstable : (prefixWord ++ tailWord_4751548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4751548).length < 2 ^ (prefixWord ++ tailWord_4751548).sum := by decide
  have hdescent : baseEnd_4751548 < baseStart_4751548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4751548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4751560 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 4, 6]
def baseStart_4751560 : Nat := 118140960795 + 4751560 * 2 ^ 59
def prefixEnd_4751560 : Nat := 4983230072969 + 3 ^ 40 * 4751560 * 2
def baseEnd_4751560 : Nat := 813278046225844911115993

theorem tailTrace_4751560 : CollatzResearch.WordTrace tailWord_4751560 prefixEnd_4751560 813278046225844911115993 := by
  unfold tailWord_4751560
  simp only [CollatzResearch.WordTrace]
  refine ⟨86651815332958548343074067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115535753777278064457432089 86651815332958548343074067)
  ·
    refine ⟨129977722999437822514611101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86651815332958548343074067 129977722999437822514611101)
    ·
      refine ⟨48741646124789183442979163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129977722999437822514611101 48741646124789183442979163)
      ·
        refine ⟨73112469187183775164468745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48741646124789183442979163 73112469187183775164468745)
        ·
          refine ⟨54834351890387831373351559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73112469187183775164468745 54834351890387831373351559)
          ·
            refine ⟨82251527835581747060027339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54834351890387831373351559 82251527835581747060027339)
            ·
              refine ⟨123377291753372620590041009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82251527835581747060027339 123377291753372620590041009)
              ·
                refine ⟨92532968815029465442530757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123377291753372620590041009 92532968815029465442530757)
                ·
                  refine ⟨17349931652818024770474517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92532968815029465442530757 17349931652818024770474517)
                  ·
                    refine ⟨813278046225844911115993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17349931652818024770474517 813278046225844911115993)
                    ·
                      rfl

theorem cell23_4751560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_4751560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4751560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4751560 prefixEnd_4751560 := by exact prefixLift 4751560
  have htrace : WordTrace (prefixWord ++ tailWord_4751560) baseStart_4751560 baseEnd_4751560 := by
    simpa [prefixWord, tailWord_4751560, baseEnd_4751560] using wordTrace_append hprefix tailTrace_4751560
  have hstable : (prefixWord ++ tailWord_4751560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4751560).length < 2 ^ (prefixWord ++ tailWord_4751560).sum := by decide
  have hdescent : baseEnd_4751560 < baseStart_4751560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4751560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4751601 : List Nat := [1, 2, 2, 2, 2, 1, 4, 3, 2, 2, 2]
def baseStart_4751601 : Nat := 118140960795 + 4751601 * 2 ^ 59
def prefixEnd_4751601 : Nat := 4983230072969 + 3 ^ 40 * 4751601 * 2
def baseEnd_4751601 : Nat := 2439855191384369072935291

theorem tailTrace_4751601 : CollatzResearch.WordTrace tailWord_4751601 prefixEnd_4751601 2439855191384369072935291 := by
  unfold tailWord_4751601
  simp only [CollatzResearch.WordTrace]
  refine ⟨173305126058768560688390657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115536750705845707125593771 173305126058768560688390657)
  ·
    refine ⟨129978844544076420516292993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173305126058768560688390657 129978844544076420516292993)
    ·
      refine ⟨97484133408057315387219745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129978844544076420516292993 97484133408057315387219745)
      ·
        refine ⟨73113100056042986540414809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97484133408057315387219745 73113100056042986540414809)
        ·
          refine ⟨54834825042032239905311107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73113100056042986540414809 54834825042032239905311107)
          ·
            refine ⟨82252237563048359857966661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54834825042032239905311107 82252237563048359857966661)
            ·
              refine ⟨15422294543071567473368749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82252237563048359857966661 15422294543071567473368749)
              ·
                refine ⟨5783360453651837802513281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15422294543071567473368749 5783360453651837802513281)
                ·
                  refine ⟨4337520340238878351884961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5783360453651837802513281 4337520340238878351884961)
                  ·
                    refine ⟨3253140255179158763913721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4337520340238878351884961 3253140255179158763913721)
                    ·
                      refine ⟨2439855191384369072935291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3253140255179158763913721 2439855191384369072935291)
                      ·
                        rfl

theorem cell23_4751601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3, 2, 2, 2].length) (baseStart_4751601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4751601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4751601 prefixEnd_4751601 := by exact prefixLift 4751601
  have htrace : WordTrace (prefixWord ++ tailWord_4751601) baseStart_4751601 baseEnd_4751601 := by
    simpa [prefixWord, tailWord_4751601, baseEnd_4751601] using wordTrace_append hprefix tailTrace_4751601
  have hstable : (prefixWord ++ tailWord_4751601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4751601).length < 2 ^ (prefixWord ++ tailWord_4751601).sum := by decide
  have hdescent : baseEnd_4751601 < baseStart_4751601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4751601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4751617 : List Nat := [1, 2, 4, 1, 1, 2, 1, 2, 1, 5, 3]
def baseStart_4751617 : Nat := 118140960795 + 4751617 * 2 ^ 59
def prefixEnd_4751617 : Nat := 4983230072969 + 3 ^ 40 * 4751617 * 2
def baseEnd_4751617 : Nat := 2439863407074841010335217

theorem tailTrace_4751617 : CollatzResearch.WordTrace tailWord_4751617 prefixEnd_4751617 2439863407074841010335217 := by
  unfold tailWord_4751617
  simp only [CollatzResearch.WordTrace]
  refine ⟨173305709626710595420973105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115537139751140396947315403 173305709626710595420973105)
  ·
    refine ⟨129979282220032946565729829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173305709626710595420973105 129979282220032946565729829)
    ·
      refine ⟨24371115416256177481074343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129979282220032946565729829 24371115416256177481074343)
      ·
        refine ⟨36556673124384266221611515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24371115416256177481074343 36556673124384266221611515)
        ·
          refine ⟨54835009686576399332417273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36556673124384266221611515 54835009686576399332417273)
          ·
            refine ⟨41126257264932299499312955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54835009686576399332417273 41126257264932299499312955)
            ·
              refine ⟨61689385897398449248969433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41126257264932299499312955 61689385897398449248969433)
              ·
                refine ⟨46267039423048836936727075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61689385897398449248969433 46267039423048836936727075)
                ·
                  refine ⟨69400559134573255405090613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46267039423048836936727075 69400559134573255405090613)
                  ·
                    refine ⟨6506302418866242694227245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 69400559134573255405090613 6506302418866242694227245)
                    ·
                      refine ⟨2439863407074841010335217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6506302418866242694227245 2439863407074841010335217)
                      ·
                        rfl

theorem cell23_4751617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_4751617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4751617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4751617 prefixEnd_4751617 := by exact prefixLift 4751617
  have htrace : WordTrace (prefixWord ++ tailWord_4751617) baseStart_4751617 baseEnd_4751617 := by
    simpa [prefixWord, tailWord_4751617, baseEnd_4751617] using wordTrace_append hprefix tailTrace_4751617
  have hstable : (prefixWord ++ tailWord_4751617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4751617).length < 2 ^ (prefixWord ++ tailWord_4751617).sum := by decide
  have hdescent : baseEnd_4751617 < baseStart_4751617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4751617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4751624 : List Nat := [2, 1, 3, 2, 3, 1, 1, 5, 5]
def baseStart_4751624 : Nat := 118140960795 + 4751624 * 2 ^ 59
def prefixEnd_4751624 : Nat := 4983230072969 + 3 ^ 40 * 4751624 * 2
def baseEnd_4751624 : Nat := 271096333493269164771965

theorem tailTrace_4751624 : CollatzResearch.WordTrace tailWord_4751624 prefixEnd_4751624 271096333493269164771965 := by
  unfold tailWord_4751624
  simp only [CollatzResearch.WordTrace]
  refine ⟨86652982468842617808238963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115537309958456823744318617 86652982468842617808238963)
  ·
    refine ⟨129979473703263926712358445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86652982468842617808238963 129979473703263926712358445)
    ·
      refine ⟨48742302638723972517134417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129979473703263926712358445 48742302638723972517134417)
      ·
        refine ⟨36556726979042979387850813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48742302638723972517134417 36556726979042979387850813)
        ·
          refine ⟨13708772617141117270444055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36556726979042979387850813 13708772617141117270444055)
          ·
            refine ⟨20563158925711675905666083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13708772617141117270444055 20563158925711675905666083)
            ·
              refine ⟨30844738388567513858499125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20563158925711675905666083 30844738388567513858499125)
              ·
                refine ⟨2891694223928204424234293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30844738388567513858499125 2891694223928204424234293)
                ·
                  refine ⟨271096333493269164771965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2891694223928204424234293 271096333493269164771965)
                  ·
                    rfl

theorem cell23_4751624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 5, 5].length) (baseStart_4751624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4751624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4751624 prefixEnd_4751624 := by exact prefixLift 4751624
  have htrace : WordTrace (prefixWord ++ tailWord_4751624) baseStart_4751624 baseEnd_4751624 := by
    simpa [prefixWord, tailWord_4751624, baseEnd_4751624] using wordTrace_append hprefix tailTrace_4751624
  have hstable : (prefixWord ++ tailWord_4751624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4751624).length < 2 ^ (prefixWord ++ tailWord_4751624).sum := by decide
  have hdescent : baseEnd_4751624 < baseStart_4751624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4751624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4751637 : List Nat := [1, 3, 2, 1, 2, 1, 2, 4, 2, 5]
def baseStart_4751637 : Nat := 118140960795 + 4751637 * 2 ^ 59
def prefixEnd_4751637 : Nat := 4983230072969 + 3 ^ 40 * 4751637 * 2
def baseEnd_4751637 : Nat := 813291225562643644028375

theorem tailTrace_4751637 : CollatzResearch.WordTrace tailWord_4751637 prefixEnd_4751637 813291225562643644028375 := by
  unfold tailWord_4751637
  simp only [CollatzResearch.WordTrace]
  refine ⟨173306439086638138836701165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115537626057758759224467443 173306439086638138836701165)
  ·
    refine ⟨64989914657489302063762937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173306439086638138836701165 64989914657489302063762937)
    ·
      refine ⟨48742435993116976547822203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64989914657489302063762937 48742435993116976547822203)
      ·
        refine ⟨73113653989675464821733305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48742435993116976547822203 73113653989675464821733305)
        ·
          refine ⟨54835240492256598616299979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73113653989675464821733305 54835240492256598616299979)
          ·
            refine ⟨82252860738384897924449969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54835240492256598616299979 82252860738384897924449969)
            ·
              refine ⟨61689645553788673443337477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82252860738384897924449969 61689645553788673443337477)
              ·
                refine ⟨11566808541335376270625777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61689645553788673443337477 11566808541335376270625777)
                ·
                  refine ⟨8675106406001532202969333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11566808541335376270625777 8675106406001532202969333)
                  ·
                    refine ⟨813291225562643644028375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8675106406001532202969333 813291225562643644028375)
                    ·
                      rfl

theorem cell23_4751637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_4751637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4751637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4751637 prefixEnd_4751637 := by exact prefixLift 4751637
  have htrace : WordTrace (prefixWord ++ tailWord_4751637) baseStart_4751637 baseEnd_4751637 := by
    simpa [prefixWord, tailWord_4751637, baseEnd_4751637] using wordTrace_append hprefix tailTrace_4751637
  have hstable : (prefixWord ++ tailWord_4751637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4751637).length < 2 ^ (prefixWord ++ tailWord_4751637).sum := by decide
  have hdescent : baseEnd_4751637 < baseStart_4751637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4751637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4751697 : List Nat := [1, 2, 2, 1, 4, 2, 2, 1, 8]
def baseStart_4751697 : Nat := 118140960795 + 4751697 * 2 ^ 59
def prefixEnd_4751697 : Nat := 4983230072969 + 3 ^ 40 * 4751697 * 2
def baseEnd_4751697 : Nat := 271100498391911188592761

theorem tailTrace_4751697 : CollatzResearch.WordTrace tailWord_4751697 prefixEnd_4751697 271100498391911188592761 := by
  unfold tailWord_4751697
  simp only [CollatzResearch.WordTrace]
  refine ⟨173308627466420769083885345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115539084977613846055923563 173308627466420769083885345)
  ·
    refine ⟨129981470599815576812914009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173308627466420769083885345 129981470599815576812914009)
    ·
      refine ⟨97486102949861682609685507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129981470599815576812914009 97486102949861682609685507)
      ·
        refine ⟨146229154424792523914528261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97486102949861682609685507 146229154424792523914528261)
        ·
          refine ⟨27417966454648598233974049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 146229154424792523914528261 27417966454648598233974049)
          ·
            refine ⟨20563474840986448675480537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27417966454648598233974049 20563474840986448675480537)
            ·
              refine ⟨15422606130739836506610403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20563474840986448675480537 15422606130739836506610403)
              ·
                refine ⟨23133909196109754759915605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15422606130739836506610403 23133909196109754759915605)
                ·
                  refine ⟨271100498391911188592761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23133909196109754759915605 271100498391911188592761)
                  ·
                    rfl

theorem cell23_4751697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 8].length) (baseStart_4751697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4751697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4751697 prefixEnd_4751697 := by exact prefixLift 4751697
  have htrace : WordTrace (prefixWord ++ tailWord_4751697) baseStart_4751697 baseEnd_4751697 := by
    simpa [prefixWord, tailWord_4751697, baseEnd_4751697] using wordTrace_append hprefix tailTrace_4751697
  have hstable : (prefixWord ++ tailWord_4751697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4751697).length < 2 ^ (prefixWord ++ tailWord_4751697).sum := by decide
  have hdescent : baseEnd_4751697 < baseStart_4751697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4751697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4751751 : List Nat := [1, 1, 4, 2, 2, 1, 1, 4, 2, 3, 2]
def baseStart_4751751 : Nat := 118140960795 + 4751751 * 2 ^ 59
def prefixEnd_4751751 : Nat := 4983230072969 + 3 ^ 40 * 4751751 * 2
def baseEnd_4751751 : Nat := 2439932213482543486059601

theorem tailTrace_4751751 : CollatzResearch.WordTrace tailWord_4751751 prefixEnd_4751751 2439932213482543486059601 := by
  unfold tailWord_4751751
  simp only [CollatzResearch.WordTrace]
  refine ⟨173310597008225136306351107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115540398005483424204234071 173310597008225136306351107)
  ·
    refine ⟨259965895512337704459526661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173310597008225136306351107 259965895512337704459526661)
    ·
      refine ⟨48743605408563319586161249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 259965895512337704459526661 48743605408563319586161249)
      ·
        refine ⟨36557704056422489689620937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48743605408563319586161249 36557704056422489689620937)
        ·
          refine ⟨27418278042316867267215703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36557704056422489689620937 27418278042316867267215703)
          ·
            refine ⟨41127417063475300900823555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27418278042316867267215703 41127417063475300900823555)
            ·
              refine ⟨61691125595212951351235333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41127417063475300900823555 61691125595212951351235333)
              ·
                refine ⟨11567086049102428378356625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61691125595212951351235333 11567086049102428378356625)
                ·
                  refine ⟨8675314536826821283767469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11567086049102428378356625 8675314536826821283767469)
                  ·
                    refine ⟨3253242951310057981412801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8675314536826821283767469 3253242951310057981412801)
                    ·
                      refine ⟨2439932213482543486059601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3253242951310057981412801 2439932213482543486059601)
                      ·
                        rfl

theorem cell23_4751751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2, 3, 2].length) (baseStart_4751751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4751751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4751751 prefixEnd_4751751 := by exact prefixLift 4751751
  have htrace : WordTrace (prefixWord ++ tailWord_4751751) baseStart_4751751 baseEnd_4751751 := by
    simpa [prefixWord, tailWord_4751751, baseEnd_4751751] using wordTrace_append hprefix tailTrace_4751751
  have hstable : (prefixWord ++ tailWord_4751751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4751751).length < 2 ^ (prefixWord ++ tailWord_4751751).sum := by decide
  have hdescent : baseEnd_4751751 < baseStart_4751751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4751751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4751794 : List Nat := [3, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4]
def baseStart_4751794 : Nat := 118140960795 + 4751794 * 2 ^ 59
def prefixEnd_4751794 : Nat := 4983230072969 + 3 ^ 40 * 4751794 * 2
def baseEnd_4751794 : Nat := 2439954293150686817821903

theorem tailTrace_4751794 : CollatzResearch.WordTrace tailWord_4751794 prefixEnd_4751794 2439954293150686817821903 := by
  unfold tailWord_4751794
  simp only [CollatzResearch.WordTrace]
  refine ⟨43328041336767338662541609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115541443564712903100110957 43328041336767338662541609)
  ·
    refine ⟨32496031002575503996906207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43328041336767338662541609 32496031002575503996906207)
    ·
      refine ⟨48744046503863255995359311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32496031002575503996906207 48744046503863255995359311)
      ·
        refine ⟨73116069755794883993038967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48744046503863255995359311 73116069755794883993038967)
        ·
          refine ⟨109674104633692325989558451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73116069755794883993038967 109674104633692325989558451)
          ·
            refine ⟨164511156950538488984337677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109674104633692325989558451 164511156950538488984337677)
            ·
              refine ⟨61691683856451933369126629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 164511156950538488984337677 61691683856451933369126629)
              ·
                refine ⟨11567190723084737506711243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61691683856451933369126629 11567190723084737506711243)
                ·
                  refine ⟨17350786084627106260066865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11567190723084737506711243 17350786084627106260066865)
                  ·
                    refine ⟨13013089563470329695050149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17350786084627106260066865 13013089563470329695050149)
                    ·
                      refine ⟨2439954293150686817821903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13013089563470329695050149 2439954293150686817821903)
                      ·
                        rfl

theorem cell23_4751794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_4751794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4751794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4751794 prefixEnd_4751794 := by exact prefixLift 4751794
  have htrace : WordTrace (prefixWord ++ tailWord_4751794) baseStart_4751794 baseEnd_4751794 := by
    simpa [prefixWord, tailWord_4751794, baseEnd_4751794] using wordTrace_append hprefix tailTrace_4751794
  have hstable : (prefixWord ++ tailWord_4751794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4751794).length < 2 ^ (prefixWord ++ tailWord_4751794).sum := by decide
  have hdescent : baseEnd_4751794 < baseStart_4751794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4751794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4751804 : List Nat := [2, 2, 2, 4, 1, 2, 10]
def baseStart_4751804 : Nat := 118140960795 + 4751804 * 2 ^ 59
def prefixEnd_4751804 : Nat := 4983230072969 + 3 ^ 40 * 4751804 * 2
def baseEnd_4751804 : Nat := 30122955900706565169097

theorem tailTrace_4751804 : CollatzResearch.WordTrace tailWord_4751804 prefixEnd_4751804 30122955900706565169097 := by
  unfold tailWord_4751804
  simp only [CollatzResearch.WordTrace]
  refine ⟨86656265038516563179015233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115541686718022084238686977 86656265038516563179015233)
  ·
    refine ⟨64992198778887422384261425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86656265038516563179015233 64992198778887422384261425)
    ·
      refine ⟨48744149084165566788196069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64992198778887422384261425 48744149084165566788196069)
      ·
        refine ⟨9139527953281043772786763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48744149084165566788196069 9139527953281043772786763)
        ·
          refine ⟨13709291929921565659180145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9139527953281043772786763 13709291929921565659180145)
          ·
            refine ⟨10281968947441174244385109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13709291929921565659180145 10281968947441174244385109)
            ·
              refine ⟨30122955900706565169097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10281968947441174244385109 30122955900706565169097)
              ·
                rfl

theorem cell23_4751804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 10].length) (baseStart_4751804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4751804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4751804 prefixEnd_4751804 := by exact prefixLift 4751804
  have htrace : WordTrace (prefixWord ++ tailWord_4751804) baseStart_4751804 baseEnd_4751804 := by
    simpa [prefixWord, tailWord_4751804, baseEnd_4751804] using wordTrace_append hprefix tailTrace_4751804
  have hstable : (prefixWord ++ tailWord_4751804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4751804).length < 2 ^ (prefixWord ++ tailWord_4751804).sum := by decide
  have hdescent : baseEnd_4751804 < baseStart_4751804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4751804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4751807 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 6]
def baseStart_4751807 : Nat := 118140960795 + 4751807 * 2 ^ 59
def prefixEnd_4751807 : Nat := 4983230072969 + 3 ^ 40 * 4751807 * 2
def baseEnd_4751807 : Nat := 2439960968399195266959343

theorem tailTrace_4751807 : CollatzResearch.WordTrace tailWord_4751807 prefixEnd_4751807 2439960968399195266959343 := by
  unfold tailWord_4751807
  simp only [CollatzResearch.WordTrace]
  refine ⟨173312639496022257870389675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115541759664014838580259783 173312639496022257870389675)
  ·
    refine ⟨259968959244033386805584513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173312639496022257870389675 259968959244033386805584513)
    ·
      refine ⟨194976719433025040104188385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259968959244033386805584513 194976719433025040104188385)
      ·
        refine ⟨146232539574768780078141289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194976719433025040104188385 146232539574768780078141289)
        ·
          refine ⟨109674404681076585058605967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146232539574768780078141289 109674404681076585058605967)
          ·
            refine ⟨164511607021614877587908951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109674404681076585058605967 164511607021614877587908951)
            ·
              refine ⟨246767410532422316381863427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164511607021614877587908951 246767410532422316381863427)
              ·
                refine ⟨370151115798633474572795141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 246767410532422316381863427 370151115798633474572795141)
                ·
                  refine ⟨69403334212243776482399089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 370151115798633474572795141 69403334212243776482399089)
                  ·
                    refine ⟨52052500659182832361799317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 69403334212243776482399089 52052500659182832361799317)
                    ·
                      refine ⟨2439960968399195266959343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52052500659182832361799317 2439960968399195266959343)
                      ·
                        rfl

theorem cell23_4751807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_4751807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4751807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4751807 prefixEnd_4751807 := by exact prefixLift 4751807
  have htrace : WordTrace (prefixWord ++ tailWord_4751807) baseStart_4751807 baseEnd_4751807 := by
    simpa [prefixWord, tailWord_4751807, baseEnd_4751807] using wordTrace_append hprefix tailTrace_4751807
  have hstable : (prefixWord ++ tailWord_4751807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4751807).length < 2 ^ (prefixWord ++ tailWord_4751807).sum := by decide
  have hdescent : baseEnd_4751807 < baseStart_4751807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4751807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4751815 : List Nat := [1, 1, 4, 1, 1, 4, 2, 4, 1, 2, 2]
def baseStart_4751815 : Nat := 118140960795 + 4751815 * 2 ^ 59
def prefixEnd_4751815 : Nat := 4983230072969 + 3 ^ 40 * 4751815 * 2
def baseEnd_4751815 : Nat := 2439965076244431235659307

theorem tailTrace_4751815 : CollatzResearch.WordTrace tailWord_4751815 prefixEnd_4751815 2439965076244431235659307 := by
  unfold tailWord_4751815
  simp only [CollatzResearch.WordTrace]
  refine ⟨173312931279993275236680899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115541954186662183491120599 173312931279993275236680899)
  ·
    refine ⟨259969396919989912855021349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173312931279993275236680899 259969396919989912855021349)
    ·
      refine ⟨48744261922498108660316503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 259969396919989912855021349 48744261922498108660316503)
      ·
        refine ⟨73116392883747162990474755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48744261922498108660316503 73116392883747162990474755)
        ·
          refine ⟨109674589325620744485712133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73116392883747162990474755 109674589325620744485712133)
          ·
            refine ⟨20563985498553889591071025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109674589325620744485712133 20563985498553889591071025)
            ·
              refine ⟨15422989123915417193303269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20563985498553889591071025 15422989123915417193303269)
              ·
                refine ⟨2891810460734140723744363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15422989123915417193303269 2891810460734140723744363)
                ·
                  refine ⟨4337715691101211085616545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2891810460734140723744363 4337715691101211085616545)
                  ·
                    refine ⟨3253286768325908314212409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4337715691101211085616545 3253286768325908314212409)
                    ·
                      refine ⟨2439965076244431235659307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3253286768325908314212409 2439965076244431235659307)
                      ·
                        rfl

theorem cell23_4751815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 4, 1, 2, 2].length) (baseStart_4751815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4751815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4751815 prefixEnd_4751815 := by exact prefixLift 4751815
  have htrace : WordTrace (prefixWord ++ tailWord_4751815) baseStart_4751815 baseEnd_4751815 := by
    simpa [prefixWord, tailWord_4751815, baseEnd_4751815] using wordTrace_append hprefix tailTrace_4751815
  have hstable : (prefixWord ++ tailWord_4751815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4751815).length < 2 ^ (prefixWord ++ tailWord_4751815).sum := by decide
  have hdescent : baseEnd_4751815 < baseStart_4751815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4751815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4751817 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 1, 9]
def baseStart_4751817 : Nat := 118140960795 + 4751817 * 2 ^ 59
def prefixEnd_4751817 : Nat := 4983230072969 + 3 ^ 40 * 4751817 * 2
def baseEnd_4751817 : Nat := 813322034401913409278099

theorem tailTrace_4751817 : CollatzResearch.WordTrace tailWord_4751817 prefixEnd_4751817 813322034401913409278099 := by
  unfold tailWord_4751817
  simp only [CollatzResearch.WordTrace]
  refine ⟨173313004225986029578253705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115542002817324019718835803 173313004225986029578253705)
  ·
    refine ⟨129984753169489522183690279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173313004225986029578253705 129984753169489522183690279)
    ·
      refine ⟨194977129754234283275535419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129984753169489522183690279 194977129754234283275535419)
      ·
        refine ⟨292465694631351424913303129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194977129754234283275535419 292465694631351424913303129)
        ·
          refine ⟨219349270973513568684977347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292465694631351424913303129 219349270973513568684977347)
          ·
            refine ⟨329023906460270353027466021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219349270973513568684977347 329023906460270353027466021)
            ·
              refine ⟨61691982461300691192649879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 329023906460270353027466021 61691982461300691192649879)
              ·
                refine ⟨92537973691951036788974819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61691982461300691192649879 92537973691951036788974819)
                ·
                  refine ⟨138806960537926555183462229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92537973691951036788974819 138806960537926555183462229)
                  ·
                    refine ⟨813322034401913409278099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 138806960537926555183462229 813322034401913409278099)
                    ·
                      rfl

theorem cell23_4751817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 9].length) (baseStart_4751817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4751817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4751817 prefixEnd_4751817 := by exact prefixLift 4751817
  have htrace : WordTrace (prefixWord ++ tailWord_4751817) baseStart_4751817 baseEnd_4751817 := by
    simpa [prefixWord, tailWord_4751817, baseEnd_4751817] using wordTrace_append hprefix tailTrace_4751817
  have hstable : (prefixWord ++ tailWord_4751817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4751817).length < 2 ^ (prefixWord ++ tailWord_4751817).sum := by decide
  have hdescent : baseEnd_4751817 < baseStart_4751817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4751817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4751828 : List Nat := [2, 4, 1, 2, 2, 3, 1, 1, 1, 2, 4]
def baseStart_4751828 : Nat := 118140960795 + 4751828 * 2 ^ 59
def prefixEnd_4751828 : Nat := 4983230072969 + 3 ^ 40 * 4751828 * 2
def baseEnd_4751828 : Nat := 2439971751492939684796747

theorem tailTrace_4751828 : CollatzResearch.WordTrace tailWord_4751828 prefixEnd_4751828 2439971751492939684796747 := by
  unfold tailWord_4751828
  simp only [CollatzResearch.WordTrace]
  refine ⟨86656702714473089228452069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115542270285964118971269425 86656702714473089228452069)
  ·
    refine ⟨16248131758963704230334763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86656702714473089228452069 16248131758963704230334763)
    ·
      refine ⟨24372197638445556345502145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16248131758963704230334763 24372197638445556345502145)
      ·
        refine ⟨18279148228834167259126609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24372197638445556345502145 18279148228834167259126609)
        ·
          refine ⟨13709361171625625444344957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18279148228834167259126609 13709361171625625444344957)
          ·
            refine ⟨5141010439359609541629359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13709361171625625444344957 5141010439359609541629359)
            ·
              refine ⟨7711515659039414312444039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5141010439359609541629359 7711515659039414312444039)
              ·
                refine ⟨11567273488559121468666059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7711515659039414312444039 11567273488559121468666059)
                ·
                  refine ⟨17350910232838682202999089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11567273488559121468666059 17350910232838682202999089)
                  ·
                    refine ⟨13013182674629011652249317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17350910232838682202999089 13013182674629011652249317)
                    ·
                      refine ⟨2439971751492939684796747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13013182674629011652249317 2439971751492939684796747)
                      ·
                        rfl

theorem cell23_4751828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_4751828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4751828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4751828 prefixEnd_4751828 := by exact prefixLift 4751828
  have htrace : WordTrace (prefixWord ++ tailWord_4751828) baseStart_4751828 baseEnd_4751828 := by
    simpa [prefixWord, tailWord_4751828, baseEnd_4751828] using wordTrace_append hprefix tailTrace_4751828
  have hstable : (prefixWord ++ tailWord_4751828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4751828).length < 2 ^ (prefixWord ++ tailWord_4751828).sum := by decide
  have hdescent : baseEnd_4751828 < baseStart_4751828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4751828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4751892 : List Nat := [2, 4, 3, 1, 1, 1, 3, 2, 1, 3, 2]
def baseStart_4751892 : Nat := 118140960795 + 4751892 * 2 ^ 59
def prefixEnd_4751892 : Nat := 4983230072969 + 3 ^ 40 * 4751892 * 2
def baseEnd_4751892 : Nat := 2440004614254827434396453

theorem tailTrace_4751892 : CollatzResearch.WordTrace tailWord_4751892 prefixEnd_4751892 2440004614254827434396453 := by
  unfold tailWord_4751892
  simp only [CollatzResearch.WordTrace]
  refine ⟨86657869850357158693616965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115543826467142878258155953 86657869850357158693616965)
  ·
    refine ⟨16248350596941967255053181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86657869850357158693616965 16248350596941967255053181)
    ·
      refine ⟨6093131473853237720644943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16248350596941967255053181 6093131473853237720644943)
      ·
        refine ⟨9139697210779856580967415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6093131473853237720644943 9139697210779856580967415)
        ·
          refine ⟨13709545816169784871451123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9139697210779856580967415 13709545816169784871451123)
          ·
            refine ⟨20564318724254677307176685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13709545816169784871451123 20564318724254677307176685)
            ·
              refine ⟨7711619521595503990191257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20564318724254677307176685 7711619521595503990191257)
              ·
                refine ⟨5783714641196627992643443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7711619521595503990191257 5783714641196627992643443)
                ·
                  refine ⟨8675571961794941988965165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5783714641196627992643443 8675571961794941988965165)
                  ·
                    refine ⟨3253339485673103245861937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8675571961794941988965165 3253339485673103245861937)
                    ·
                      refine ⟨2440004614254827434396453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3253339485673103245861937 2440004614254827434396453)
                      ·
                        rfl

theorem cell23_4751892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_4751892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4751892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4751892 prefixEnd_4751892 := by exact prefixLift 4751892
  have htrace : WordTrace (prefixWord ++ tailWord_4751892) baseStart_4751892 baseEnd_4751892 := by
    simpa [prefixWord, tailWord_4751892, baseEnd_4751892] using wordTrace_append hprefix tailTrace_4751892
  have hstable : (prefixWord ++ tailWord_4751892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4751892).length < 2 ^ (prefixWord ++ tailWord_4751892).sum := by decide
  have hdescent : baseEnd_4751892 < baseStart_4751892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4751892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4751971 : List Nat := [1, 1, 1, 5, 1, 2, 1, 2, 5, 4]
def baseStart_4751971 : Nat := 118140960795 + 4751971 * 2 ^ 59
def prefixEnd_4751971 : Nat := 4983230072969 + 3 ^ 40 * 4751971 * 2
def baseEnd_4751971 : Nat := 813348393075510875102863

theorem tailTrace_4751971 : CollatzResearch.WordTrace tailWord_4751971 prefixEnd_4751971 813348393075510875102863 := by
  unfold tailWord_4751971
  simp only [CollatzResearch.WordTrace]
  refine ⟨173318621067428113879359767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115545747378285409252906511 173318621067428113879359767)
  ·
    refine ⟨259977931601142170819039651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173318621067428113879359767 259977931601142170819039651)
    ·
      refine ⟨389966897401713256228559477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259977931601142170819039651 389966897401713256228559477)
      ·
        refine ⟨36559396631410617771427451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 389966897401713256228559477 36559396631410617771427451)
        ·
          refine ⟨54839094947115926657141177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36559396631410617771427451 54839094947115926657141177)
          ·
            refine ⟨41129321210336944992855883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54839094947115926657141177 41129321210336944992855883)
            ·
              refine ⟨61693981815505417489283825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41129321210336944992855883 61693981815505417489283825)
              ·
                refine ⟨46270486361629063116962869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61693981815505417489283825 46270486361629063116962869)
                ·
                  refine ⟨4337858096402724667215269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46270486361629063116962869 4337858096402724667215269)
                  ·
                    refine ⟨813348393075510875102863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4337858096402724667215269 813348393075510875102863)
                    ·
                      rfl

theorem cell23_4751971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 5, 4].length) (baseStart_4751971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4751971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4751971 prefixEnd_4751971 := by exact prefixLift 4751971
  have htrace : WordTrace (prefixWord ++ tailWord_4751971) baseStart_4751971 baseEnd_4751971 := by
    simpa [prefixWord, tailWord_4751971, baseEnd_4751971] using wordTrace_append hprefix tailTrace_4751971
  have hstable : (prefixWord ++ tailWord_4751971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4751971).length < 2 ^ (prefixWord ++ tailWord_4751971).sum := by decide
  have hdescent : baseEnd_4751971 < baseStart_4751971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4751971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4751978 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 4, 4, 2]
def baseStart_4751978 : Nat := 118140960795 + 4751978 * 2 ^ 59
def prefixEnd_4751978 : Nat := 4983230072969 + 3 ^ 40 * 4751978 * 2
def baseEnd_4751978 : Nat := 2440048773591114097921057

theorem tailTrace_4751978 : CollatzResearch.WordTrace tailWord_4751978 prefixEnd_4751978 2440048773591114097921057 := by
  unfold tailWord_4751978
  simp only [CollatzResearch.WordTrace]
  refine ⟨43329719094600688518716147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115545917585601836049909725 43329719094600688518716147)
  ·
    refine ⟨64994578641901032778074221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43329719094600688518716147 64994578641901032778074221)
    ·
      refine ⟨24372966990712887291777833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64994578641901032778074221 24372966990712887291777833)
      ·
        refine ⟨18279725243034665468833375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24372966990712887291777833 18279725243034665468833375)
        ·
          refine ⟨27419587864551998203250063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18279725243034665468833375 27419587864551998203250063)
          ·
            refine ⟨41129381796827997304875095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27419587864551998203250063 41129381796827997304875095)
            ·
              refine ⟨61694072695241995957312643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41129381796827997304875095 61694072695241995957312643)
              ·
                refine ⟨92541109042862993935968965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61694072695241995957312643 92541109042862993935968965)
                ·
                  refine ⟨17351457945536811362994181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92541109042862993935968965 17351457945536811362994181)
                  ·
                    refine ⟨3253398364788152130561409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17351457945536811362994181 3253398364788152130561409)
                    ·
                      refine ⟨2440048773591114097921057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3253398364788152130561409 2440048773591114097921057)
                      ·
                        rfl

theorem cell23_4751978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_4751978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4751978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4751978 prefixEnd_4751978 := by exact prefixLift 4751978
  have htrace : WordTrace (prefixWord ++ tailWord_4751978) baseStart_4751978 baseEnd_4751978 := by
    simpa [prefixWord, tailWord_4751978, baseEnd_4751978] using wordTrace_append hprefix tailTrace_4751978
  have hstable : (prefixWord ++ tailWord_4751978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4751978).length < 2 ^ (prefixWord ++ tailWord_4751978).sum := by decide
  have hdescent : baseEnd_4751978 < baseStart_4751978 := by decide
  rcases family_descends (prefixWord ++ tailWord_4751978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4751994 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 2, 1, 9]
def baseStart_4751994 : Nat := 118140960795 + 4751994 * 2 ^ 59
def prefixEnd_4751994 : Nat := 4983230072969 + 3 ^ 40 * 4751994 * 2
def baseEnd_4751994 : Nat := 2440056989281586035320983

theorem tailTrace_4751994 : CollatzResearch.WordTrace tailWord_4751994 prefixEnd_4751994 2440056989281586035320983 := by
  unfold tailWord_4751994
  simp only [CollatzResearch.WordTrace]
  refine ⟨43329864986586197201861759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115546306630896525871631357 43329864986586197201861759)
  ·
    refine ⟨64994797479879295802792639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43329864986586197201861759 64994797479879295802792639)
    ·
      refine ⟨97492196219818943704188959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64994797479879295802792639 97492196219818943704188959)
      ·
        refine ⟨146238294329728415556283439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97492196219818943704188959 146238294329728415556283439)
        ·
          refine ⟨219357441494592623334425159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146238294329728415556283439 219357441494592623334425159)
          ·
            refine ⟨329036162241888935001637739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219357441494592623334425159 329036162241888935001637739)
            ·
              refine ⟨493554243362833402502456609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 329036162241888935001637739 493554243362833402502456609)
              ·
                refine ⟨370165682522125051876842457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 493554243362833402502456609 370165682522125051876842457)
                ·
                  refine ⟨277624261891593788907631843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 370165682522125051876842457 277624261891593788907631843)
                  ·
                    refine ⟨416436392837390683361447765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 277624261891593788907631843 416436392837390683361447765)
                    ·
                      refine ⟨2440056989281586035320983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 416436392837390683361447765 2440056989281586035320983)
                      ·
                        rfl

theorem cell23_4751994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_4751994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4751994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4751994 prefixEnd_4751994 := by exact prefixLift 4751994
  have htrace : WordTrace (prefixWord ++ tailWord_4751994) baseStart_4751994 baseEnd_4751994 := by
    simpa [prefixWord, tailWord_4751994, baseEnd_4751994] using wordTrace_append hprefix tailTrace_4751994
  have hstable : (prefixWord ++ tailWord_4751994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4751994).length < 2 ^ (prefixWord ++ tailWord_4751994).sum := by decide
  have hdescent : baseEnd_4751994 < baseStart_4751994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4751994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752039 : List Nat := [1, 1, 6, 3, 2, 1, 1, 1, 3, 4]
def baseStart_4752039 : Nat := 118140960795 + 4752039 * 2 ^ 59
def prefixEnd_4752039 : Nat := 4983230072969 + 3 ^ 40 * 4752039 * 2
def baseEnd_4752039 : Nat := 813360031970346119752759

theorem tailTrace_4752039 : CollatzResearch.WordTrace tailWord_4752039 prefixEnd_4752039 813360031970346119752759 := by
  unfold tailWord_4752039
  simp only [CollatzResearch.WordTrace]
  refine ⟨173321101231181761492835171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115547400820787840995223447 173321101231181761492835171)
  ·
    refine ⟨259981651846772642239252757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173321101231181761492835171 259981651846772642239252757)
    ·
      refine ⟨12186639930317467604964973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 259981651846772642239252757 12186639930317467604964973)
      ·
        refine ⟨4569989973869050351861865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12186639930317467604964973 4569989973869050351861865)
        ·
          refine ⟨3427492480401787763896399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4569989973869050351861865 3427492480401787763896399)
          ·
            refine ⟨5141238720602681645844599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3427492480401787763896399 5141238720602681645844599)
            ·
              refine ⟨7711858080904022468766899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5141238720602681645844599 7711858080904022468766899)
              ·
                refine ⟨11567787121356033703150349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7711858080904022468766899 11567787121356033703150349)
                ·
                  refine ⟨4337920170508512638681381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11567787121356033703150349 4337920170508512638681381)
                  ·
                    refine ⟨813360031970346119752759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4337920170508512638681381 813360031970346119752759)
                    ·
                      rfl

theorem cell23_4752039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_4752039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752039 prefixEnd_4752039 := by exact prefixLift 4752039
  have htrace : WordTrace (prefixWord ++ tailWord_4752039) baseStart_4752039 baseEnd_4752039 := by
    simpa [prefixWord, tailWord_4752039, baseEnd_4752039] using wordTrace_append hprefix tailTrace_4752039
  have hstable : (prefixWord ++ tailWord_4752039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752039).length < 2 ^ (prefixWord ++ tailWord_4752039).sum := by decide
  have hdescent : baseEnd_4752039 < baseStart_4752039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752078 : List Nat := [4, 1, 1, 1, 3, 3, 1, 2, 1, 6]
def baseStart_4752078 : Nat := 118140960795 + 4752078 * 2 ^ 59
def prefixEnd_4752078 : Nat := 4983230072969 + 3 ^ 40 * 4752078 * 2
def baseEnd_4752078 : Nat := 813366707218854568890199

theorem tailTrace_4752078 : CollatzResearch.WordTrace tailWord_4752078 prefixEnd_4752078 813366707218854568890199 := by
  unfold tailWord_4752078
  simp only [CollatzResearch.WordTrace]
  refine ⟨21665315459755058894188111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115548349118693647435669925 21665315459755058894188111)
  ·
    refine ⟨32497973189632588341282167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21665315459755058894188111 32497973189632588341282167)
    ·
      refine ⟨48746959784448882511923251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32497973189632588341282167 48746959784448882511923251)
      ·
        refine ⟨73120439676673323767884877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48746959784448882511923251 73120439676673323767884877)
        ·
          refine ⟨27420164878752496412956829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73120439676673323767884877 27420164878752496412956829)
          ·
            refine ⟨10282561829532186154858811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27420164878752496412956829 10282561829532186154858811)
            ·
              refine ⟨15423842744298279232288217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10282561829532186154858811 15423842744298279232288217)
              ·
                refine ⟨11567882058223709424216163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15423842744298279232288217 11567882058223709424216163)
                ·
                  refine ⟨17351823087335564136324245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11567882058223709424216163 17351823087335564136324245)
                  ·
                    refine ⟨813366707218854568890199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17351823087335564136324245 813366707218854568890199)
                    ·
                      rfl

theorem cell23_4752078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_4752078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752078 prefixEnd_4752078 := by exact prefixLift 4752078
  have htrace : WordTrace (prefixWord ++ tailWord_4752078) baseStart_4752078 baseEnd_4752078 := by
    simpa [prefixWord, tailWord_4752078, baseEnd_4752078] using wordTrace_append hprefix tailTrace_4752078
  have hstable : (prefixWord ++ tailWord_4752078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752078).length < 2 ^ (prefixWord ++ tailWord_4752078).sum := by decide
  have hdescent : baseEnd_4752078 < baseStart_4752078 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752082 : List Nat := [3, 2, 2, 2, 3, 1, 3, 1, 1, 5]
def baseStart_4752082 : Nat := 118140960795 + 4752082 * 2 ^ 59
def prefixEnd_4752082 : Nat := 4983230072969 + 3 ^ 40 * 4752082 * 2
def baseEnd_4752082 : Nat := 813367391859727230340193

theorem tailTrace_4752082 : CollatzResearch.WordTrace tailWord_4752082 prefixEnd_4752082 813367391859727230340193 := by
  unfold tailWord_4752082
  simp only [CollatzResearch.WordTrace]
  refine ⟨43330667392506494959162625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115548446380017319891100333 43330667392506494959162625)
  ·
    refine ⟨32498000544379871219371969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43330667392506494959162625 32498000544379871219371969)
    ·
      refine ⟨24373500408284903414528977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32498000544379871219371969 24373500408284903414528977)
      ·
        refine ⟨18280125306213677560896733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24373500408284903414528977 18280125306213677560896733)
        ·
          refine ⟨6855046989830129085336275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18280125306213677560896733 6855046989830129085336275)
          ·
            refine ⟨10282570484745193628004413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6855046989830129085336275 10282570484745193628004413)
            ·
              refine ⟨3855963931779447610501655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10282570484745193628004413 3855963931779447610501655)
              ·
                refine ⟨5783945897669171415752483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3855963931779447610501655 5783945897669171415752483)
                ·
                  refine ⟨8675918846503757123628725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5783945897669171415752483 8675918846503757123628725)
                  ·
                    refine ⟨813367391859727230340193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8675918846503757123628725 813367391859727230340193)
                    ·
                      rfl

theorem cell23_4752082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_4752082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752082 prefixEnd_4752082 := by exact prefixLift 4752082
  have htrace : WordTrace (prefixWord ++ tailWord_4752082) baseStart_4752082 baseEnd_4752082 := by
    simpa [prefixWord, tailWord_4752082, baseEnd_4752082] using wordTrace_append hprefix tailTrace_4752082
  have hstable : (prefixWord ++ tailWord_4752082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752082).length < 2 ^ (prefixWord ++ tailWord_4752082).sum := by decide
  have hdescent : baseEnd_4752082 < baseStart_4752082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752088 : List Nat := [2, 1, 2, 2, 3, 2, 3, 1, 1, 1, 5]
def baseStart_4752088 : Nat := 118140960795 + 4752088 * 2 ^ 59
def prefixEnd_4752088 : Nat := 4983230072969 + 3 ^ 40 * 4752088 * 2
def baseEnd_4752088 : Nat := 2440105256463108667545551

theorem tailTrace_4752088 : CollatzResearch.WordTrace tailWord_4752088 prefixEnd_4752088 2440105256463108667545551 := by
  unfold tailWord_4752088
  simp only [CollatzResearch.WordTrace]
  refine ⟨86661444204002121430684459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115548592272002828574245945 86661444204002121430684459)
  ·
    refine ⟨129992166306003182146026689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86661444204002121430684459 129992166306003182146026689)
    ·
      refine ⟨97494124729502386609520017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129992166306003182146026689 97494124729502386609520017)
      ·
        refine ⟨73120593547126789957140013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97494124729502386609520017 73120593547126789957140013)
        ·
          refine ⟨27420222580172546233927505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73120593547126789957140013 27420222580172546233927505)
          ·
            refine ⟨20565166935129409675445629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27420222580172546233927505 20565166935129409675445629)
            ·
              refine ⟨7711937600673528628292111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20565166935129409675445629 7711937600673528628292111)
              ·
                refine ⟨11567906401010292942438167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7711937600673528628292111 11567906401010292942438167)
                ·
                  refine ⟨17351859601515439413657251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11567906401010292942438167 17351859601515439413657251)
                  ·
                    refine ⟨26027789402273159120485877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17351859601515439413657251 26027789402273159120485877)
                    ·
                      refine ⟨2440105256463108667545551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26027789402273159120485877 2440105256463108667545551)
                      ·
                        rfl

theorem cell23_4752088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 1, 1, 5].length) (baseStart_4752088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752088 prefixEnd_4752088 := by exact prefixLift 4752088
  have htrace : WordTrace (prefixWord ++ tailWord_4752088) baseStart_4752088 baseEnd_4752088 := by
    simpa [prefixWord, tailWord_4752088, baseEnd_4752088] using wordTrace_append hprefix tailTrace_4752088
  have hstable : (prefixWord ++ tailWord_4752088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752088).length < 2 ^ (prefixWord ++ tailWord_4752088).sum := by decide
  have hdescent : baseEnd_4752088 < baseStart_4752088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752095 : List Nat := [1, 1, 2, 3, 2, 4, 2, 2, 2, 4]
def baseStart_4752095 : Nat := 118140960795 + 4752095 * 2 ^ 59
def prefixEnd_4752095 : Nat := 4983230072969 + 3 ^ 40 * 4752095 * 2
def baseEnd_4752095 : Nat := 813369616942563380052673

theorem tailTrace_4752095 : CollatzResearch.WordTrace tailWord_4752095 prefixEnd_4752095 813369616942563380052673 := by
  unfold tailWord_4752095
  simp only [CollatzResearch.WordTrace]
  refine ⟨173323143718978883056873739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115548762479319255371249159 173323143718978883056873739)
  ·
    refine ⟨259984715578468324585310609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173323143718978883056873739 259984715578468324585310609)
    ·
      refine ⟨194988536683851243438982957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259984715578468324585310609 194988536683851243438982957)
      ·
        refine ⟨73120701256444216289618609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194988536683851243438982957 73120701256444216289618609)
        ·
          refine ⟨54840525942333162217213957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73120701256444216289618609 54840525942333162217213957)
          ·
            refine ⟨10282598614187467915727617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54840525942333162217213957 10282598614187467915727617)
            ·
              refine ⟨7711948960640600936795713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10282598614187467915727617 7711948960640600936795713)
              ·
                refine ⟨5783961720480450702596785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7711948960640600936795713 5783961720480450702596785)
                ·
                  refine ⟨4337971290360338026947589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5783961720480450702596785 4337971290360338026947589)
                  ·
                    refine ⟨813369616942563380052673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4337971290360338026947589 813369616942563380052673)
                    ·
                      rfl

theorem cell23_4752095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2, 2, 4].length) (baseStart_4752095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752095 prefixEnd_4752095 := by exact prefixLift 4752095
  have htrace : WordTrace (prefixWord ++ tailWord_4752095) baseStart_4752095 baseEnd_4752095 := by
    simpa [prefixWord, tailWord_4752095, baseEnd_4752095] using wordTrace_append hprefix tailTrace_4752095
  have hstable : (prefixWord ++ tailWord_4752095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752095).length < 2 ^ (prefixWord ++ tailWord_4752095).sum := by decide
  have hdescent : baseEnd_4752095 < baseStart_4752095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752131 : List Nat := [1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 5]
def baseStart_4752131 : Nat := 118140960795 + 4752131 * 2 ^ 59
def prefixEnd_4752131 : Nat := 4983230072969 + 3 ^ 40 * 4752131 * 2
def baseEnd_4752131 : Nat := 2440127336131251999307853

theorem tailTrace_4752131 : CollatzResearch.WordTrace tailWord_4752131 prefixEnd_4752131 2440127336131251999307853 := by
  unfold tailWord_4752131
  simp only [CollatzResearch.WordTrace]
  refine ⟨173324456746848461205184247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115549637831232307470122831 173324456746848461205184247)
  ·
    refine ⟨259986685120272691807776371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173324456746848461205184247 259986685120272691807776371)
    ·
      refine ⟨389980027680409037711664557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259986685120272691807776371 389980027680409037711664557)
      ·
        refine ⟨146242510380153389141874209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 389980027680409037711664557 146242510380153389141874209)
        ·
          refine ⟨109681882785115041856405657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146242510380153389141874209 109681882785115041856405657)
          ·
            refine ⟨82261412088836281392304243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109681882785115041856405657 82261412088836281392304243)
            ·
              refine ⟨123392118133254422088456365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82261412088836281392304243 123392118133254422088456365)
              ·
                refine ⟨46272044299970408283171137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123392118133254422088456365 46272044299970408283171137)
                ·
                  refine ⟨34704033224977806212378353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46272044299970408283171137 34704033224977806212378353)
                  ·
                    refine ⟨26028024918733354659283765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34704033224977806212378353 26028024918733354659283765)
                    ·
                      refine ⟨2440127336131251999307853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26028024918733354659283765 2440127336131251999307853)
                      ·
                        rfl

theorem cell23_4752131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_4752131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752131 prefixEnd_4752131 := by exact prefixLift 4752131
  have htrace : WordTrace (prefixWord ++ tailWord_4752131) baseStart_4752131 baseEnd_4752131 := by
    simpa [prefixWord, tailWord_4752131, baseEnd_4752131] using wordTrace_append hprefix tailTrace_4752131
  have hstable : (prefixWord ++ tailWord_4752131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752131).length < 2 ^ (prefixWord ++ tailWord_4752131).sum := by decide
  have hdescent : baseEnd_4752131 < baseStart_4752131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752135 : List Nat := [1, 1, 4, 4, 1, 1, 2, 2, 1, 3, 3]
def baseStart_4752135 : Nat := 118140960795 + 4752135 * 2 ^ 59
def prefixEnd_4752135 : Nat := 4983230072969 + 3 ^ 40 * 4752135 * 2
def baseEnd_4752135 : Nat := 2440129390053869983657835

theorem tailTrace_4752135 : CollatzResearch.WordTrace tailWord_4752135 prefixEnd_4752135 2440129390053869983657835 := by
  unfold tailWord_4752135
  simp only [CollatzResearch.WordTrace]
  refine ⟨173324602638833969888329859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115549735092555979925553239 173324602638833969888329859)
  ·
    refine ⟨259986903958250954832494789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173324602638833969888329859 259986903958250954832494789)
    ·
      refine ⟨48747544492172054031092773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 259986903958250954832494789 48747544492172054031092773)
      ·
        refine ⟨9140164592282260130829895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48747544492172054031092773 9140164592282260130829895)
        ·
          refine ⟨13710246888423390196244843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9140164592282260130829895 13710246888423390196244843)
          ·
            refine ⟨20565370332635085294367265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13710246888423390196244843 20565370332635085294367265)
            ·
              refine ⟨15424027749476313970775449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20565370332635085294367265 15424027749476313970775449)
              ·
                refine ⟨11568020812107235478081587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15424027749476313970775449 11568020812107235478081587)
                ·
                  refine ⟨17352031218160853217122381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11568020812107235478081587 17352031218160853217122381)
                  ·
                    refine ⟨6507011706810319956420893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17352031218160853217122381 6507011706810319956420893)
                    ·
                      refine ⟨2440129390053869983657835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6507011706810319956420893 2440129390053869983657835)
                      ·
                        rfl

theorem cell23_4752135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_4752135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752135 prefixEnd_4752135 := by exact prefixLift 4752135
  have htrace : WordTrace (prefixWord ++ tailWord_4752135) baseStart_4752135 baseEnd_4752135 := by
    simpa [prefixWord, tailWord_4752135, baseEnd_4752135] using wordTrace_append hprefix tailTrace_4752135
  have hstable : (prefixWord ++ tailWord_4752135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752135).length < 2 ^ (prefixWord ++ tailWord_4752135).sum := by decide
  have hdescent : baseEnd_4752135 < baseStart_4752135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752146 : List Nat := [3, 2, 4, 1, 3, 1, 1, 2, 2, 4]
def baseStart_4752146 : Nat := 118140960795 + 4752146 * 2 ^ 59
def prefixEnd_4752146 : Nat := 4983230072969 + 3 ^ 40 * 4752146 * 2
def baseEnd_4752146 : Nat := 813378346113689813540095

theorem tailTrace_4752146 : CollatzResearch.WordTrace tailWord_4752146 prefixEnd_4752146 813378346113689813540095 := by
  unfold tailWord_4752146
  simp only [CollatzResearch.WordTrace]
  refine ⟨43331250960448529691745073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115550002561196079177986861 43331250960448529691745073)
  ·
    refine ⟨32498438220336397268808805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43331250960448529691745073 32498438220336397268808805)
    ·
      refine ⟨6093457166313074487901651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32498438220336397268808805 6093457166313074487901651)
      ·
        refine ⟨9140185749469611731852477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6093457166313074487901651 9140185749469611731852477)
        ·
          refine ⟨3427569656051104399444679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9140185749469611731852477 3427569656051104399444679)
          ·
            refine ⟨5141354484076656599167019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3427569656051104399444679 5141354484076656599167019)
            ·
              refine ⟨7712031726114984898750529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5141354484076656599167019 7712031726114984898750529)
              ·
                refine ⟨5784023794586238674062897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7712031726114984898750529 5784023794586238674062897)
                ·
                  refine ⟨4338017845939679005547173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5784023794586238674062897 4338017845939679005547173)
                  ·
                    refine ⟨813378346113689813540095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4338017845939679005547173 813378346113689813540095)
                    ·
                      rfl

theorem cell23_4752146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_4752146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752146 prefixEnd_4752146 := by exact prefixLift 4752146
  have htrace : WordTrace (prefixWord ++ tailWord_4752146) baseStart_4752146 baseEnd_4752146 := by
    simpa [prefixWord, tailWord_4752146, baseEnd_4752146] using wordTrace_append hprefix tailTrace_4752146
  have hstable : (prefixWord ++ tailWord_4752146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752146).length < 2 ^ (prefixWord ++ tailWord_4752146).sum := by decide
  have hdescent : baseEnd_4752146 < baseStart_4752146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752168 : List Nat := [2, 1, 5, 1, 1, 1, 1, 3, 2, 6]
def baseStart_4752168 : Nat := 118140960795 + 4752168 * 2 ^ 59
def prefixEnd_4752168 : Nat := 4983230072969 + 3 ^ 40 * 4752168 * 2
def baseEnd_4752168 : Nat := 813382111638489451515061

theorem tailTrace_4752168 : CollatzResearch.WordTrace tailWord_4752168 prefixEnd_4752168 813382111638489451515061 := by
  unfold tailWord_4752168
  simp only [CollatzResearch.WordTrace]
  refine ⟨86662903123857208262140579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115550537498476277682854105 86662903123857208262140579)
  ·
    refine ⟨129994354685785812393210869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86662903123857208262140579 129994354685785812393210869)
    ·
      refine ⟨12186970751792419911863519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 129994354685785812393210869 12186970751792419911863519)
      ·
        refine ⟨18280456127688629867795279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12186970751792419911863519 18280456127688629867795279)
        ·
          refine ⟨27420684191532944801692919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18280456127688629867795279 27420684191532944801692919)
          ·
            refine ⟨41131026287299417202539379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27420684191532944801692919 41131026287299417202539379)
            ·
              refine ⟨61696539430949125803809069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41131026287299417202539379 61696539430949125803809069)
              ·
                refine ⟨23136202286605922176428401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61696539430949125803809069 23136202286605922176428401)
                ·
                  refine ⟨17352151714954441632321301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23136202286605922176428401 17352151714954441632321301)
                  ·
                    refine ⟨813382111638489451515061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17352151714954441632321301 813382111638489451515061)
                    ·
                      rfl

theorem cell23_4752168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_4752168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752168 prefixEnd_4752168 := by exact prefixLift 4752168
  have htrace : WordTrace (prefixWord ++ tailWord_4752168) baseStart_4752168 baseEnd_4752168 := by
    simpa [prefixWord, tailWord_4752168, baseEnd_4752168] using wordTrace_append hprefix tailTrace_4752168
  have hstable : (prefixWord ++ tailWord_4752168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752168).length < 2 ^ (prefixWord ++ tailWord_4752168).sum := by decide
  have hdescent : baseEnd_4752168 < baseStart_4752168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752175 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 8, 2, 2]
def baseStart_4752175 : Nat := 118140960795 + 4752175 * 2 ^ 59
def prefixEnd_4752175 : Nat := 4983230072969 + 3 ^ 40 * 4752175 * 2
def baseEnd_4752175 : Nat := 2440149929280049827157651

theorem tailTrace_4752175 : CollatzResearch.WordTrace tailWord_4752175 prefixEnd_4752175 2440149929280049827157651 := by
  unfold tailWord_4752175
  simp only [CollatzResearch.WordTrace]
  refine ⟨173326061558689056719785979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115550707705792704479857319 173326061558689056719785979)
  ·
    refine ⟨259989092338033585079678969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173326061558689056719785979 259989092338033585079678969)
    ·
      refine ⟨194991819253525188809759227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259989092338033585079678969 194991819253525188809759227)
      ·
        refine ⟨292487728880287783214638841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194991819253525188809759227 292487728880287783214638841)
        ·
          refine ⟨219365796660215837410979131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292487728880287783214638841 219365796660215837410979131)
          ·
            refine ⟨329048694990323756116468697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219365796660215837410979131 329048694990323756116468697)
            ·
              refine ⟨246786521242742817087351523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 329048694990323756116468697 246786521242742817087351523)
              ·
                refine ⟨370179781864114225631027285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 246786521242742817087351523 370179781864114225631027285)
                ·
                  refine ⟨4338044318720088581613601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 370179781864114225631027285 4338044318720088581613601)
                  ·
                    refine ⟨3253533239040066436210201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4338044318720088581613601 3253533239040066436210201)
                    ·
                      refine ⟨2440149929280049827157651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3253533239040066436210201 2440149929280049827157651)
                      ·
                        rfl

theorem cell23_4752175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 8, 2, 2].length) (baseStart_4752175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752175 prefixEnd_4752175 := by exact prefixLift 4752175
  have htrace : WordTrace (prefixWord ++ tailWord_4752175) baseStart_4752175 baseEnd_4752175 := by
    simpa [prefixWord, tailWord_4752175, baseEnd_4752175] using wordTrace_append hprefix tailTrace_4752175
  have hstable : (prefixWord ++ tailWord_4752175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752175).length < 2 ^ (prefixWord ++ tailWord_4752175).sum := by decide
  have hdescent : baseEnd_4752175 < baseStart_4752175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752178 : List Nat := [3, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5]
def baseStart_4752178 : Nat := 118140960795 + 4752178 * 2 ^ 59
def prefixEnd_4752178 : Nat := 4983230072969 + 3 ^ 40 * 4752178 * 2
def baseEnd_4752178 : Nat := 2440151469722013315420137

theorem tailTrace_4752178 : CollatzResearch.WordTrace tailWord_4752178 prefixEnd_4752178 2440151469722013315420137 := by
  unfold tailWord_4752178
  simp only [CollatzResearch.WordTrace]
  refine ⟨43331542744419547058036297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115550780651785458821430125 43331542744419547058036297)
  ·
    refine ⟨32498657058314660293527223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43331542744419547058036297 32498657058314660293527223)
    ·
      refine ⟨48747985587471990440290835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32498657058314660293527223 48747985587471990440290835)
      ·
        refine ⟨73121978381207985660436253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48747985587471990440290835 73121978381207985660436253)
        ·
          refine ⟨27420741892952994622663595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73121978381207985660436253 27420741892952994622663595)
          ·
            refine ⟨41131112839429491933995393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27420741892952994622663595 41131112839429491933995393)
            ·
              refine ⟨30848334629572118950496545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41131112839429491933995393 30848334629572118950496545)
              ·
                refine ⟨23136250972179089212872409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30848334629572118950496545 23136250972179089212872409)
                ·
                  refine ⟨17352188229134316909654307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23136250972179089212872409 17352188229134316909654307)
                  ·
                    refine ⟨26028282343701475364481461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17352188229134316909654307 26028282343701475364481461)
                    ·
                      refine ⟨2440151469722013315420137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26028282343701475364481461 2440151469722013315420137)
                      ·
                        rfl

theorem cell23_4752178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_4752178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752178 prefixEnd_4752178 := by exact prefixLift 4752178
  have htrace : WordTrace (prefixWord ++ tailWord_4752178) baseStart_4752178 baseEnd_4752178 := by
    simpa [prefixWord, tailWord_4752178, baseEnd_4752178] using wordTrace_append hprefix tailTrace_4752178
  have hstable : (prefixWord ++ tailWord_4752178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752178).length < 2 ^ (prefixWord ++ tailWord_4752178).sum := by decide
  have hdescent : baseEnd_4752178 < baseStart_4752178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752208 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 3]
def baseStart_4752208 : Nat := 118140960795 + 4752208 * 2 ^ 59
def prefixEnd_4752208 : Nat := 4983230072969 + 3 ^ 40 * 4752208 * 2
def baseEnd_4752208 : Nat := 2440166874141648198044999

theorem tailTrace_4752208 : CollatzResearch.WordTrace tailWord_4752208 prefixEnd_4752208 2440166874141648198044999 := by
  unfold tailWord_4752208
  simp only [CollatzResearch.WordTrace]
  refine ⟨86663632583784751677868639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115551510111713002237158185 86663632583784751677868639)
  ·
    refine ⟨129995448875677127516802959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86663632583784751677868639 129995448875677127516802959)
    ·
      refine ⟨194993173313515691275204439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129995448875677127516802959 194993173313515691275204439)
      ·
        refine ⟨292489759970273536912806659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194993173313515691275204439 292489759970273536912806659)
        ·
          refine ⟨438734639955410305369209989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292489759970273536912806659 438734639955410305369209989)
          ·
            refine ⟨82262744991639432256726873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 438734639955410305369209989 82262744991639432256726873)
            ·
              refine ⟨61697058743729574192545155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82262744991639432256726873 61697058743729574192545155)
              ·
                refine ⟨92545588115594361288817733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61697058743729574192545155 92545588115594361288817733)
                ·
                  refine ⟨17352297771673942741653325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92545588115594361288817733 17352297771673942741653325)
                  ·
                    refine ⟨6507111664377728528119997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17352297771673942741653325 6507111664377728528119997)
                    ·
                      refine ⟨2440166874141648198044999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6507111664377728528119997 2440166874141648198044999)
                      ·
                        rfl

theorem cell23_4752208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 3].length) (baseStart_4752208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752208 prefixEnd_4752208 := by exact prefixLift 4752208
  have htrace : WordTrace (prefixWord ++ tailWord_4752208) baseStart_4752208 baseEnd_4752208 := by
    simpa [prefixWord, tailWord_4752208, baseEnd_4752208] using wordTrace_append hprefix tailTrace_4752208
  have hstable : (prefixWord ++ tailWord_4752208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752208).length < 2 ^ (prefixWord ++ tailWord_4752208).sum := by decide
  have hdescent : baseEnd_4752208 < baseStart_4752208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752215 : List Nat := [1, 1, 3, 2, 4, 3, 1, 1, 7]
def baseStart_4752215 : Nat := 118140960795 + 4752215 * 2 ^ 59
def prefixEnd_4752215 : Nat := 4983230072969 + 3 ^ 40 * 4752215 * 2
def baseEnd_4752215 : Nat := 271130052056247741184163

theorem tailTrace_4752215 : CollatzResearch.WordTrace tailWord_4752215 prefixEnd_4752215 271130052056247741184163 := by
  unfold tailWord_4752215
  simp only [CollatzResearch.WordTrace]
  refine ⟨173327520478544143551242099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115551680319029429034161399 173327520478544143551242099)
  ·
    refine ⟨259991280717816215326863149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173327520478544143551242099 259991280717816215326863149)
    ·
      refine ⟨97496730269181080747573681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 259991280717816215326863149 97496730269181080747573681)
      ·
        refine ⟨73122547701885810560680261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97496730269181080747573681 73122547701885810560680261)
        ·
          refine ⟨13710477694103589480127549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73122547701885810560680261 13710477694103589480127549)
          ·
            refine ⟨5141429135288846055047831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13710477694103589480127549 5141429135288846055047831)
            ·
              refine ⟨7712143702933269082571747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5141429135288846055047831 7712143702933269082571747)
              ·
                refine ⟨11568215554399903623857621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7712143702933269082571747 11568215554399903623857621)
                ·
                  refine ⟨271130052056247741184163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11568215554399903623857621 271130052056247741184163)
                  ·
                    rfl

theorem cell23_4752215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 7].length) (baseStart_4752215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752215 prefixEnd_4752215 := by exact prefixLift 4752215
  have htrace : WordTrace (prefixWord ++ tailWord_4752215) baseStart_4752215 baseEnd_4752215 := by
    simpa [prefixWord, tailWord_4752215, baseEnd_4752215] using wordTrace_append hprefix tailTrace_4752215
  have hstable : (prefixWord ++ tailWord_4752215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752215).length < 2 ^ (prefixWord ++ tailWord_4752215).sum := by decide
  have hdescent : baseEnd_4752215 < baseStart_4752215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752226 : List Nat := [3, 3, 2, 1, 3, 1, 1, 3, 2, 2, 2]
def baseStart_4752226 : Nat := 118140960795 + 4752226 * 2 ^ 59
def prefixEnd_4752226 : Nat := 4983230072969 + 3 ^ 40 * 4752226 * 2
def baseEnd_4752226 : Nat := 2440176116793429127619917

theorem tailTrace_4752226 : CollatzResearch.WordTrace tailWord_4752226 prefixEnd_4752226 2440176116793429127619917 := by
  unfold tailWord_4752226
  simp only [CollatzResearch.WordTrace]
  refine ⟨43331980420376073107473133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115551947787669528286595021 43331980420376073107473133)
  ·
    refine ⟨16249492657641027415302425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43331980420376073107473133 16249492657641027415302425)
    ·
      refine ⟨12187119493230770561476819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16249492657641027415302425 12187119493230770561476819)
      ·
        refine ⟨18280679239846155842215229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12187119493230770561476819 18280679239846155842215229)
        ·
          refine ⟨6855254714942308440830711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18280679239846155842215229 6855254714942308440830711)
          ·
            refine ⟨10282882072413462661246067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6855254714942308440830711 10282882072413462661246067)
            ·
              refine ⟨15424323108620193991869101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10282882072413462661246067 15424323108620193991869101)
              ·
                refine ⟨5784121165732572746950913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15424323108620193991869101 5784121165732572746950913)
                ·
                  refine ⟨4338090874299429560213185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5784121165732572746950913 4338090874299429560213185)
                  ·
                    refine ⟨3253568155724572170159889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4338090874299429560213185 3253568155724572170159889)
                    ·
                      refine ⟨2440176116793429127619917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3253568155724572170159889 2440176116793429127619917)
                      ·
                        rfl

theorem cell23_4752226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_4752226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752226 prefixEnd_4752226 := by exact prefixLift 4752226
  have htrace : WordTrace (prefixWord ++ tailWord_4752226) baseStart_4752226 baseEnd_4752226 := by
    simpa [prefixWord, tailWord_4752226, baseEnd_4752226] using wordTrace_append hprefix tailTrace_4752226
  have hstable : (prefixWord ++ tailWord_4752226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752226).length < 2 ^ (prefixWord ++ tailWord_4752226).sum := by decide
  have hdescent : baseEnd_4752226 < baseStart_4752226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752245 : List Nat := [1, 3, 4, 1, 1, 2, 1, 3, 2, 5]
def baseStart_4752245 : Nat := 118140960795 + 4752245 * 2 ^ 59
def prefixEnd_4752245 : Nat := 4983230072969 + 3 ^ 40 * 4752245 * 2
def baseEnd_4752245 : Nat := 813395290975288184427443

theorem tailTrace_4752245 : CollatzResearch.WordTrace tailWord_4752245 prefixEnd_4752245 813395290975288184427443 := by
  unfold tailWord_4752245
  simp only [CollatzResearch.WordTrace]
  refine ⟨173328614668435458674834189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115552409778956972449889459 173328614668435458674834189)
  ·
    refine ⟨64998230500663297003062821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173328614668435458674834189 64998230500663297003062821)
    ·
      refine ⟨12187168218874368188074279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64998230500663297003062821 12187168218874368188074279)
      ·
        refine ⟨18280752328311552282111419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12187168218874368188074279 18280752328311552282111419)
        ·
          refine ⟨27421128492467328423167129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18280752328311552282111419 27421128492467328423167129)
          ·
            refine ⟨20565846369350496317375347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27421128492467328423167129 20565846369350496317375347)
            ·
              refine ⟨30848769554025744476063021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20565846369350496317375347 30848769554025744476063021)
              ·
                refine ⟨11568288582759654178523633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30848769554025744476063021 11568288582759654178523633)
                ·
                  refine ⟨8676216437069740633892725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11568288582759654178523633 8676216437069740633892725)
                  ·
                    refine ⟨813395290975288184427443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8676216437069740633892725 813395290975288184427443)
                    ·
                      rfl

theorem cell23_4752245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_4752245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752245 prefixEnd_4752245 := by exact prefixLift 4752245
  have htrace : WordTrace (prefixWord ++ tailWord_4752245) baseStart_4752245 baseEnd_4752245 := by
    simpa [prefixWord, tailWord_4752245, baseEnd_4752245] using wordTrace_append hprefix tailTrace_4752245
  have hstable : (prefixWord ++ tailWord_4752245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752245).length < 2 ^ (prefixWord ++ tailWord_4752245).sum := by decide
  have hdescent : baseEnd_4752245 < baseStart_4752245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752265 : List Nat := [1, 2, 1, 1, 5, 2, 2, 2, 2, 1, 4]
def baseStart_4752265 : Nat := 118140960795 + 4752265 * 2 ^ 59
def prefixEnd_4752265 : Nat := 4983230072969 + 3 ^ 40 * 4752265 * 2
def baseEnd_4752265 : Nat := 2440196142538954475032237

theorem tailTrace_4752265 : CollatzResearch.WordTrace tailWord_4752265 prefixEnd_4752265 2440196142538954475032237 := by
  unfold tailWord_4752265
  simp only [CollatzResearch.WordTrace]
  refine ⟨173329344128363002090562249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115552896085575334727041499 173329344128363002090562249)
  ·
    refine ⟨129997008096272251567921687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173329344128363002090562249 129997008096272251567921687)
    ·
      refine ⟨194995512144408377351882531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129997008096272251567921687 194995512144408377351882531)
      ·
        refine ⟨292493268216612566027823797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194995512144408377351882531 292493268216612566027823797)
        ·
          refine ⟨27421243895307428065108481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 292493268216612566027823797 27421243895307428065108481)
          ·
            refine ⟨20565932921480571048831361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27421243895307428065108481 20565932921480571048831361)
            ·
              refine ⟨15424449691110428286623521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20565932921480571048831361 15424449691110428286623521)
              ·
                refine ⟨11568337268332821214967641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15424449691110428286623521 11568337268332821214967641)
                ·
                  refine ⟨8676252951249615911225731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11568337268332821214967641 8676252951249615911225731)
                  ·
                    refine ⟨13014379426874423866838597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8676252951249615911225731 13014379426874423866838597)
                    ·
                      refine ⟨2440196142538954475032237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13014379426874423866838597 2440196142538954475032237)
                      ·
                        rfl

theorem cell23_4752265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2, 1, 4].length) (baseStart_4752265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752265 prefixEnd_4752265 := by exact prefixLift 4752265
  have htrace : WordTrace (prefixWord ++ tailWord_4752265) baseStart_4752265 baseEnd_4752265 := by
    simpa [prefixWord, tailWord_4752265, baseEnd_4752265] using wordTrace_append hprefix tailTrace_4752265
  have hstable : (prefixWord ++ tailWord_4752265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752265).length < 2 ^ (prefixWord ++ tailWord_4752265).sum := by decide
  have hdescent : baseEnd_4752265 < baseStart_4752265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752285 : List Nat := [1, 4, 2, 1, 2, 1, 2, 2, 1, 4, 3]
def baseStart_4752285 : Nat := 118140960795 + 4752285 * 2 ^ 59
def prefixEnd_4752285 : Nat := 4983230072969 + 3 ^ 40 * 4752285 * 2
def baseEnd_4752285 : Nat := 2440206412152044396782145

theorem tailTrace_4752285 : CollatzResearch.WordTrace tailWord_4752285 prefixEnd_4752285 2440206412152044396782145 := by
  unfold tailWord_4752285
  simp only [CollatzResearch.WordTrace]
  refine ⟨173330073588290545506290309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115553382392193697004193539 173330073588290545506290309)
  ·
    refine ⟨32499388797804477282429433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173330073588290545506290309 32499388797804477282429433)
    ·
      refine ⟨24374541598353357961822075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32499388797804477282429433 24374541598353357961822075)
      ·
        refine ⟨36561812397530036942733113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24374541598353357961822075 36561812397530036942733113)
        ·
          refine ⟨27421359298147527707049835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36561812397530036942733113 27421359298147527707049835)
          ·
            refine ⟨41132038947221291560574753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27421359298147527707049835 41132038947221291560574753)
            ·
              refine ⟨30849029210415968670431065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41132038947221291560574753 30849029210415968670431065)
              ·
                refine ⟨23136771907811976502823299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30849029210415968670431065 23136771907811976502823299)
                ·
                  refine ⟨34705157861717964754234949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23136771907811976502823299 34705157861717964754234949)
                  ·
                    refine ⟨6507217099072118391419053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34705157861717964754234949 6507217099072118391419053)
                    ·
                      refine ⟨2440206412152044396782145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6507217099072118391419053 2440206412152044396782145)
                      ·
                        rfl

theorem cell23_4752285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_4752285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752285 prefixEnd_4752285 := by exact prefixLift 4752285
  have htrace : WordTrace (prefixWord ++ tailWord_4752285) baseStart_4752285 baseEnd_4752285 := by
    simpa [prefixWord, tailWord_4752285, baseEnd_4752285] using wordTrace_append hprefix tailTrace_4752285
  have hstable : (prefixWord ++ tailWord_4752285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752285).length < 2 ^ (prefixWord ++ tailWord_4752285).sum := by decide
  have hdescent : baseEnd_4752285 < baseStart_4752285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752309 : List Nat := [1, 3, 3, 2, 1, 1, 4, 3, 1, 4]
def baseStart_4752309 : Nat := 118140960795 + 4752309 * 2 ^ 59
def prefixEnd_4752309 : Nat := 4983230072969 + 3 ^ 40 * 4752309 * 2
def baseEnd_4752309 : Nat := 813406245229250767627345

theorem tailTrace_4752309 : CollatzResearch.WordTrace tailWord_4752309 prefixEnd_4752309 813406245229250767627345 := by
  unfold tailWord_4752309
  simp only [CollatzResearch.WordTrace]
  refine ⟨173330948940203597605163981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115553965960135731736775987 173330948940203597605163981)
  ·
    refine ⟨64999105852576349101936493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173330948940203597605163981 64999105852576349101936493)
    ·
      refine ⟨24374664694716130913226185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64999105852576349101936493 24374664694716130913226185)
      ·
        refine ⟨18280998521037098184919639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24374664694716130913226185 18280998521037098184919639)
        ·
          refine ⟨27421497781555647277379459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18280998521037098184919639 27421497781555647277379459)
          ·
            refine ⟨41132246672333470916069189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27421497781555647277379459 41132246672333470916069189)
            ·
              refine ⟨7712296251062525796762973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41132246672333470916069189 7712296251062525796762973)
              ·
                refine ⟨2892111094148447173786115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7712296251062525796762973 2892111094148447173786115)
                ·
                  refine ⟨4338166641222670760679173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2892111094148447173786115 4338166641222670760679173)
                  ·
                    refine ⟨813406245229250767627345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4338166641222670760679173 813406245229250767627345)
                    ·
                      rfl

theorem cell23_4752309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_4752309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752309 prefixEnd_4752309 := by exact prefixLift 4752309
  have htrace : WordTrace (prefixWord ++ tailWord_4752309) baseStart_4752309 baseEnd_4752309 := by
    simpa [prefixWord, tailWord_4752309, baseEnd_4752309] using wordTrace_append hprefix tailTrace_4752309
  have hstable : (prefixWord ++ tailWord_4752309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752309).length < 2 ^ (prefixWord ++ tailWord_4752309).sum := by decide
  have hdescent : baseEnd_4752309 < baseStart_4752309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752349 : List Nat := [1, 4, 3, 1, 2, 1, 2, 2, 3, 1, 3]
def baseStart_4752349 : Nat := 118140960795 + 4752349 * 2 ^ 59
def prefixEnd_4752349 : Nat := 4983230072969 + 3 ^ 40 * 4752349 * 2
def baseEnd_4752349 : Nat := 2440239274913932146381851

theorem tailTrace_4752349 : CollatzResearch.WordTrace tailWord_4752349 prefixEnd_4752349 2440239274913932146381851 := by
  unfold tailWord_4752349
  simp only [CollatzResearch.WordTrace]
  refine ⟨173332407860058684436620101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115554938573372456291080067 173332407860058684436620101)
  ·
    refine ⟨32499826473761003331866269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173332407860058684436620101 32499826473761003331866269)
    ·
      refine ⟨12187434927660376249449851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32499826473761003331866269 12187434927660376249449851)
      ·
        refine ⟨18281152391490564374174777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12187434927660376249449851 18281152391490564374174777)
        ·
          refine ⟨13710864293617923280631083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18281152391490564374174777 13710864293617923280631083)
          ·
            refine ⟨20566296440426884920946625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13710864293617923280631083 20566296440426884920946625)
            ·
              refine ⟨15424722330320163690709969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20566296440426884920946625 15424722330320163690709969)
              ·
                refine ⟨11568541747740122768032477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15424722330320163690709969 11568541747740122768032477)
                ·
                  refine ⟨4338203155402546038012179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11568541747740122768032477 4338203155402546038012179)
                  ·
                    refine ⟨6507304733103819057018269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4338203155402546038012179 6507304733103819057018269)
                    ·
                      refine ⟨2440239274913932146381851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6507304733103819057018269 2440239274913932146381851)
                      ·
                        rfl

theorem cell23_4752349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_4752349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752349 prefixEnd_4752349 := by exact prefixLift 4752349
  have htrace : WordTrace (prefixWord ++ tailWord_4752349) baseStart_4752349 baseEnd_4752349 := by
    simpa [prefixWord, tailWord_4752349, baseEnd_4752349] using wordTrace_append hprefix tailTrace_4752349
  have hstable : (prefixWord ++ tailWord_4752349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752349).length < 2 ^ (prefixWord ++ tailWord_4752349).sum := by decide
  have hdescent : baseEnd_4752349 < baseStart_4752349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752385 : List Nat := [1, 2, 4, 1, 2, 2, 1, 2, 1, 1, 6]
def baseStart_4752385 : Nat := 118140960795 + 4752385 * 2 ^ 59
def prefixEnd_4752385 : Nat := 4983230072969 + 3 ^ 40 * 4752385 * 2
def baseEnd_4752385 : Nat := 2440257760217494005531685

theorem tailTrace_4752385 : CollatzResearch.WordTrace tailWord_4752385 prefixEnd_4752385 2440257760217494005531685 := by
  unfold tailWord_4752385
  simp only [CollatzResearch.WordTrace]
  refine ⟨173333720887928262584930609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115555813925285508389953739 173333720887928262584930609)
  ·
    refine ⟨130000290665946196938697957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173333720887928262584930609 130000290665946196938697957)
    ·
      refine ⟨24375054499864911926005867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130000290665946196938697957 24375054499864911926005867)
      ·
        refine ⟨36562581749797367889008801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24375054499864911926005867 36562581749797367889008801)
        ·
          refine ⟨27421936312348025916756601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36562581749797367889008801 27421936312348025916756601)
          ·
            refine ⟨20566452234261019437567451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27421936312348025916756601 20566452234261019437567451)
            ·
              refine ⟨30849678351391529156351177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20566452234261019437567451 30849678351391529156351177)
              ·
                refine ⟨23137258763543646867263383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30849678351391529156351177 23137258763543646867263383)
                ·
                  refine ⟨34705888145315470300895075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23137258763543646867263383 34705888145315470300895075)
                  ·
                    refine ⟨52058832217973205451342613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34705888145315470300895075 52058832217973205451342613)
                    ·
                      refine ⟨2440257760217494005531685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52058832217973205451342613 2440257760217494005531685)
                      ·
                        rfl

theorem cell23_4752385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_4752385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752385 prefixEnd_4752385 := by exact prefixLift 4752385
  have htrace : WordTrace (prefixWord ++ tailWord_4752385) baseStart_4752385 baseEnd_4752385 := by
    simpa [prefixWord, tailWord_4752385, baseEnd_4752385] using wordTrace_append hprefix tailTrace_4752385
  have hstable : (prefixWord ++ tailWord_4752385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752385).length < 2 ^ (prefixWord ++ tailWord_4752385).sum := by decide
  have hdescent : baseEnd_4752385 < baseStart_4752385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752395 : List Nat := [1, 1, 1, 1, 6, 3, 2, 8]
def baseStart_4752395 : Nat := 118140960795 + 4752395 * 2 ^ 59
def prefixEnd_4752395 : Nat := 4983230072969 + 3 ^ 40 * 4752395 * 2
def baseEnd_4752395 : Nat := 90380107223112554311357

theorem tailTrace_4752395 : CollatzResearch.WordTrace tailWord_4752395 prefixEnd_4752395 90380107223112554311357 := by
  unfold tailWord_4752395
  simp only [CollatzResearch.WordTrace]
  refine ⟨173334085617892034292794639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115556057078594689528529759 173334085617892034292794639)
  ·
    refine ⟨260001128426838051439191959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173334085617892034292794639 260001128426838051439191959)
    ·
      refine ⟨390001692640257077158787939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260001128426838051439191959 390001692640257077158787939)
      ·
        refine ⟨585002538960385615738181909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390001692640257077158787939 585002538960385615738181909)
        ·
          refine ⟨27421994013768075737727277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 585002538960385615738181909 27421994013768075737727277)
          ·
            refine ⟨10283247755163028401647729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27421994013768075737727277 10283247755163028401647729)
            ·
              refine ⟨7712435816372271301235797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10283247755163028401647729 7712435816372271301235797)
              ·
                refine ⟨90380107223112554311357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7712435816372271301235797 90380107223112554311357)
                ·
                  rfl

theorem cell23_4752395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 8].length) (baseStart_4752395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752395 prefixEnd_4752395 := by exact prefixLift 4752395
  have htrace : WordTrace (prefixWord ++ tailWord_4752395) baseStart_4752395 baseEnd_4752395 := by
    simpa [prefixWord, tailWord_4752395, baseEnd_4752395] using wordTrace_append hprefix tailTrace_4752395
  have hstable : (prefixWord ++ tailWord_4752395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752395).length < 2 ^ (prefixWord ++ tailWord_4752395).sum := by decide
  have hdescent : baseEnd_4752395 < baseStart_4752395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752426 : List Nat := [3, 1, 4, 1, 4, 1, 1, 1, 1, 1, 5]
def baseStart_4752426 : Nat := 118140960795 + 4752426 * 2 ^ 59
def prefixEnd_4752426 : Nat := 4983230072969 + 3 ^ 40 * 4752426 * 2
def baseEnd_4752426 : Nat := 2440278812924328345118997

theorem tailTrace_4752426 : CollatzResearch.WordTrace tailWord_4752426 prefixEnd_4752426 2440278812924328345118997 := by
  unfold tailWord_4752426
  simp only [CollatzResearch.WordTrace]
  refine ⟨43333804070194931646793283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115556810853853151058115421 43333804070194931646793283)
  ·
    refine ⟨65000706105292397470189925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43333804070194931646793283 65000706105292397470189925)
    ·
      refine ⟨12187632394742324525660611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65000706105292397470189925 12187632394742324525660611)
      ·
        refine ⟨18281448592113486788490917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12187632394742324525660611 18281448592113486788490917)
        ·
          refine ⟨3427771611021278772842047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18281448592113486788490917 3427771611021278772842047)
          ·
            refine ⟨5141657416531918159263071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3427771611021278772842047 5141657416531918159263071)
            ·
              refine ⟨7712486124797877238894607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5141657416531918159263071 7712486124797877238894607)
              ·
                refine ⟨11568729187196815858341911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7712486124797877238894607 11568729187196815858341911)
                ·
                  refine ⟨17353093780795223787512867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11568729187196815858341911 17353093780795223787512867)
                  ·
                    refine ⟨26029640671192835681269301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17353093780795223787512867 26029640671192835681269301)
                    ·
                      refine ⟨2440278812924328345118997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26029640671192835681269301 2440278812924328345118997)
                      ·
                        rfl

theorem cell23_4752426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_4752426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752426 prefixEnd_4752426 := by exact prefixLift 4752426
  have htrace : WordTrace (prefixWord ++ tailWord_4752426) baseStart_4752426 baseEnd_4752426 := by
    simpa [prefixWord, tailWord_4752426, baseEnd_4752426] using wordTrace_append hprefix tailTrace_4752426
  have hstable : (prefixWord ++ tailWord_4752426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752426).length < 2 ^ (prefixWord ++ tailWord_4752426).sum := by decide
  have hdescent : baseEnd_4752426 < baseStart_4752426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752440 : List Nat := [2, 1, 2, 1, 5, 3, 2, 2, 1, 2, 2]
def baseStart_4752440 : Nat := 118140960795 + 4752440 * 2 ^ 59
def prefixEnd_4752440 : Nat := 4983230072969 + 3 ^ 40 * 4752440 * 2
def baseEnd_4752440 : Nat := 2440286001653491290343933

theorem tailTrace_4752440 : CollatzResearch.WordTrace tailWord_4752440 prefixEnd_4752440 2440286001653491290343933 := by
  unfold tailWord_4752440
  simp only [CollatzResearch.WordTrace]
  refine ⟨86667863451364503489091387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115557151268486004652121849 86667863451364503489091387)
  ·
    refine ⟨130001795177046755233637081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86667863451364503489091387 130001795177046755233637081)
    ·
      refine ⟨97501346382785066425227811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130001795177046755233637081 97501346382785066425227811)
      ·
        refine ⟨146252019574177599637841717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97501346382785066425227811 146252019574177599637841717)
        ·
          refine ⟨13711126835079149966047661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 146252019574177599637841717 13711126835079149966047661)
          ·
            refine ⟨5141672563154681237267873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13711126835079149966047661 5141672563154681237267873)
            ·
              refine ⟨3856254422366010927950905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5141672563154681237267873 3856254422366010927950905)
              ·
                refine ⟨2892190816774508195963179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3856254422366010927950905 2892190816774508195963179)
                ·
                  refine ⟨4338286225161762293944769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2892190816774508195963179 4338286225161762293944769)
                  ·
                    refine ⟨3253714668871321720458577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4338286225161762293944769 3253714668871321720458577)
                    ·
                      refine ⟨2440286001653491290343933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3253714668871321720458577 2440286001653491290343933)
                      ·
                        rfl

theorem cell23_4752440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 2, 1, 2, 2].length) (baseStart_4752440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752440 prefixEnd_4752440 := by exact prefixLift 4752440
  have htrace : WordTrace (prefixWord ++ tailWord_4752440) baseStart_4752440 baseEnd_4752440 := by
    simpa [prefixWord, tailWord_4752440, baseEnd_4752440] using wordTrace_append hprefix tailTrace_4752440
  have hstable : (prefixWord ++ tailWord_4752440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752440).length < 2 ^ (prefixWord ++ tailWord_4752440).sum := by decide
  have hdescent : baseEnd_4752440 < baseStart_4752440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752455 : List Nat := [1, 1, 4, 1, 3, 2, 1, 1, 1, 8]
def baseStart_4752455 : Nat := 118140960795 + 4752455 * 2 ^ 59
def prefixEnd_4752455 : Nat := 4983230072969 + 3 ^ 40 * 4752455 * 2
def baseEnd_4752455 : Nat := 813431234621102910552121

theorem tailTrace_4752455 : CollatzResearch.WordTrace tailWord_4752455 prefixEnd_4752455 813431234621102910552121 := by
  unfold tailWord_4752455
  simp only [CollatzResearch.WordTrace]
  refine ⟨173336273997674664539978819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115557515998449776359985879 173336273997674664539978819)
  ·
    refine ⟨260004410996511996809968229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173336273997674664539978819 260004410996511996809968229)
    ·
      refine ⟨48750827061845999401869043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 260004410996511996809968229 48750827061845999401869043)
      ·
        refine ⟨73126240592768999102803565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48750827061845999401869043 73126240592768999102803565)
        ·
          refine ⟨27422340222288374663551337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73126240592768999102803565 27422340222288374663551337)
          ·
            refine ⟨20566755166716280997663503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27422340222288374663551337 20566755166716280997663503)
            ·
              refine ⟨30850132750074421496495255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20566755166716280997663503 30850132750074421496495255)
              ·
                refine ⟨46275199125111632244742883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30850132750074421496495255 46275199125111632244742883)
                ·
                  refine ⟨69412798687667448367114325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46275199125111632244742883 69412798687667448367114325)
                  ·
                    refine ⟨813431234621102910552121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 69412798687667448367114325 813431234621102910552121)
                    ·
                      rfl

theorem cell23_4752455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_4752455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752455 prefixEnd_4752455 := by exact prefixLift 4752455
  have htrace : WordTrace (prefixWord ++ tailWord_4752455) baseStart_4752455 baseEnd_4752455 := by
    simpa [prefixWord, tailWord_4752455, baseEnd_4752455] using wordTrace_append hprefix tailTrace_4752455
  have hstable : (prefixWord ++ tailWord_4752455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752455).length < 2 ^ (prefixWord ++ tailWord_4752455).sum := by decide
  have hdescent : baseEnd_4752455 < baseStart_4752455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752465 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 4, 1, 5]
def baseStart_4752465 : Nat := 118140960795 + 4752465 * 2 ^ 59
def prefixEnd_4752465 : Nat := 4983230072969 + 3 ^ 40 * 4752465 * 2
def baseEnd_4752465 : Nat := 2440298838669853692531317

theorem tailTrace_4752465 : CollatzResearch.WordTrace tailWord_4752465 prefixEnd_4752465 2440298838669853692531317 := by
  unfold tailWord_4752465
  simp only [CollatzResearch.WordTrace]
  refine ⟨173336638727638436247842849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115557759151758957498561899 173336638727638436247842849)
  ·
    refine ⟨130002479045728827185882137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173336638727638436247842849 130002479045728827185882137)
    ·
      refine ⟨97501859284296620389411603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130002479045728827185882137 97501859284296620389411603)
      ·
        refine ⟨146252788926444930584117405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97501859284296620389411603 146252788926444930584117405)
        ·
          refine ⟨54844795847416848969044027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146252788926444930584117405 54844795847416848969044027)
          ·
            refine ⟨82267193771125273453566041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54844795847416848969044027 82267193771125273453566041)
            ·
              refine ⟨61700395328343955090174531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82267193771125273453566041 61700395328343955090174531)
              ·
                refine ⟨92550592992515932635261797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61700395328343955090174531 92550592992515932635261797)
                ·
                  refine ⟨17353236186096737369111587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92550592992515932635261797 17353236186096737369111587)
                  ·
                    refine ⟨26029854279145106053667381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17353236186096737369111587 26029854279145106053667381)
                    ·
                      refine ⟨2440298838669853692531317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26029854279145106053667381 2440298838669853692531317)
                      ·
                        rfl

theorem cell23_4752465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 1, 5].length) (baseStart_4752465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752465 prefixEnd_4752465 := by exact prefixLift 4752465
  have htrace : WordTrace (prefixWord ++ tailWord_4752465) baseStart_4752465 baseEnd_4752465 := by
    simpa [prefixWord, tailWord_4752465, baseEnd_4752465] using wordTrace_append hprefix tailTrace_4752465
  have hstable : (prefixWord ++ tailWord_4752465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752465).length < 2 ^ (prefixWord ++ tailWord_4752465).sum := by decide
  have hdescent : baseEnd_4752465 < baseStart_4752465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752479 : List Nat := [1, 1, 2, 3, 1, 1, 4, 2, 4, 2, 2]
def baseStart_4752479 : Nat := 118140960795 + 4752479 * 2 ^ 59
def prefixEnd_4752479 : Nat := 4983230072969 + 3 ^ 40 * 4752479 * 2
def baseEnd_4752479 : Nat := 2440306027399016637756253

theorem tailTrace_4752479 : CollatzResearch.WordTrace tailWord_4752479 prefixEnd_4752479 2440306027399016637756253 := by
  unfold tailWord_4752479
  simp only [CollatzResearch.WordTrace]
  refine ⟨173337149349587716638852491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115558099566391811092568327 173337149349587716638852491)
  ·
    refine ⟨260005724024381574958278737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173337149349587716638852491 260005724024381574958278737)
    ·
      refine ⟨195004293018286181218709053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260005724024381574958278737 195004293018286181218709053)
      ·
        refine ⟨73126609881857317957015895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195004293018286181218709053 73126609881857317957015895)
        ·
          refine ⟨109689914822785976935523843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73126609881857317957015895 109689914822785976935523843)
          ·
            refine ⟨164534872234178965403285765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109689914822785976935523843 164534872234178965403285765)
            ·
              refine ⟨30850288543908556013116081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 164534872234178965403285765 30850288543908556013116081)
              ·
                refine ⟨23137716407931417009837061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30850288543908556013116081 23137716407931417009837061)
                ·
                  refine ⟨4338321826487140689344449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23137716407931417009837061 4338321826487140689344449)
                  ·
                    refine ⟨3253741369865355517008337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4338321826487140689344449 3253741369865355517008337)
                    ·
                      refine ⟨2440306027399016637756253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3253741369865355517008337 2440306027399016637756253)
                      ·
                        rfl

theorem cell23_4752479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 4, 2, 2].length) (baseStart_4752479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752479 prefixEnd_4752479 := by exact prefixLift 4752479
  have htrace : WordTrace (prefixWord ++ tailWord_4752479) baseStart_4752479 baseEnd_4752479 := by
    simpa [prefixWord, tailWord_4752479, baseEnd_4752479] using wordTrace_append hprefix tailTrace_4752479
  have hstable : (prefixWord ++ tailWord_4752479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752479).length < 2 ^ (prefixWord ++ tailWord_4752479).sum := by decide
  have hdescent : baseEnd_4752479 < baseStart_4752479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752485 : List Nat := [1, 3, 1, 3, 2, 1, 1, 2, 9]
def baseStart_4752485 : Nat := 118140960795 + 4752485 * 2 ^ 59
def prefixEnd_4752485 : Nat := 4983230072969 + 3 ^ 40 * 4752485 * 2
def baseEnd_4752485 : Nat := 271145456475882623809025

theorem tailTrace_4752485 : CollatzResearch.WordTrace tailWord_4752485 prefixEnd_4752485 271145456475882623809025 := by
  unfold tailWord_4752485
  simp only [CollatzResearch.WordTrace]
  refine ⟨173337368187565979663570909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115558245458377319775713939 173337368187565979663570909)
  ·
    refine ⟨65001513070337242373839091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173337368187565979663570909 65001513070337242373839091)
    ·
      refine ⟨97502269605505863560758637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65001513070337242373839091 97502269605505863560758637)
      ·
        refine ⟨36563351102064698835284489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97502269605505863560758637 36563351102064698835284489)
        ·
          refine ⟨27422513326548524126463367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36563351102064698835284489 27422513326548524126463367)
          ·
            refine ⟨41133769989822786189695051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27422513326548524126463367 41133769989822786189695051)
            ·
              refine ⟨61700654984734179284542577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41133769989822786189695051 61700654984734179284542577)
              ·
                refine ⟨46275491238550634463406933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61700654984734179284542577 46275491238550634463406933)
                ·
                  refine ⟨271145456475882623809025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 46275491238550634463406933 271145456475882623809025)
                  ·
                    rfl

theorem cell23_4752485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 9].length) (baseStart_4752485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752485 prefixEnd_4752485 := by exact prefixLift 4752485
  have htrace : WordTrace (prefixWord ++ tailWord_4752485) baseStart_4752485 baseEnd_4752485 := by
    simpa [prefixWord, tailWord_4752485, baseEnd_4752485] using wordTrace_append hprefix tailTrace_4752485
  have hstable : (prefixWord ++ tailWord_4752485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752485).length < 2 ^ (prefixWord ++ tailWord_4752485).sum := by decide
  have hdescent : baseEnd_4752485 < baseStart_4752485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752512 : List Nat := [2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 3]
def baseStart_4752512 : Nat := 118140960795 + 4752512 * 2 ^ 59
def prefixEnd_4752512 : Nat := 4983230072969 + 3 ^ 40 * 4752512 * 2
def baseEnd_4752512 : Nat := 2440322972260615008643601

theorem tailTrace_4752512 : CollatzResearch.WordTrace tailWord_4752512 prefixEnd_4752512 2440322972260615008643601 := by
  unfold tailWord_4752512
  simp only [CollatzResearch.WordTrace]
  refine ⟨86669176479234081637401895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115558901972312108849869193 86669176479234081637401895)
  ·
    refine ⟨130003764718851122456102843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86669176479234081637401895 130003764718851122456102843)
    ·
      refine ⟨195005647078276683684154265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130003764718851122456102843 195005647078276683684154265)
      ·
        refine ⟨146254235308707512763115699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195005647078276683684154265 146254235308707512763115699)
        ·
          refine ⟨219381352963061269144673549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146254235308707512763115699 219381352963061269144673549)
          ·
            refine ⟨82268007361147975929252581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 219381352963061269144673549 82268007361147975929252581)
            ·
              refine ⟨15425251380215245486734859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82268007361147975929252581 15425251380215245486734859)
              ·
                refine ⟨23137877070322868230102289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15425251380215245486734859 23137877070322868230102289)
                ·
                  refine ⟨17353407802742151172576717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23137877070322868230102289 17353407802742151172576717)
                  ·
                    refine ⟨6507527926028306689716269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17353407802742151172576717 6507527926028306689716269)
                    ·
                      refine ⟨2440322972260615008643601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6507527926028306689716269 2440322972260615008643601)
                      ·
                        rfl

theorem cell23_4752512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 3].length) (baseStart_4752512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752512 prefixEnd_4752512 := by exact prefixLift 4752512
  have htrace : WordTrace (prefixWord ++ tailWord_4752512) baseStart_4752512 baseEnd_4752512 := by
    simpa [prefixWord, tailWord_4752512, baseEnd_4752512] using wordTrace_append hprefix tailTrace_4752512
  have hstable : (prefixWord ++ tailWord_4752512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752512).length < 2 ^ (prefixWord ++ tailWord_4752512).sum := by decide
  have hdescent : baseEnd_4752512 < baseStart_4752512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752515 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 3, 7]
def baseStart_4752515 : Nat := 118140960795 + 4752515 * 2 ^ 59
def prefixEnd_4752515 : Nat := 4983230072969 + 3 ^ 40 * 4752515 * 2
def baseEnd_4752515 : Nat := 813441504234192832302029

theorem tailTrace_4752515 : CollatzResearch.WordTrace tailWord_4752515 prefixEnd_4752515 813441504234192832302029 := by
  unfold tailWord_4752515
  simp only [CollatzResearch.WordTrace]
  refine ⟨173338462377457294787162999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115558974918304863191441999 173338462377457294787162999)
  ·
    refine ⟨260007693566185942180744499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173338462377457294787162999 260007693566185942180744499)
    ·
      refine ⟨390011540349278913271116749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260007693566185942180744499 390011540349278913271116749)
      ·
        refine ⟨146254327630979592476668781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 390011540349278913271116749 146254327630979592476668781)
        ·
          refine ⟨54845372861617347178750793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146254327630979592476668781 54845372861617347178750793)
          ·
            refine ⟨41134029646213010384063095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54845372861617347178750793 41134029646213010384063095)
            ·
              refine ⟨61701044469319515576094643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41134029646213010384063095 61701044469319515576094643)
              ·
                refine ⟨92551566703979273364141965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61701044469319515576094643 92551566703979273364141965)
                ·
                  refine ⟨34706837513992227511553237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92551566703979273364141965 34706837513992227511553237)
                  ·
                    refine ⟨813441504234192832302029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34706837513992227511553237 813441504234192832302029)
                    ·
                      rfl

theorem cell23_4752515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 7].length) (baseStart_4752515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752515 prefixEnd_4752515 := by exact prefixLift 4752515
  have htrace : WordTrace (prefixWord ++ tailWord_4752515) baseStart_4752515 baseEnd_4752515 := by
    simpa [prefixWord, tailWord_4752515, baseEnd_4752515] using wordTrace_append hprefix tailTrace_4752515
  have hstable : (prefixWord ++ tailWord_4752515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752515).length < 2 ^ (prefixWord ++ tailWord_4752515).sum := by decide
  have hdescent : baseEnd_4752515 < baseStart_4752515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752536 : List Nat := [2, 1, 2, 4, 2, 3, 1, 3, 5]
def baseStart_4752536 : Nat := 118140960795 + 4752536 * 2 ^ 59
def prefixEnd_4752536 : Nat := 4983230072969 + 3 ^ 40 * 4752536 * 2
def baseEnd_4752536 : Nat := 271148366199591434971499

theorem tailTrace_4752536 : CollatzResearch.WordTrace tailWord_4752536 prefixEnd_4752536 271148366199591434971499 := by
  unfold tailWord_4752536
  simp only [CollatzResearch.WordTrace]
  refine ⟨86669614155190607686838731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115559485540254143582451641 86669614155190607686838731)
  ·
    refine ⟨130004421232785911530258097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86669614155190607686838731 130004421232785911530258097)
    ·
      refine ⟨97503315924589433647693573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130004421232785911530258097 97503315924589433647693573)
      ·
        refine ⟨18281871735860518808942545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97503315924589433647693573 18281871735860518808942545)
        ·
          refine ⟨13711403801895389106706909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18281871735860518808942545 13711403801895389106706909)
          ·
            refine ⟨5141776425710770915015091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13711403801895389106706909 5141776425710770915015091)
            ·
              refine ⟨7712664638566156372522637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5141776425710770915015091 7712664638566156372522637)
              ·
                refine ⟨2892249239462308639695989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7712664638566156372522637 2892249239462308639695989)
                ·
                  refine ⟨271148366199591434971499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2892249239462308639695989 271148366199591434971499)
                  ·
                    rfl

theorem cell23_4752536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 3, 5].length) (baseStart_4752536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752536 prefixEnd_4752536 := by exact prefixLift 4752536
  have htrace : WordTrace (prefixWord ++ tailWord_4752536) baseStart_4752536 baseEnd_4752536 := by
    simpa [prefixWord, tailWord_4752536, baseEnd_4752536] using wordTrace_append hprefix tailTrace_4752536
  have hstable : (prefixWord ++ tailWord_4752536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752536).length < 2 ^ (prefixWord ++ tailWord_4752536).sum := by decide
  have hdescent : baseEnd_4752536 < baseStart_4752536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752609 : List Nat := [1, 2, 3, 1, 3, 3, 2, 2, 6]
def baseStart_4752609 : Nat := 118140960795 + 4752609 * 2 ^ 59
def prefixEnd_4752609 : Nat := 4983230072969 + 3 ^ 40 * 4752609 * 2
def baseEnd_4752609 : Nat := 271152531098233458792295

theorem tailTrace_4752609 : CollatzResearch.WordTrace tailWord_4752609 prefixEnd_4752609 271152531098233458792295 := by
  unfold tailWord_4752609
  simp only [CollatzResearch.WordTrace]
  refine ⟨173341890839116748841084881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115561260559411165894056587 173341890839116748841084881)
  ·
    refine ⟨130006418129337561630813661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173341890839116748841084881 130006418129337561630813661)
    ·
      refine ⟨48752406798501585611555123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130006418129337561630813661 48752406798501585611555123)
      ·
        refine ⟨73128610197752378417332685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48752406798501585611555123 73128610197752378417332685)
        ·
          refine ⟨27423228824157141906499757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73128610197752378417332685 27423228824157141906499757)
          ·
            refine ⟨10283710809058928214937409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27423228824157141906499757 10283710809058928214937409)
            ·
              refine ⟨7712783106794196161203057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10283710809058928214937409 7712783106794196161203057)
              ·
                refine ⟨5784587330095647120902293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7712783106794196161203057 5784587330095647120902293)
                ·
                  refine ⟨271152531098233458792295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5784587330095647120902293 271152531098233458792295)
                  ·
                    rfl

theorem cell23_4752609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2, 6].length) (baseStart_4752609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752609 prefixEnd_4752609 := by exact prefixLift 4752609
  have htrace : WordTrace (prefixWord ++ tailWord_4752609) baseStart_4752609 baseEnd_4752609 := by
    simpa [prefixWord, tailWord_4752609, baseEnd_4752609] using wordTrace_append hprefix tailTrace_4752609
  have hstable : (prefixWord ++ tailWord_4752609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752609).length < 2 ^ (prefixWord ++ tailWord_4752609).sum := by decide
  have hdescent : baseEnd_4752609 < baseStart_4752609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752613 : List Nat := [1, 3, 1, 4, 3, 1, 1, 4, 1, 4]
def baseStart_4752613 : Nat := 118140960795 + 4752613 * 2 ^ 59
def prefixEnd_4752613 : Nat := 4983230072969 + 3 ^ 40 * 4752613 * 2
def baseEnd_4752613 : Nat := 813458277935573037826879

theorem tailTrace_4752613 : CollatzResearch.WordTrace tailWord_4752613 prefixEnd_4752613 813458277935573037826879 := by
  unfold tailWord_4752613
  simp only [CollatzResearch.WordTrace]
  refine ⟨173342036731102257524230493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115561357820734838349486995 173342036731102257524230493)
  ·
    refine ⟨65003263774163346571586435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173342036731102257524230493 65003263774163346571586435)
    ·
      refine ⟨97504895661245019857379653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65003263774163346571586435 97504895661245019857379653)
      ·
        refine ⟨18282167936483441223258685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97504895661245019857379653 18282167936483441223258685)
        ·
          refine ⟨6855812976181290458722007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18282167936483441223258685 6855812976181290458722007)
          ·
            refine ⟨10283719464271935688083011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6855812976181290458722007 10283719464271935688083011)
            ·
              refine ⟨15425579196407903532124517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10283719464271935688083011 15425579196407903532124517)
              ·
                refine ⟨2892296099326481912273347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15425579196407903532124517 2892296099326481912273347)
                ·
                  refine ⟨4338444148989722868410021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2892296099326481912273347 4338444148989722868410021)
                  ·
                    refine ⟨813458277935573037826879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4338444148989722868410021 813458277935573037826879)
                    ·
                      rfl

theorem cell23_4752613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 4, 1, 4].length) (baseStart_4752613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752613 prefixEnd_4752613 := by exact prefixLift 4752613
  have htrace : WordTrace (prefixWord ++ tailWord_4752613) baseStart_4752613 baseEnd_4752613 := by
    simpa [prefixWord, tailWord_4752613, baseEnd_4752613] using wordTrace_append hprefix tailTrace_4752613
  have hstable : (prefixWord ++ tailWord_4752613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752613).length < 2 ^ (prefixWord ++ tailWord_4752613).sum := by decide
  have hdescent : baseEnd_4752613 < baseStart_4752613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752689 : List Nat := [1, 2, 2, 3, 3, 2, 1, 1, 1, 1, 6]
def baseStart_4752689 : Nat := 118140960795 + 4752689 * 2 ^ 59
def prefixEnd_4752689 : Nat := 4983230072969 + 3 ^ 40 * 4752689 * 2
def baseEnd_4752689 : Nat := 2440413858336460816130287

theorem tailTrace_4752689 : CollatzResearch.WordTrace tailWord_4752689 prefixEnd_4752689 2440413858336460816130287 := by
  unfold tailWord_4752689
  simp only [CollatzResearch.WordTrace]
  refine ⟨173344808678826922503997121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115563205785884615002664747 173344808678826922503997121)
  ·
    refine ⟨130008606509120191877997841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173344808678826922503997121 130008606509120191877997841)
    ·
      refine ⟨97506454881840143908498381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130008606509120191877997841 97506454881840143908498381)
      ·
        refine ⟨36564920580690053965686893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97506454881840143908498381 36564920580690053965686893)
        ·
          refine ⟨13711845217758770237132585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36564920580690053965686893 13711845217758770237132585)
          ·
            refine ⟨10283883913319077677849439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13711845217758770237132585 10283883913319077677849439)
            ·
              refine ⟨15425825869978616516774159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10283883913319077677849439 15425825869978616516774159)
              ·
                refine ⟨23138738804967924775161239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15425825869978616516774159 23138738804967924775161239)
                ·
                  refine ⟨34708108207451887162741859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23138738804967924775161239 34708108207451887162741859)
                  ·
                    refine ⟨52062162311177830744112789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34708108207451887162741859 52062162311177830744112789)
                    ·
                      refine ⟨2440413858336460816130287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52062162311177830744112789 2440413858336460816130287)
                      ·
                        rfl

theorem cell23_4752689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_4752689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752689 prefixEnd_4752689 := by exact prefixLift 4752689
  have htrace : WordTrace (prefixWord ++ tailWord_4752689) baseStart_4752689 baseEnd_4752689 := by
    simpa [prefixWord, tailWord_4752689, baseEnd_4752689] using wordTrace_append hprefix tailTrace_4752689
  have hstable : (prefixWord ++ tailWord_4752689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752689).length < 2 ^ (prefixWord ++ tailWord_4752689).sum := by decide
  have hdescent : baseEnd_4752689 < baseStart_4752689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752693 : List Nat := [1, 3, 3, 1, 2, 2, 2, 2, 3, 2, 2]
def baseStart_4752693 : Nat := 118140960795 + 4752693 * 2 ^ 59
def prefixEnd_4752693 : Nat := 4983230072969 + 3 ^ 40 * 4752693 * 2
def baseEnd_4752693 : Nat := 2440415912259078800480269

theorem tailTrace_4752693 : CollatzResearch.WordTrace tailWord_4752693 prefixEnd_4752693 2440415912259078800480269 := by
  unfold tailWord_4752693
  simp only [CollatzResearch.WordTrace]
  refine ⟨173344954570812431187142733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115563303047208287458095155 173344954570812431187142733)
  ·
    refine ⟨65004357964054661695178525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173344954570812431187142733 65004357964054661695178525)
    ·
      refine ⟨24376634236520498135691947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65004357964054661695178525 24376634236520498135691947)
      ·
        refine ⟨36564951354780747203537921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24376634236520498135691947 36564951354780747203537921)
        ·
          refine ⟨27423713516085560402653441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36564951354780747203537921 27423713516085560402653441)
          ·
            refine ⟨20567785137064170301990081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27423713516085560402653441 20567785137064170301990081)
            ·
              refine ⟨15425838852798127726492561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20567785137064170301990081 15425838852798127726492561)
              ·
                refine ⟨11569379139598595794869421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15425838852798127726492561 11569379139598595794869421)
                ·
                  refine ⟨4338517177349473423076033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11569379139598595794869421 4338517177349473423076033)
                  ·
                    refine ⟨3253887883012105067307025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4338517177349473423076033 3253887883012105067307025)
                    ·
                      refine ⟨2440415912259078800480269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3253887883012105067307025 2440415912259078800480269)
                      ·
                        rfl

theorem cell23_4752693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 3, 2, 2].length) (baseStart_4752693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752693 prefixEnd_4752693 := by exact prefixLift 4752693
  have htrace : WordTrace (prefixWord ++ tailWord_4752693) baseStart_4752693 baseEnd_4752693 := by
    simpa [prefixWord, tailWord_4752693, baseEnd_4752693] using wordTrace_append hprefix tailTrace_4752693
  have hstable : (prefixWord ++ tailWord_4752693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752693).length < 2 ^ (prefixWord ++ tailWord_4752693).sum := by decide
  have hdescent : baseEnd_4752693 < baseStart_4752693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752709 : List Nat := [1, 3, 1, 1, 1, 2, 1, 6, 1, 3, 3]
def baseStart_4752709 : Nat := 118140960795 + 4752709 * 2 ^ 59
def prefixEnd_4752709 : Nat := 4983230072969 + 3 ^ 40 * 4752709 * 2
def baseEnd_4752709 : Nat := 2440424127949550737880195

theorem tailTrace_4752709 : CollatzResearch.WordTrace tailWord_4752709 prefixEnd_4752709 2440424127949550737880195 := by
  unfold tailWord_4752709
  simp only [CollatzResearch.WordTrace]
  refine ⟨173345538138754465919725181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115563692092502977279816787 173345538138754465919725181)
  ·
    refine ⟨65004576802032924719896943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173345538138754465919725181 65004576802032924719896943)
    ·
      refine ⟨97506865203049387079845415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65004576802032924719896943 97506865203049387079845415)
      ·
        refine ⟨146260297804574080619768123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97506865203049387079845415 146260297804574080619768123)
        ·
          refine ⟨219390446706861120929652185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146260297804574080619768123 219390446706861120929652185)
          ·
            refine ⟨164542835030145840697239139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219390446706861120929652185 164542835030145840697239139)
            ·
              refine ⟨246814252545218761045858709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164542835030145840697239139 246814252545218761045858709)
              ·
                refine ⟨11569418088057129424024627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 246814252545218761045858709 11569418088057129424024627)
                ·
                  refine ⟨17354127132085694136036941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11569418088057129424024627 17354127132085694136036941)
                  ·
                    refine ⟨6507797674532135301013853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17354127132085694136036941 6507797674532135301013853)
                    ·
                      refine ⟨2440424127949550737880195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6507797674532135301013853 2440424127949550737880195)
                      ·
                        rfl

theorem cell23_4752709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 3, 3].length) (baseStart_4752709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752709 prefixEnd_4752709 := by exact prefixLift 4752709
  have htrace : WordTrace (prefixWord ++ tailWord_4752709) baseStart_4752709 baseEnd_4752709 := by
    simpa [prefixWord, tailWord_4752709, baseEnd_4752709] using wordTrace_append hprefix tailTrace_4752709
  have hstable : (prefixWord ++ tailWord_4752709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752709).length < 2 ^ (prefixWord ++ tailWord_4752709).sum := by decide
  have hdescent : baseEnd_4752709 < baseStart_4752709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752712 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 1, 9]
def baseStart_4752712 : Nat := 118140960795 + 4752712 * 2 ^ 59
def prefixEnd_4752712 : Nat := 4983230072969 + 3 ^ 40 * 4752712 * 2
def baseEnd_4752712 : Nat := 813475222797171408714227

theorem tailTrace_4752712 : CollatzResearch.WordTrace tailWord_4752712 prefixEnd_4752712 813475222797171408714227 := by
  unfold tailWord_4752712
  simp only [CollatzResearch.WordTrace]
  refine ⟨86672823778871798716042195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115563765038495731621389593 86672823778871798716042195)
  ·
    refine ⟨130009235668307698074063293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86672823778871798716042195 130009235668307698074063293)
    ·
      refine ⟨48753463375615386777773735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130009235668307698074063293 48753463375615386777773735)
      ·
        refine ⟨73130195063423080166660603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48753463375615386777773735 73130195063423080166660603)
        ·
          refine ⟨109695292595134620249990905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73130195063423080166660603 109695292595134620249990905)
          ·
            refine ⟨82271469446350965187493179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109695292595134620249990905 82271469446350965187493179)
            ·
              refine ⟨123407204169526447781239769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82271469446350965187493179 123407204169526447781239769)
              ·
                refine ⟨92555403127144835835929827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123407204169526447781239769 92555403127144835835929827)
                ·
                  refine ⟨138833104690717253753894741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92555403127144835835929827 138833104690717253753894741)
                  ·
                    refine ⟨813475222797171408714227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 138833104690717253753894741 813475222797171408714227)
                    ·
                      rfl

theorem cell23_4752712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_4752712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752712 prefixEnd_4752712 := by exact prefixLift 4752712
  have htrace : WordTrace (prefixWord ++ tailWord_4752712) baseStart_4752712 baseEnd_4752712 := by
    simpa [prefixWord, tailWord_4752712, baseEnd_4752712] using wordTrace_append hprefix tailTrace_4752712
  have hstable : (prefixWord ++ tailWord_4752712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752712).length < 2 ^ (prefixWord ++ tailWord_4752712).sum := by decide
  have hdescent : baseEnd_4752712 < baseStart_4752712 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752719 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 1, 9, 2]
def baseStart_4752719 : Nat := 118140960795 + 4752719 * 2 ^ 59
def prefixEnd_4752719 : Nat := 4983230072969 + 3 ^ 40 * 4752719 * 2
def baseEnd_4752719 : Nat := 2440429262756095698755149

theorem tailTrace_4752719 : CollatzResearch.WordTrace tailWord_4752719 prefixEnd_4752719 2440429262756095698755149 := by
  unfold tailWord_4752719
  simp only [CollatzResearch.WordTrace]
  refine ⟨173345902868718237627589211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115563935245812158418392807 173345902868718237627589211)
  ·
    refine ⟨260018854303077356441383817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173345902868718237627589211 260018854303077356441383817)
    ·
      refine ⟨195014140727308017331037863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260018854303077356441383817 195014140727308017331037863)
      ·
        refine ⟨292521211090962025996556795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195014140727308017331037863 292521211090962025996556795)
        ·
          refine ⟨438781816636443038994835193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292521211090962025996556795 438781816636443038994835193)
          ·
            refine ⟨329086362477332279246126395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 438781816636443038994835193 329086362477332279246126395)
            ·
              refine ⟨493629543715998418869189593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 329086362477332279246126395 493629543715998418869189593)
              ·
                refine ⟨370222157786998814151892195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 493629543715998418869189593 370222157786998814151892195)
                ·
                  refine ⟨555333236680498221227838293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 370222157786998814151892195 555333236680498221227838293)
                  ·
                    refine ⟨3253905683674794265006865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 555333236680498221227838293 3253905683674794265006865)
                    ·
                      refine ⟨2440429262756095698755149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3253905683674794265006865 2440429262756095698755149)
                      ·
                        rfl

theorem cell23_4752719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 9, 2].length) (baseStart_4752719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752719 prefixEnd_4752719 := by exact prefixLift 4752719
  have htrace : WordTrace (prefixWord ++ tailWord_4752719) baseStart_4752719 baseEnd_4752719 := by
    simpa [prefixWord, tailWord_4752719, baseEnd_4752719] using wordTrace_append hprefix tailTrace_4752719
  have hstable : (prefixWord ++ tailWord_4752719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752719).length < 2 ^ (prefixWord ++ tailWord_4752719).sum := by decide
  have hdescent : baseEnd_4752719 < baseStart_4752719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752727 : List Nat := [1, 1, 3, 2, 3, 3, 3, 2, 1, 2, 2]
def baseStart_4752727 : Nat := 118140960795 + 4752727 * 2 ^ 59
def prefixEnd_4752727 : Nat := 4983230072969 + 3 ^ 40 * 4752727 * 2
def baseEnd_4752727 : Nat := 2440433370601331667455113

theorem tailTrace_4752727 : CollatzResearch.WordTrace tailWord_4752727 prefixEnd_4752727 2440433370601331667455113 := by
  unfold tailWord_4752727
  simp only [CollatzResearch.WordTrace]
  refine ⟨173346194652689254993880435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115564129768459503329253623 173346194652689254993880435)
  ·
    refine ⟨260019291979033882490820653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173346194652689254993880435 260019291979033882490820653)
    ·
      refine ⟨97507234492137705934057745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 260019291979033882490820653 97507234492137705934057745)
      ·
        refine ⟨73130425869103279450543309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97507234492137705934057745 73130425869103279450543309)
        ·
          refine ⟨27423909700913729793953741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73130425869103279450543309 27423909700913729793953741)
          ·
            refine ⟨10283966137842648672732653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27423909700913729793953741 10283966137842648672732653)
            ·
              refine ⟨3856487301690993252274745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10283966137842648672732653 3856487301690993252274745)
              ·
                refine ⟨2892365476268244939206059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3856487301690993252274745 2892365476268244939206059)
                ·
                  refine ⟨4338548214402367408809089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2892365476268244939206059 4338548214402367408809089)
                  ·
                    refine ⟨3253911160801775556606817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4338548214402367408809089 3253911160801775556606817)
                    ·
                      refine ⟨2440433370601331667455113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3253911160801775556606817 2440433370601331667455113)
                      ·
                        rfl

theorem cell23_4752727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 2, 1, 2, 2].length) (baseStart_4752727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752727 prefixEnd_4752727 := by exact prefixLift 4752727
  have htrace : WordTrace (prefixWord ++ tailWord_4752727) baseStart_4752727 baseEnd_4752727 := by
    simpa [prefixWord, tailWord_4752727, baseEnd_4752727] using wordTrace_append hprefix tailTrace_4752727
  have hstable : (prefixWord ++ tailWord_4752727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752727).length < 2 ^ (prefixWord ++ tailWord_4752727).sum := by decide
  have hdescent : baseEnd_4752727 < baseStart_4752727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752753 : List Nat := [1, 2, 2, 2, 1, 2, 5, 2, 1, 3, 2]
def baseStart_4752753 : Nat := 118140960795 + 4752753 * 2 ^ 59
def prefixEnd_4752753 : Nat := 4983230072969 + 3 ^ 40 * 4752753 * 2
def baseEnd_4752753 : Nat := 2440446721098348565729993

theorem tailTrace_4752753 : CollatzResearch.WordTrace tailWord_4752753 prefixEnd_4752753 2440446721098348565729993 := by
  unfold tailWord_4752753
  simp only [CollatzResearch.WordTrace]
  refine ⟨173347142950595061434326913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115564761967063374289551275 173347142950595061434326913)
  ·
    refine ⟨130010357212946296075745185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173347142950595061434326913 130010357212946296075745185)
    ·
      refine ⟨97507767909709722056808889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130010357212946296075745185 97507767909709722056808889)
      ·
        refine ⟨73130825932282291542606667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97507767909709722056808889 73130825932282291542606667)
        ·
          refine ⟨109696238898423437313910001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73130825932282291542606667 109696238898423437313910001)
          ·
            refine ⟨82272179173817577985432501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109696238898423437313910001 82272179173817577985432501)
            ·
              refine ⟨7713016797545397936134297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82272179173817577985432501 7713016797545397936134297)
              ·
                refine ⟨5784762598159048452100723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7713016797545397936134297 5784762598159048452100723)
                ·
                  refine ⟨8677143897238572678151085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5784762598159048452100723 8677143897238572678151085)
                  ·
                    refine ⟨3253928961464464754306657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8677143897238572678151085 3253928961464464754306657)
                    ·
                      refine ⟨2440446721098348565729993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3253928961464464754306657 2440446721098348565729993)
                      ·
                        rfl

theorem cell23_4752753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2, 1, 3, 2].length) (baseStart_4752753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752753 prefixEnd_4752753 := by exact prefixLift 4752753
  have htrace : WordTrace (prefixWord ++ tailWord_4752753) baseStart_4752753 baseEnd_4752753 := by
    simpa [prefixWord, tailWord_4752753, baseEnd_4752753] using wordTrace_append hprefix tailTrace_4752753
  have hstable : (prefixWord ++ tailWord_4752753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752753).length < 2 ^ (prefixWord ++ tailWord_4752753).sum := by decide
  have hdescent : baseEnd_4752753 < baseStart_4752753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752779 : List Nat := [1, 1, 1, 1, 4, 3, 2, 2, 2, 2, 4]
def baseStart_4752779 : Nat := 118140960795 + 4752779 * 2 ^ 59
def prefixEnd_4752779 : Nat := 4983230072969 + 3 ^ 40 * 4752779 * 2
def baseEnd_4752779 : Nat := 2440460071595365464004873

theorem tailTrace_4752779 : CollatzResearch.WordTrace tailWord_4752779 prefixEnd_4752779 2440460071595365464004873 := by
  unfold tailWord_4752779
  simp only [CollatzResearch.WordTrace]
  refine ⟨173348091248500867874773391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115565394165667245249848927 173348091248500867874773391)
  ·
    refine ⟨260022136872751301812160087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173348091248500867874773391 260022136872751301812160087)
    ·
      refine ⟨390033205309126952718240131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260022136872751301812160087 390033205309126952718240131)
      ·
        refine ⟨585049807963690429077360197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390033205309126952718240131 585049807963690429077360197)
        ·
          refine ⟨109696838993191955452005037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 585049807963690429077360197 109696838993191955452005037)
          ·
            refine ⟨41136314622446983294501889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109696838993191955452005037 41136314622446983294501889)
            ·
              refine ⟨30852235966835237470876417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41136314622446983294501889 30852235966835237470876417)
              ·
                refine ⟨23139176975126428103157313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30852235966835237470876417 23139176975126428103157313)
                ·
                  refine ⟨17354382731344821077367985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23139176975126428103157313 17354382731344821077367985)
                  ·
                    refine ⟨13015787048508615808025989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17354382731344821077367985 13015787048508615808025989)
                    ·
                      refine ⟨2440460071595365464004873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13015787048508615808025989 2440460071595365464004873)
                      ·
                        rfl

theorem cell23_4752779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2, 4].length) (baseStart_4752779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752779 prefixEnd_4752779 := by exact prefixLift 4752779
  have htrace : WordTrace (prefixWord ++ tailWord_4752779) baseStart_4752779 baseEnd_4752779 := by
    simpa [prefixWord, tailWord_4752779, baseEnd_4752779] using wordTrace_append hprefix tailTrace_4752779
  have hstable : (prefixWord ++ tailWord_4752779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752779).length < 2 ^ (prefixWord ++ tailWord_4752779).sum := by decide
  have hdescent : baseEnd_4752779 < baseStart_4752779 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752879 : List Nat := [1, 1, 2, 1, 4, 1, 3, 2, 8]
def baseStart_4752879 : Nat := 118140960795 + 4752879 * 2 ^ 59
def prefixEnd_4752879 : Nat := 4983230072969 + 3 ^ 40 * 4752879 * 2
def baseEnd_4752879 : Nat := 271167935517868341417157

theorem tailTrace_4752879 : CollatzResearch.WordTrace tailWord_4752879 prefixEnd_4752879 271167935517868341417157 := by
  unfold tailWord_4752879
  simp only [CollatzResearch.WordTrace]
  refine ⟨173351738548138584953413691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115567825698759056635609127 173351738548138584953413691)
  ·
    refine ⟨260027607822207877430120537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173351738548138584953413691 260027607822207877430120537)
    ·
      refine ⟨195020705866655908072590403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260027607822207877430120537 195020705866655908072590403)
      ·
        refine ⟨292531058799983862108885605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195020705866655908072590403 292531058799983862108885605)
        ·
          refine ⟨54849573524996974145416051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 292531058799983862108885605 54849573524996974145416051)
          ·
            refine ⟨82274360287495461218124077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54849573524996974145416051 82274360287495461218124077)
            ·
              refine ⟨30852885107810797956796529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82274360287495461218124077 30852885107810797956796529)
              ·
                refine ⟨23139663830858098467597397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30852885107810797956796529 23139663830858098467597397)
                ·
                  refine ⟨271167935517868341417157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23139663830858098467597397 271167935517868341417157)
                  ·
                    rfl

theorem cell23_4752879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 8].length) (baseStart_4752879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752879 prefixEnd_4752879 := by exact prefixLift 4752879
  have htrace : WordTrace (prefixWord ++ tailWord_4752879) baseStart_4752879 baseEnd_4752879 := by
    simpa [prefixWord, tailWord_4752879, baseEnd_4752879] using wordTrace_append hprefix tailTrace_4752879
  have hstable : (prefixWord ++ tailWord_4752879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752879).length < 2 ^ (prefixWord ++ tailWord_4752879).sum := by decide
  have hdescent : baseEnd_4752879 < baseStart_4752879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752883 : List Nat := [1, 1, 1, 2, 2, 2, 2, 7, 1, 4]
def baseStart_4752883 : Nat := 118140960795 + 4752883 * 2 ^ 59
def prefixEnd_4752883 : Nat := 4983230072969 + 3 ^ 40 * 4752883 * 2
def baseEnd_4752883 : Nat := 813504491194477685701465

theorem tailTrace_4752883 : CollatzResearch.WordTrace tailWord_4752883 prefixEnd_4752883 813504491194477685701465 := by
  unfold tailWord_4752883
  simp only [CollatzResearch.WordTrace]
  refine ⟨173351884440124093636559303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115567922960082729091039535 173351884440124093636559303)
  ·
    refine ⟨260027826660186140454838955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173351884440124093636559303 260027826660186140454838955)
    ·
      refine ⟨390041739990279210682258433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260027826660186140454838955 390041739990279210682258433)
      ·
        refine ⟨292531304992709408011693825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 390041739990279210682258433 292531304992709408011693825)
        ·
          refine ⟨219398478744532056008770369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292531304992709408011693825 219398478744532056008770369)
          ·
            refine ⟨164548859058399042006577777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219398478744532056008770369 164548859058399042006577777)
            ·
              refine ⟨123411644293799281504933333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164548859058399042006577777 123411644293799281504933333)
              ·
                refine ⟨2892460413135920660271875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 123411644293799281504933333 2892460413135920660271875)
                ·
                  refine ⟨4338690619703880990407813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2892460413135920660271875 4338690619703880990407813)
                  ·
                    refine ⟨813504491194477685701465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4338690619703880990407813 813504491194477685701465)
                    ·
                      rfl

theorem cell23_4752883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7, 1, 4].length) (baseStart_4752883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752883 prefixEnd_4752883 := by exact prefixLift 4752883
  have htrace : WordTrace (prefixWord ++ tailWord_4752883) baseStart_4752883 baseEnd_4752883 := by
    simpa [prefixWord, tailWord_4752883, baseEnd_4752883] using wordTrace_append hprefix tailTrace_4752883
  have hstable : (prefixWord ++ tailWord_4752883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752883).length < 2 ^ (prefixWord ++ tailWord_4752883).sum := by decide
  have hdescent : baseEnd_4752883 < baseStart_4752883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752893 : List Nat := [1, 4, 1, 1, 1, 5, 1, 2, 2, 2, 3]
def baseStart_4752893 : Nat := 118140960795 + 4752893 * 2 ^ 59
def prefixEnd_4752893 : Nat := 4983230072969 + 3 ^ 40 * 4752893 * 2
def baseEnd_4752893 : Nat := 2440518608389978017979349

theorem tailTrace_4752893 : CollatzResearch.WordTrace tailWord_4752893 prefixEnd_4752893 2440518608389978017979349 := by
  unfold tailWord_4752893
  simp only [CollatzResearch.WordTrace]
  refine ⟨173352249170087865344423333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115568166113391910229615555 173352249170087865344423333)
  ·
    refine ⟨32503546719391474752079375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173352249170087865344423333 32503546719391474752079375)
    ·
      refine ⟨48755320079087212128119063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32503546719391474752079375 48755320079087212128119063)
      ·
        refine ⟨73132980118630818192178595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48755320079087212128119063 73132980118630818192178595)
        ·
          refine ⟨109699470177946227288267893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73132980118630818192178595 109699470177946227288267893)
          ·
            refine ⟨10284325329182458808275115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 109699470177946227288267893 10284325329182458808275115)
            ·
              refine ⟨15426487993773688212412673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10284325329182458808275115 15426487993773688212412673)
              ·
                refine ⟨11569865995330266159309505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15426487993773688212412673 11569865995330266159309505)
                ·
                  refine ⟨8677399496497699619482129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11569865995330266159309505 8677399496497699619482129)
                  ·
                    refine ⟨6508049622373274714611597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8677399496497699619482129 6508049622373274714611597)
                    ·
                      refine ⟨2440518608389978017979349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6508049622373274714611597 2440518608389978017979349)
                      ·
                        rfl

theorem cell23_4752893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2, 2, 3].length) (baseStart_4752893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752893 prefixEnd_4752893 := by exact prefixLift 4752893
  have htrace : WordTrace (prefixWord ++ tailWord_4752893) baseStart_4752893 baseEnd_4752893 := by
    simpa [prefixWord, tailWord_4752893, baseEnd_4752893] using wordTrace_append hprefix tailTrace_4752893
  have hstable : (prefixWord ++ tailWord_4752893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752893).length < 2 ^ (prefixWord ++ tailWord_4752893).sum := by decide
  have hdescent : baseEnd_4752893 < baseStart_4752893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752899 : List Nat := [1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 6]
def baseStart_4752899 : Nat := 118140960795 + 4752899 * 2 ^ 59
def prefixEnd_4752899 : Nat := 4983230072969 + 3 ^ 40 * 4752899 * 2
def baseEnd_4752899 : Nat := 2440521689273904994504321

theorem tailTrace_4752899 : CollatzResearch.WordTrace tailWord_4752899 prefixEnd_4752899 2440521689273904994504321 := by
  unfold tailWord_4752899
  simp only [CollatzResearch.WordTrace]
  refine ⟨173352468008066128369141751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115568312005377418912761167 173352468008066128369141751)
  ·
    refine ⟨260028702012099192553712627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173352468008066128369141751 260028702012099192553712627)
    ·
      refine ⟨390043053018148788830568941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260028702012099192553712627 390043053018148788830568941)
      ·
        refine ⟨146266144881805795811463353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 390043053018148788830568941 146266144881805795811463353)
        ·
          refine ⟨109699608661354346858597515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146266144881805795811463353 109699608661354346858597515)
          ·
            refine ⟨164549412992031520287896273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109699608661354346858597515 164549412992031520287896273)
            ·
              refine ⟨123412059744023640215922205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164549412992031520287896273 123412059744023640215922205)
              ·
                refine ⟨46279522404008865080970827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123412059744023640215922205 46279522404008865080970827)
                ·
                  refine ⟨69419283606013297621456241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46279522404008865080970827 69419283606013297621456241)
                  ·
                    refine ⟨52064462704509973216092181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 69419283606013297621456241 52064462704509973216092181)
                    ·
                      refine ⟨2440521689273904994504321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52064462704509973216092181 2440521689273904994504321)
                      ·
                        rfl

theorem cell23_4752899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_4752899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752899 prefixEnd_4752899 := by exact prefixLift 4752899
  have htrace : WordTrace (prefixWord ++ tailWord_4752899) baseStart_4752899 baseEnd_4752899 := by
    simpa [prefixWord, tailWord_4752899, baseEnd_4752899] using wordTrace_append hprefix tailTrace_4752899
  have hstable : (prefixWord ++ tailWord_4752899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752899).length < 2 ^ (prefixWord ++ tailWord_4752899).sum := by decide
  have hdescent : baseEnd_4752899 < baseStart_4752899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752983 : List Nat := [1, 1, 3, 2, 2, 3, 2, 1, 3, 2, 3]
def baseStart_4752983 : Nat := 118140960795 + 4752983 * 2 ^ 59
def prefixEnd_4752983 : Nat := 4983230072969 + 3 ^ 40 * 4752983 * 2
def baseEnd_4752983 : Nat := 2440564821648882665853935

theorem tailTrace_4752983 : CollatzResearch.WordTrace tailWord_4752983 prefixEnd_4752983 2440564821648882665853935 := by
  unfold tailWord_4752983
  simp only [CollatzResearch.WordTrace]
  refine ⟨173355531739761810715199603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115570354493174540476799735 173355531739761810715199603)
  ·
    refine ⟨260033297609642716072799405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173355531739761810715199603 260033297609642716072799405)
    ·
      refine ⟨97512486603616018527299777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 260033297609642716072799405 97512486603616018527299777)
      ·
        refine ⟨73134364952712013895474833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97512486603616018527299777 73134364952712013895474833)
        ·
          refine ⟨54850773714534010421606125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73134364952712013895474833 54850773714534010421606125)
          ·
            refine ⟨20569040142950253908102297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54850773714534010421606125 20569040142950253908102297)
            ·
              refine ⟨15426780107212690431076723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20569040142950253908102297 15426780107212690431076723)
              ·
                refine ⟨23140170160819035646615085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15426780107212690431076723 23140170160819035646615085)
                ·
                  refine ⟨8677563810307138367480657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23140170160819035646615085 8677563810307138367480657)
                  ·
                    refine ⟨6508172857730353775610493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8677563810307138367480657 6508172857730353775610493)
                    ·
                      refine ⟨2440564821648882665853935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6508172857730353775610493 2440564821648882665853935)
                      ·
                        rfl

theorem cell23_4752983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3, 2, 3].length) (baseStart_4752983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752983 prefixEnd_4752983 := by exact prefixLift 4752983
  have htrace : WordTrace (prefixWord ++ tailWord_4752983) baseStart_4752983 baseEnd_4752983 := by
    simpa [prefixWord, tailWord_4752983, baseEnd_4752983] using wordTrace_append hprefix tailTrace_4752983
  have hstable : (prefixWord ++ tailWord_4752983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752983).length < 2 ^ (prefixWord ++ tailWord_4752983).sum := by decide
  have hdescent : baseEnd_4752983 < baseStart_4752983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4752997 : List Nat := [1, 3, 1, 3, 3, 3, 2, 1, 1, 1, 4]
def baseStart_4752997 : Nat := 118140960795 + 4752997 * 2 ^ 59
def prefixEnd_4752997 : Nat := 4983230072969 + 3 ^ 40 * 4752997 * 2
def baseEnd_4752997 : Nat := 2440572010378045611078871

theorem tailTrace_4752997 : CollatzResearch.WordTrace tailWord_4752997 prefixEnd_4752997 2440572010378045611078871 := by
  unfold tailWord_4752997
  simp only [CollatzResearch.WordTrace]
  refine ⟨173356042361711091106209245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115570694907807394070806163 173356042361711091106209245)
  ·
    refine ⟨65008515885641659164828467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173356042361711091106209245 65008515885641659164828467)
    ·
      refine ⟨97512773828462488747242701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65008515885641659164828467 97512773828462488747242701)
      ·
        refine ⟨36567290185673433280216013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97512773828462488747242701 36567290185673433280216013)
        ·
          refine ⟨13712733819627537480081005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36567290185673433280216013 13712733819627537480081005)
          ·
            refine ⟨5142275182360326555030377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13712733819627537480081005 5142275182360326555030377)
            ·
              refine ⟨3856706386770244916272783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5142275182360326555030377 3856706386770244916272783)
              ·
                refine ⟨5785059580155367374409175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3856706386770244916272783 5785059580155367374409175)
                ·
                  refine ⟨8677589370233051061613763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5785059580155367374409175 8677589370233051061613763)
                  ·
                    refine ⟨13016384055349576592420645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8677589370233051061613763 13016384055349576592420645)
                    ·
                      refine ⟨2440572010378045611078871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13016384055349576592420645 2440572010378045611078871)
                      ·
                        rfl

theorem cell23_4752997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 1, 1, 1, 4].length) (baseStart_4752997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4752997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4752997 prefixEnd_4752997 := by exact prefixLift 4752997
  have htrace : WordTrace (prefixWord ++ tailWord_4752997) baseStart_4752997 baseEnd_4752997 := by
    simpa [prefixWord, tailWord_4752997, baseEnd_4752997] using wordTrace_append hprefix tailTrace_4752997
  have hstable : (prefixWord ++ tailWord_4752997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4752997).length < 2 ^ (prefixWord ++ tailWord_4752997).sum := by decide
  have hdescent : baseEnd_4752997 < baseStart_4752997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4752997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753014 : List Nat := [5, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2]
def baseStart_4753014 : Nat := 118140960795 + 4753014 * 2 ^ 59
def prefixEnd_4753014 : Nat := 4983230072969 + 3 ^ 40 * 4753014 * 2
def baseEnd_4753014 : Nat := 2440580739549172044566293

theorem tailTrace_4753014 : CollatzResearch.WordTrace tailWord_4753014 prefixEnd_4753014 2440580739549172044566293 := by
  unfold tailWord_4753014
  simp only [CollatzResearch.WordTrace]
  refine ⟨10834791400165593938098631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115571108268433002006385397 10834791400165593938098631)
  ·
    refine ⟨16252187100248390907147947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10834791400165593938098631 16252187100248390907147947)
    ·
      refine ⟨24378280650372586360721921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16252187100248390907147947 24378280650372586360721921)
      ·
        refine ⟨18283710487779439770541441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24378280650372586360721921 18283710487779439770541441)
        ·
          refine ⟨13712782865834579827906081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18283710487779439770541441 13712782865834579827906081)
          ·
            refine ⟨10284587149375934870929561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13712782865834579827906081 10284587149375934870929561)
            ·
              refine ⟨7713440362031951153197171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10284587149375934870929561 7713440362031951153197171)
              ·
                refine ⟨11570160543047926729795757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7713440362031951153197171 11570160543047926729795757)
                ·
                  refine ⟨4338810203642972523673409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11570160543047926729795757 4338810203642972523673409)
                  ·
                    refine ⟨3254107652732229392755057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4338810203642972523673409 3254107652732229392755057)
                    ·
                      refine ⟨2440580739549172044566293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3254107652732229392755057 2440580739549172044566293)
                      ·
                        rfl

theorem cell23_4753014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_4753014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753014 prefixEnd_4753014 := by exact prefixLift 4753014
  have htrace : WordTrace (prefixWord ++ tailWord_4753014) baseStart_4753014 baseEnd_4753014 := by
    simpa [prefixWord, tailWord_4753014, baseEnd_4753014] using wordTrace_append hprefix tailTrace_4753014
  have hstable : (prefixWord ++ tailWord_4753014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753014).length < 2 ^ (prefixWord ++ tailWord_4753014).sum := by decide
  have hdescent : baseEnd_4753014 < baseStart_4753014 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753057 : List Nat := [1, 2, 3, 3, 2, 1, 2, 3, 1, 3, 2]
def baseStart_4753057 : Nat := 118140960795 + 4753057 * 2 ^ 59
def prefixEnd_4753057 : Nat := 4983230072969 + 3 ^ 40 * 4753057 * 2
def baseEnd_4753057 : Nat := 2440602819217315376328595

theorem tailTrace_4753057 : CollatzResearch.WordTrace tailWord_4753057 prefixEnd_4753057 2440602819217315376328595 := by
  unfold tailWord_4753057
  simp only [CollatzResearch.WordTrace]
  refine ⟨173358230741493721353393425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115572153827662480902262283 173358230741493721353393425)
  ·
    refine ⟨130018673056120291015045069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173358230741493721353393425 130018673056120291015045069)
    ·
      refine ⟨48757002396045109130641901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130018673056120291015045069 48757002396045109130641901)
      ·
        refine ⟨18283875898516915923990713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48757002396045109130641901 18283875898516915923990713)
        ·
          refine ⟨13712906923887686942993035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18283875898516915923990713 13712906923887686942993035)
          ·
            refine ⟨20569360385831530414489553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13712906923887686942993035 20569360385831530414489553)
            ·
              refine ⟨15427020289373647810867165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20569360385831530414489553 15427020289373647810867165)
              ·
                refine ⟨5785132608515117929075187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15427020289373647810867165 5785132608515117929075187)
                ·
                  refine ⟨8677698912772676893612781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5785132608515117929075187 8677698912772676893612781)
                  ·
                    refine ⟨3254137092289753835104793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8677698912772676893612781 3254137092289753835104793)
                    ·
                      refine ⟨2440602819217315376328595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3254137092289753835104793 2440602819217315376328595)
                      ·
                        rfl

theorem cell23_4753057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_4753057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753057 prefixEnd_4753057 := by exact prefixLift 4753057
  have htrace : WordTrace (prefixWord ++ tailWord_4753057) baseStart_4753057 baseEnd_4753057 := by
    simpa [prefixWord, tailWord_4753057, baseEnd_4753057] using wordTrace_append hprefix tailTrace_4753057
  have hstable : (prefixWord ++ tailWord_4753057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753057).length < 2 ^ (prefixWord ++ tailWord_4753057).sum := by decide
  have hdescent : baseEnd_4753057 < baseStart_4753057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753087 : List Nat := [1, 1, 2, 2, 2, 3, 3, 3, 2, 2, 2]
def baseStart_4753087 : Nat := 118140960795 + 4753087 * 2 ^ 59
def prefixEnd_4753087 : Nat := 4983230072969 + 3 ^ 40 * 4753087 * 2
def baseEnd_4753087 : Nat := 2440618223636950258953457

theorem tailTrace_4753087 : CollatzResearch.WordTrace tailWord_4753087 prefixEnd_4753087 2440618223636950258953457 := by
  unfold tailWord_4753087
  simp only [CollatzResearch.WordTrace]
  refine ⟨173359324931385036476985515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115572883287590024317990343 173359324931385036476985515)
  ·
    refine ⟨260038987397077554715478273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173359324931385036476985515 260038987397077554715478273)
    ·
      refine ⟨195029240547808166036608705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260038987397077554715478273 195029240547808166036608705)
      ·
        refine ⟨146271930410856124527456529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195029240547808166036608705 146271930410856124527456529)
        ·
          refine ⟨109703947808142093395592397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146271930410856124527456529 109703947808142093395592397)
          ·
            refine ⟨41138980428053285023347149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109703947808142093395592397 41138980428053285023347149)
            ·
              refine ⟨15427117660519981883755181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41138980428053285023347149 15427117660519981883755181)
              ·
                refine ⟨5785169122694993206408193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15427117660519981883755181 5785169122694993206408193)
                ·
                  refine ⟨4338876842021244904806145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5785169122694993206408193 4338876842021244904806145)
                  ·
                    refine ⟨3254157631515933678604609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4338876842021244904806145 3254157631515933678604609)
                    ·
                      refine ⟨2440618223636950258953457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3254157631515933678604609 2440618223636950258953457)
                      ·
                        rfl

theorem cell23_4753087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 2, 2, 2].length) (baseStart_4753087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753087 prefixEnd_4753087 := by exact prefixLift 4753087
  have htrace : WordTrace (prefixWord ++ tailWord_4753087) baseStart_4753087 baseEnd_4753087 := by
    simpa [prefixWord, tailWord_4753087, baseEnd_4753087] using wordTrace_append hprefix tailTrace_4753087
  have hstable : (prefixWord ++ tailWord_4753087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753087).length < 2 ^ (prefixWord ++ tailWord_4753087).sum := by decide
  have hdescent : baseEnd_4753087 < baseStart_4753087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753130 : List Nat := [3, 1, 3, 1, 1, 1, 3, 1, 2, 5, 2]
def baseStart_4753130 : Nat := 118140960795 + 4753130 * 2 ^ 59
def prefixEnd_4753130 : Nat := 4983230072969 + 3 ^ 40 * 4753130 * 2
def baseEnd_4753130 : Nat := 2440640303305093590715759

theorem tailTrace_4753130 : CollatzResearch.WordTrace tailWord_4753130 prefixEnd_4753130 2440640303305093590715759 := by
  unfold tailWord_4753130
  simp only [CollatzResearch.WordTrace]
  refine ⟨43340223317557313705200211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115573928846819503213867229 43340223317557313705200211)
  ·
    refine ⟨65010334976335970557800317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43340223317557313705200211 65010334976335970557800317)
    ·
      refine ⟨24378875616125988959175119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65010334976335970557800317 24378875616125988959175119)
      ·
        refine ⟨36568313424188983438762679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24378875616125988959175119 36568313424188983438762679)
        ·
          refine ⟨54852470136283475158144019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36568313424188983438762679 54852470136283475158144019)
          ·
            refine ⟨82278705204425212737216029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54852470136283475158144019 82278705204425212737216029)
            ·
              refine ⟨30854514451659454776456011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82278705204425212737216029 30854514451659454776456011)
              ·
                refine ⟨46281771677489182164684017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30854514451659454776456011 46281771677489182164684017)
                ·
                  refine ⟨34711328758116886623513013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46281771677489182164684017 34711328758116886623513013)
                  ·
                    refine ⟨3254187071073458120954345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34711328758116886623513013 3254187071073458120954345)
                    ·
                      refine ⟨2440640303305093590715759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3254187071073458120954345 2440640303305093590715759)
                      ·
                        rfl

theorem cell23_4753130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 2, 5, 2].length) (baseStart_4753130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753130 prefixEnd_4753130 := by exact prefixLift 4753130
  have htrace : WordTrace (prefixWord ++ tailWord_4753130) baseStart_4753130 baseEnd_4753130 := by
    simpa [prefixWord, tailWord_4753130, baseEnd_4753130] using wordTrace_append hprefix tailTrace_4753130
  have hstable : (prefixWord ++ tailWord_4753130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753130).length < 2 ^ (prefixWord ++ tailWord_4753130).sum := by decide
  have hdescent : baseEnd_4753130 < baseStart_4753130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753143 : List Nat := [1, 1, 3, 1, 1, 1, 4, 2, 4, 1, 4]
def baseStart_4753143 : Nat := 118140960795 + 4753143 * 2 ^ 59
def prefixEnd_4753143 : Nat := 4983230072969 + 3 ^ 40 * 4753143 * 2
def baseEnd_4753143 : Nat := 2440646978553602039853199

theorem tailTrace_4753143 : CollatzResearch.WordTrace tailWord_4753143 prefixEnd_4753143 2440646978553602039853199 := by
  unfold tailWord_4753143
  simp only [CollatzResearch.WordTrace]
  refine ⟨173361367419182158041024083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115574244946121438694016055 173361367419182158041024083)
  ·
    refine ⟨260042051128773237061536125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173361367419182158041024083 260042051128773237061536125)
    ·
      refine ⟨97515769173289963898076047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 260042051128773237061536125 97515769173289963898076047)
      ·
        refine ⟨146273653759934945847114071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97515769173289963898076047 146273653759934945847114071)
        ·
          refine ⟨219410480639902418770671107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146273653759934945847114071 219410480639902418770671107)
          ·
            refine ⟨329115720959853628156006661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219410480639902418770671107 329115720959853628156006661)
            ·
              refine ⟨61709197679972555279251249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 329115720959853628156006661 61709197679972555279251249)
              ·
                refine ⟨46281898259979416459438437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61709197679972555279251249 46281898259979416459438437)
                ·
                  refine ⟨8677855923746140586144707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46281898259979416459438437 8677855923746140586144707)
                  ·
                    refine ⟨13016783885619210879217061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8677855923746140586144707 13016783885619210879217061)
                    ·
                      refine ⟨2440646978553602039853199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13016783885619210879217061 2440646978553602039853199)
                      ·
                        rfl

theorem cell23_4753143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4, 1, 4].length) (baseStart_4753143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753143 prefixEnd_4753143 := by exact prefixLift 4753143
  have htrace : WordTrace (prefixWord ++ tailWord_4753143) baseStart_4753143 baseEnd_4753143 := by
    simpa [prefixWord, tailWord_4753143, baseEnd_4753143] using wordTrace_append hprefix tailTrace_4753143
  have hstable : (prefixWord ++ tailWord_4753143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753143).length < 2 ^ (prefixWord ++ tailWord_4753143).sum := by decide
  have hdescent : baseEnd_4753143 < baseStart_4753143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753160 : List Nat := [2, 1, 3, 2, 2, 1, 1, 2, 1, 6, 2]
def baseStart_4753160 : Nat := 118140960795 + 4753160 * 2 ^ 59
def prefixEnd_4753160 : Nat := 4983230072969 + 3 ^ 40 * 4753160 * 2
def baseEnd_4753160 : Nat := 2440655707724728473340621

theorem tailTrace_4753160 : CollatzResearch.WordTrace tailWord_4753160 prefixEnd_4753160 2440655707724728473340621 := by
  unfold tailWord_4753160
  simp only [CollatzResearch.WordTrace]
  refine ⟨86680993730060284972196467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115574658306747046629595289 86680993730060284972196467)
  ·
    refine ⟨130021490595090427458294701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86680993730060284972196467 130021490595090427458294701)
    ·
      refine ⟨48758058973158910296860513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130021490595090427458294701 48758058973158910296860513)
      ·
        refine ⟨36568544229869182722645385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48758058973158910296860513 36568544229869182722645385)
        ·
          refine ⟨27426408172401887041984039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36568544229869182722645385 27426408172401887041984039)
          ·
            refine ⟨41139612258602830562976059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27426408172401887041984039 41139612258602830562976059)
            ·
              refine ⟨61709418387904245844464089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41139612258602830562976059 61709418387904245844464089)
              ·
                refine ⟨46282063790928184383348067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61709418387904245844464089 46282063790928184383348067)
                ·
                  refine ⟨69423095686392276575022101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46282063790928184383348067 69423095686392276575022101)
                  ·
                    refine ⟨3254207610299637964454161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 69423095686392276575022101 3254207610299637964454161)
                    ·
                      refine ⟨2440655707724728473340621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3254207610299637964454161 2440655707724728473340621)
                      ·
                        rfl

theorem cell23_4753160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 1, 6, 2].length) (baseStart_4753160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753160 prefixEnd_4753160 := by exact prefixLift 4753160
  have htrace : WordTrace (prefixWord ++ tailWord_4753160) baseStart_4753160 baseEnd_4753160 := by
    simpa [prefixWord, tailWord_4753160, baseEnd_4753160] using wordTrace_append hprefix tailTrace_4753160
  have hstable : (prefixWord ++ tailWord_4753160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753160).length < 2 ^ (prefixWord ++ tailWord_4753160).sum := by decide
  have hdescent : baseEnd_4753160 < baseStart_4753160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753172 : List Nat := [2, 4, 4, 1, 2, 1, 1, 2, 2, 2, 2]
def baseStart_4753172 : Nat := 118140960795 + 4753172 * 2 ^ 59
def prefixEnd_4753172 : Nat := 4983230072969 + 3 ^ 40 * 4753172 * 2
def baseEnd_4753172 : Nat := 2440661869492582426390567

theorem tailTrace_4753172 : CollatzResearch.WordTrace tailWord_4753172 prefixEnd_4753172 2440661869492582426390567 := by
  unfold tailWord_4753172
  simp only [CollatzResearch.WordTrace]
  refine ⟨86681212568038547996914885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115574950090718063995886513 86681212568038547996914885)
  ·
    refine ⟨16252727356507227749421541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86681212568038547996914885 16252727356507227749421541)
    ·
      refine ⟨3047386379345105203016539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16252727356507227749421541 3047386379345105203016539)
      ·
        refine ⟨4571079569017657804524809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3047386379345105203016539 4571079569017657804524809)
        ·
          refine ⟨3428309676763243353393607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4571079569017657804524809 3428309676763243353393607)
          ·
            refine ⟨5142464515144865030090411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3428309676763243353393607 5142464515144865030090411)
            ·
              refine ⟨7713696772717297545135617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5142464515144865030090411 7713696772717297545135617)
              ·
                refine ⟨5785272579537973158851713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7713696772717297545135617 5785272579537973158851713)
                ·
                  refine ⟨4338954434653479869138785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5785272579537973158851713 4338954434653479869138785)
                  ·
                    refine ⟨3254215825990109901854089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4338954434653479869138785 3254215825990109901854089)
                    ·
                      refine ⟨2440661869492582426390567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3254215825990109901854089 2440661869492582426390567)
                      ·
                        rfl

theorem cell23_4753172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_4753172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753172 prefixEnd_4753172 := by exact prefixLift 4753172
  have htrace : WordTrace (prefixWord ++ tailWord_4753172) baseStart_4753172 baseEnd_4753172 := by
    simpa [prefixWord, tailWord_4753172, baseEnd_4753172] using wordTrace_append hprefix tailTrace_4753172
  have hstable : (prefixWord ++ tailWord_4753172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753172).length < 2 ^ (prefixWord ++ tailWord_4753172).sum := by decide
  have hdescent : baseEnd_4753172 < baseStart_4753172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753173 : List Nat := [1, 3, 2, 1, 2, 3, 1, 1, 2, 1, 6]
def baseStart_4753173 : Nat := 118140960795 + 4753173 * 2 ^ 59
def prefixEnd_4753173 : Nat := 4983230072969 + 3 ^ 40 * 4753173 * 2
def baseEnd_4753173 : Nat := 2440662382973236922478061

theorem tailTrace_4753173 : CollatzResearch.WordTrace tailWord_4753173 prefixEnd_4753173 2440662382973236922478061 := by
  unfold tailWord_4753173
  simp only [CollatzResearch.WordTrace]
  refine ⟨173362461609073473164616173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115574974406048982109744115 173362461609073473164616173)
  ·
    refine ⟨65010923103402552436731065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173362461609073473164616173 65010923103402552436731065)
    ·
      refine ⟨48758192327551914327548299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65010923103402552436731065 48758192327551914327548299)
      ·
        refine ⟨73137288491327871491322449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48758192327551914327548299 73137288491327871491322449)
        ·
          refine ⟨54852966368495903618491837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73137288491327871491322449 54852966368495903618491837)
          ·
            refine ⟨20569862388185963856934439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54852966368495903618491837 20569862388185963856934439)
            ·
              refine ⟨30854793582278945785401659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20569862388185963856934439 30854793582278945785401659)
              ·
                refine ⟨46282190373418418678102489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30854793582278945785401659 46282190373418418678102489)
                ·
                  refine ⟨34711642780063814008576867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46282190373418418678102489 34711642780063814008576867)
                  ·
                    refine ⟨52067464170095721012865301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34711642780063814008576867 52067464170095721012865301)
                    ·
                      refine ⟨2440662382973236922478061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52067464170095721012865301 2440662382973236922478061)
                      ·
                        rfl

theorem cell23_4753173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_4753173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753173 prefixEnd_4753173 := by exact prefixLift 4753173
  have htrace : WordTrace (prefixWord ++ tailWord_4753173) baseStart_4753173 baseEnd_4753173 := by
    simpa [prefixWord, tailWord_4753173, baseEnd_4753173] using wordTrace_append hprefix tailTrace_4753173
  have hstable : (prefixWord ++ tailWord_4753173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753173).length < 2 ^ (prefixWord ++ tailWord_4753173).sum := by decide
  have hdescent : baseEnd_4753173 < baseStart_4753173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753180 : List Nat := [2, 2, 3, 1, 1, 2, 2, 1, 4, 2, 3]
def baseStart_4753180 : Nat := 118140960795 + 4753180 * 2 ^ 59
def prefixEnd_4753180 : Nat := 4983230072969 + 3 ^ 40 * 4753180 * 2
def baseEnd_4753180 : Nat := 2440665977337818395090529

theorem tailTrace_4753180 : CollatzResearch.WordTrace tailWord_4753180 prefixEnd_4753180 2440665977337818395090529 := by
  unfold tailWord_4753180
  simp only [CollatzResearch.WordTrace]
  refine ⟨86681358460024056680060497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115575144613365408906747329 86681358460024056680060497)
  ·
    refine ⟨65011018845018042510045373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86681358460024056680060497 65011018845018042510045373)
    ·
      refine ⟨24379132066881765941267015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65011018845018042510045373 24379132066881765941267015)
      ·
        refine ⟨36568698100322648911900523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24379132066881765941267015 36568698100322648911900523)
        ·
          refine ⟨54853047150483973367850785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36568698100322648911900523 54853047150483973367850785)
          ·
            refine ⟨41139785362862980025888089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54853047150483973367850785 41139785362862980025888089)
            ·
              refine ⟨30854839022147235019416067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41139785362862980025888089 30854839022147235019416067)
              ·
                refine ⟨46282258533220852529124101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30854839022147235019416067 46282258533220852529124101)
                ·
                  refine ⟨8677923474978909849210769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46282258533220852529124101 8677923474978909849210769)
                  ·
                    refine ⟨6508442606234182386908077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8677923474978909849210769 6508442606234182386908077)
                    ·
                      refine ⟨2440665977337818395090529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6508442606234182386908077 2440665977337818395090529)
                      ·
                        rfl

theorem cell23_4753180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_4753180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753180 prefixEnd_4753180 := by exact prefixLift 4753180
  have htrace : WordTrace (prefixWord ++ tailWord_4753180) baseStart_4753180 baseEnd_4753180 := by
    simpa [prefixWord, tailWord_4753180, baseEnd_4753180] using wordTrace_append hprefix tailTrace_4753180
  have hstable : (prefixWord ++ tailWord_4753180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753180).length < 2 ^ (prefixWord ++ tailWord_4753180).sum := by decide
  have hdescent : baseEnd_4753180 < baseStart_4753180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753183 : List Nat := [1, 1, 2, 4, 2, 1, 3, 1, 8]
def baseStart_4753183 : Nat := 118140960795 + 4753183 * 2 ^ 59
def prefixEnd_4753183 : Nat := 4983230072969 + 3 ^ 40 * 4753183 * 2
def baseEnd_4753183 : Nat := 271185279753309098150335

theorem tailTrace_4753183 : CollatzResearch.WordTrace tailWord_4753183 prefixEnd_4753183 271185279753309098150335 := by
  unfold tailWord_4753183
  simp only [CollatzResearch.WordTrace]
  refine ⟨173362826339037244872480203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115575217559358163248320135 173362826339037244872480203)
  ·
    refine ⟨260044239508555867308720305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173362826339037244872480203 260044239508555867308720305)
    ·
      refine ⟨195033179631416900481540229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260044239508555867308720305 195033179631416900481540229)
      ·
        refine ⟨36568721180890668840288793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 195033179631416900481540229 36568721180890668840288793)
        ·
          refine ⟨27426540885668001630216595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36568721180890668840288793 27426540885668001630216595)
          ·
            refine ⟨41139811328502002445324893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27426540885668001630216595 41139811328502002445324893)
            ·
              refine ⟨15427429248188250916996835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41139811328502002445324893 15427429248188250916996835)
              ·
                refine ⟨23141143872282376375495253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15427429248188250916996835 23141143872282376375495253)
                ·
                  refine ⟨271185279753309098150335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23141143872282376375495253 271185279753309098150335)
                  ·
                    rfl

theorem cell23_4753183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 8].length) (baseStart_4753183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753183 prefixEnd_4753183 := by exact prefixLift 4753183
  have htrace : WordTrace (prefixWord ++ tailWord_4753183) baseStart_4753183 baseEnd_4753183 := by
    simpa [prefixWord, tailWord_4753183, baseEnd_4753183] using wordTrace_append hprefix tailTrace_4753183
  have hstable : (prefixWord ++ tailWord_4753183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753183).length < 2 ^ (prefixWord ++ tailWord_4753183).sum := by decide
  have hdescent : baseEnd_4753183 < baseStart_4753183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753187 : List Nat := [1, 1, 1, 4, 2, 1, 4, 4, 1, 4]
def baseStart_4753187 : Nat := 118140960795 + 4753187 * 2 ^ 59
def prefixEnd_4753187 : Nat := 4983230072969 + 3 ^ 40 * 4753187 * 2
def baseEnd_4753187 : Nat := 813556523900799955900999

theorem tailTrace_4753187 : CollatzResearch.WordTrace tailWord_4753187 prefixEnd_4753187 813556523900799955900999 := by
  unfold tailWord_4753187
  simp only [CollatzResearch.WordTrace]
  refine ⟨173362972231022753555625815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115575314820681835703750543 173362972231022753555625815)
  ·
    refine ⟨260044458346534130333438723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173362972231022753555625815 260044458346534130333438723)
    ·
      refine ⟨390066687519801195500158085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260044458346534130333438723 390066687519801195500158085)
      ·
        refine ⟨73137503909962724156279641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 390066687519801195500158085 73137503909962724156279641)
        ·
          refine ⟨54853127932472043117209731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73137503909962724156279641 54853127932472043117209731)
          ·
            refine ⟨82279691898708064675814597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54853127932472043117209731 82279691898708064675814597)
            ·
              refine ⟨15427442231007762126715237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82279691898708064675814597 15427442231007762126715237)
              ·
                refine ⟨2892645418313955398759107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15427442231007762126715237 2892645418313955398759107)
                ·
                  refine ⟨4338968127470933098138661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2892645418313955398759107 4338968127470933098138661)
                  ·
                    refine ⟨813556523900799955900999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4338968127470933098138661 813556523900799955900999)
                    ·
                      rfl

theorem cell23_4753187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 4, 1, 4].length) (baseStart_4753187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753187 prefixEnd_4753187 := by exact prefixLift 4753187
  have htrace : WordTrace (prefixWord ++ tailWord_4753187) baseStart_4753187 baseEnd_4753187 := by
    simpa [prefixWord, tailWord_4753187, baseEnd_4753187] using wordTrace_append hprefix tailTrace_4753187
  have hstable : (prefixWord ++ tailWord_4753187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753187).length < 2 ^ (prefixWord ++ tailWord_4753187).sum := by decide
  have hdescent : baseEnd_4753187 < baseStart_4753187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753193 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 4, 5, 3]
def baseStart_4753193 : Nat := 118140960795 + 4753193 * 2 ^ 59
def prefixEnd_4753193 : Nat := 4983230072969 + 3 ^ 40 * 4753193 * 2
def baseEnd_4753193 : Nat := 2440672652586326844227969

theorem tailTrace_4753193 : CollatzResearch.WordTrace tailWord_4753193 prefixEnd_4753193 2440672652586326844227969 := by
  unfold tailWord_4753193
  simp only [CollatzResearch.WordTrace]
  refine ⟨173363191069001016580344233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115575460712667344386896155 173363191069001016580344233)
  ·
    refine ⟨130022393301750762435258175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173363191069001016580344233 130022393301750762435258175)
    ·
      refine ⟨195033589952626143652887263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130022393301750762435258175 195033589952626143652887263)
      ·
        refine ⟨292550384928939215479330895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195033589952626143652887263 292550384928939215479330895)
        ·
          refine ⟨438825577393408823218996343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292550384928939215479330895 438825577393408823218996343)
          ·
            refine ⟨658238366090113234828494515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 438825577393408823218996343 658238366090113234828494515)
            ·
              refine ⟨987357549135169852242741773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 658238366090113234828494515 987357549135169852242741773)
              ·
                refine ⟨370259080925688694591028165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 987357549135169852242741773 370259080925688694591028165)
                ·
                  refine ⟨69423577673566630235817781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 370259080925688694591028165 69423577673566630235817781)
                  ·
                    refine ⟨6508460406896871584607917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 69423577673566630235817781 6508460406896871584607917)
                    ·
                      refine ⟨2440672652586326844227969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6508460406896871584607917 2440672652586326844227969)
                      ·
                        rfl

theorem cell23_4753193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 5, 3].length) (baseStart_4753193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753193 prefixEnd_4753193 := by exact prefixLift 4753193
  have htrace : WordTrace (prefixWord ++ tailWord_4753193) baseStart_4753193 baseEnd_4753193 := by
    simpa [prefixWord, tailWord_4753193, baseEnd_4753193] using wordTrace_append hprefix tailTrace_4753193
  have hstable : (prefixWord ++ tailWord_4753193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753193).length < 2 ^ (prefixWord ++ tailWord_4753193).sum := by decide
  have hdescent : baseEnd_4753193 < baseStart_4753193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753237 : List Nat := [1, 3, 2, 2, 2, 2, 1, 1, 4, 3, 2]
def baseStart_4753237 : Nat := 118140960795 + 4753237 * 2 ^ 59
def prefixEnd_4753237 : Nat := 4983230072969 + 3 ^ 40 * 4753237 * 2
def baseEnd_4753237 : Nat := 2440695245735124672077767

theorem tailTrace_4753237 : CollatzResearch.WordTrace tailWord_4753237 prefixEnd_4753237 2440695245735124672077767 := by
  unfold tailWord_4753237
  simp only [CollatzResearch.WordTrace]
  refine ⟨173364795880841612094945965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115576530587227741396630643 173364795880841612094945965)
  ·
    refine ⟨65011798455315604535604737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173364795880841612094945965 65011798455315604535604737)
    ·
      refine ⟨48758848841486703401703553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65011798455315604535604737 48758848841486703401703553)
      ·
        refine ⟨36569136631115027551277665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48758848841486703401703553 36569136631115027551277665)
        ·
          refine ⟨27426852473336270663458249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36569136631115027551277665 27426852473336270663458249)
          ·
            refine ⟨20570139355002202997593687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27426852473336270663458249 20570139355002202997593687)
            ·
              refine ⟨30855209032503304496390531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20570139355002202997593687 30855209032503304496390531)
              ·
                refine ⟨46282813548754956744585797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30855209032503304496390531 46282813548754956744585797)
                ·
                  refine ⟨8678027540391554389609837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46282813548754956744585797 8678027540391554389609837)
                  ·
                    refine ⟨3254260327646832896103689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8678027540391554389609837 3254260327646832896103689)
                    ·
                      refine ⟨2440695245735124672077767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3254260327646832896103689 2440695245735124672077767)
                      ·
                        rfl

theorem cell23_4753237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4, 3, 2].length) (baseStart_4753237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753237 prefixEnd_4753237 := by exact prefixLift 4753237
  have htrace : WordTrace (prefixWord ++ tailWord_4753237) baseStart_4753237 baseEnd_4753237 := by
    simpa [prefixWord, tailWord_4753237, baseEnd_4753237] using wordTrace_append hprefix tailTrace_4753237
  have hstable : (prefixWord ++ tailWord_4753237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753237).length < 2 ^ (prefixWord ++ tailWord_4753237).sum := by decide
  have hdescent : baseEnd_4753237 < baseStart_4753237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753267 : List Nat := [1, 1, 1, 2, 2, 1, 3, 3, 5, 2, 2]
def baseStart_4753267 : Nat := 118140960795 + 4753267 * 2 ^ 59
def prefixEnd_4753267 : Nat := 4983230072969 + 3 ^ 40 * 4753267 * 2
def baseEnd_4753267 : Nat := 2440710650154759554702629

theorem tailTrace_4753267 : CollatzResearch.WordTrace tailWord_4753267 prefixEnd_4753267 2440710650154759554702629 := by
  unfold tailWord_4753267
  simp only [CollatzResearch.WordTrace]
  refine ⟨173365890070732927218538055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115577260047155284812358703 173365890070732927218538055)
  ·
    refine ⟨260048835106099390827807083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173365890070732927218538055 260048835106099390827807083)
    ·
      refine ⟨390073252659149086241710625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260048835106099390827807083 390073252659149086241710625)
      ·
        refine ⟨292554939494361814681282969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 390073252659149086241710625 292554939494361814681282969)
        ·
          refine ⟨219416204620771361010962227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292554939494361814681282969 219416204620771361010962227)
          ·
            refine ⟨329124306931157041516443341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219416204620771361010962227 329124306931157041516443341)
            ·
              refine ⟨123421615099183890568666253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 329124306931157041516443341 123421615099183890568666253)
              ·
                refine ⟨46283105662193958963249845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123421615099183890568666253 46283105662193958963249845)
                ·
                  refine ⟨4339041155830683652804673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46283105662193958963249845 4339041155830683652804673)
                  ·
                    refine ⟨3254280866873012739603505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4339041155830683652804673 3254280866873012739603505)
                    ·
                      refine ⟨2440710650154759554702629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3254280866873012739603505 2440710650154759554702629)
                      ·
                        rfl

theorem cell23_4753267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 5, 2, 2].length) (baseStart_4753267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753267 prefixEnd_4753267 := by exact prefixLift 4753267
  have htrace : WordTrace (prefixWord ++ tailWord_4753267) baseStart_4753267 baseEnd_4753267 := by
    simpa [prefixWord, tailWord_4753267, baseEnd_4753267] using wordTrace_append hprefix tailTrace_4753267
  have hstable : (prefixWord ++ tailWord_4753267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753267).length < 2 ^ (prefixWord ++ tailWord_4753267).sum := by decide
  have hdescent : baseEnd_4753267 < baseStart_4753267 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753273 : List Nat := [1, 2, 1, 3, 2, 2, 1, 11]
def baseStart_4753273 : Nat := 118140960795 + 4753273 * 2 ^ 59
def prefixEnd_4753273 : Nat := 4983230072969 + 3 ^ 40 * 4753273 * 2
def baseEnd_4753273 : Nat := 90396804853284686341763

theorem tailTrace_4753273 : CollatzResearch.WordTrace tailWord_4753273 prefixEnd_4753273 90396804853284686341763 := by
  unfold tailWord_4753273
  simp only [CollatzResearch.WordTrace]
  refine ⟨173366108908711190243256473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115577405939140793495504315 173366108908711190243256473)
  ·
    refine ⟨130024581681533392682442355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173366108908711190243256473 130024581681533392682442355)
    ·
      refine ⟨195036872522300089023663533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130024581681533392682442355 195036872522300089023663533)
      ·
        refine ⟨73138827195862533383873825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195036872522300089023663533 73138827195862533383873825)
        ·
          refine ⟨54854120396896900037905369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73138827195862533383873825 54854120396896900037905369)
          ·
            refine ⟨41140590297672675028429027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54854120396896900037905369 41140590297672675028429027)
            ·
              refine ⟨61710885446509012542643541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41140590297672675028429027 61710885446509012542643541)
              ·
                refine ⟨90396804853284686341763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 61710885446509012542643541 90396804853284686341763)
                ·
                  rfl

theorem cell23_4753273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 11].length) (baseStart_4753273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753273 prefixEnd_4753273 := by exact prefixLift 4753273
  have htrace : WordTrace (prefixWord ++ tailWord_4753273) baseStart_4753273 baseEnd_4753273 := by
    simpa [prefixWord, tailWord_4753273, baseEnd_4753273] using wordTrace_append hprefix tailTrace_4753273
  have hstable : (prefixWord ++ tailWord_4753273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753273).length < 2 ^ (prefixWord ++ tailWord_4753273).sum := by decide
  have hdescent : baseEnd_4753273 < baseStart_4753273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753280 : List Nat := [2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 4]
def baseStart_4753280 : Nat := 118140960795 + 4753280 * 2 ^ 59
def prefixEnd_4753280 : Nat := 4983230072969 + 3 ^ 40 * 4753280 * 2
def baseEnd_4753280 : Nat := 2440717325403268003840069

theorem tailTrace_4753280 : CollatzResearch.WordTrace tailWord_4753280 prefixEnd_4753280 2440717325403268003840069 := by
  unfold tailWord_4753280
  simp only [CollatzResearch.WordTrace]
  refine ⟨86683182109842915219380647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115577576146457220292507529 86683182109842915219380647)
  ·
    refine ⟨130024773164764372829070971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86683182109842915219380647 130024773164764372829070971)
    ·
      refine ⟨195037159747146559243606457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130024773164764372829070971 195037159747146559243606457)
      ·
        refine ⟨146277869810359919432704843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195037159747146559243606457 146277869810359919432704843)
        ·
          refine ⟨219416804715539879149057265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146277869810359919432704843 219416804715539879149057265)
          ·
            refine ⟨164562603536654909361792949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219416804715539879149057265 164562603536654909361792949)
            ·
              refine ⟨15427744081561397752668089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 164562603536654909361792949 15427744081561397752668089)
              ·
                refine ⟨11570808061171048314501067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15427744081561397752668089 11570808061171048314501067)
                ·
                  refine ⟨17356212091756572471751601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11570808061171048314501067 17356212091756572471751601)
                  ·
                    refine ⟨13017159068817429353813701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17356212091756572471751601 13017159068817429353813701)
                    ·
                      refine ⟨2440717325403268003840069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13017159068817429353813701 2440717325403268003840069)
                      ·
                        rfl

theorem cell23_4753280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 4].length) (baseStart_4753280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753280 prefixEnd_4753280 := by exact prefixLift 4753280
  have htrace : WordTrace (prefixWord ++ tailWord_4753280) baseStart_4753280 baseEnd_4753280 := by
    simpa [prefixWord, tailWord_4753280, baseEnd_4753280] using wordTrace_append hprefix tailTrace_4753280
  have hstable : (prefixWord ++ tailWord_4753280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753280).length < 2 ^ (prefixWord ++ tailWord_4753280).sum := by decide
  have hdescent : baseEnd_4753280 < baseStart_4753280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753281 : List Nat := [1, 2, 4, 4, 1, 1, 3, 1, 1, 5]
def baseStart_4753281 : Nat := 118140960795 + 4753281 * 2 ^ 59
def prefixEnd_4753281 : Nat := 4983230072969 + 3 ^ 40 * 4753281 * 2
def baseEnd_4753281 : Nat := 813572612961307499975855

theorem tailTrace_4753281 : CollatzResearch.WordTrace tailWord_4753281 prefixEnd_4753281 813572612961307499975855 := by
  unfold tailWord_4753281
  simp only [CollatzResearch.WordTrace]
  refine ⟨173366400692682207609547697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115577600461788138406365131 173366400692682207609547697)
  ·
    refine ⟨130024800519511655707160773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173366400692682207609547697 130024800519511655707160773)
    ·
      refine ⟨24379650097408435445092645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130024800519511655707160773 24379650097408435445092645)
      ·
        refine ⟨4571184393264081645954871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24379650097408435445092645 4571184393264081645954871)
        ·
          refine ⟨6856776589896122468932307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4571184393264081645954871 6856776589896122468932307)
          ·
            refine ⟨10285164884844183703398461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6856776589896122468932307 10285164884844183703398461)
            ·
              refine ⟨3856936831816568888774423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10285164884844183703398461 3856936831816568888774423)
              ·
                refine ⟨5785405247724853333161635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3856936831816568888774423 5785405247724853333161635)
                ·
                  refine ⟨8678107871587279999742453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5785405247724853333161635 8678107871587279999742453)
                  ·
                    refine ⟨813572612961307499975855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8678107871587279999742453 813572612961307499975855)
                    ·
                      rfl

theorem cell23_4753281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_4753281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753281 prefixEnd_4753281 := by exact prefixLift 4753281
  have htrace : WordTrace (prefixWord ++ tailWord_4753281) baseStart_4753281 baseEnd_4753281 := by
    simpa [prefixWord, tailWord_4753281, baseEnd_4753281] using wordTrace_append hprefix tailTrace_4753281
  have hstable : (prefixWord ++ tailWord_4753281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753281).length < 2 ^ (prefixWord ++ tailWord_4753281).sum := by decide
  have hdescent : baseEnd_4753281 < baseStart_4753281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753290 : List Nat := [3, 1, 2, 4, 2, 11]
def baseStart_4753290 : Nat := 118140960795 + 4753290 * 2 ^ 59
def prefixEnd_4753290 : Nat := 4983230072969 + 3 ^ 40 * 4753290 * 2
def baseEnd_4753290 : Nat := 10044125350657666521461

theorem tailTrace_4753290 : CollatzResearch.WordTrace tailWord_4753290 prefixEnd_4753290 10044125350657666521461 := by
  unfold tailWord_4753290
  simp only [CollatzResearch.WordTrace]
  refine ⟨43341682237412400536656331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115577819299766401431083549 43341682237412400536656331)
  ·
    refine ⟨65012523356118600804984497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43341682237412400536656331 65012523356118600804984497)
    ·
      refine ⟨48759392517088950603738373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65012523356118600804984497 48759392517088950603738373)
      ·
        refine ⟨9142386096954178238200945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48759392517088950603738373 9142386096954178238200945)
        ·
          refine ⟨6856789572715633678650709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9142386096954178238200945 6856789572715633678650709)
          ·
            refine ⟨10044125350657666521461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6856789572715633678650709 10044125350657666521461)
            ·
              rfl

theorem cell23_4753290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 11].length) (baseStart_4753290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753290 prefixEnd_4753290 := by exact prefixLift 4753290
  have htrace : WordTrace (prefixWord ++ tailWord_4753290) baseStart_4753290 baseEnd_4753290 := by
    simpa [prefixWord, tailWord_4753290, baseEnd_4753290] using wordTrace_append hprefix tailTrace_4753290
  have hstable : (prefixWord ++ tailWord_4753290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753290).length < 2 ^ (prefixWord ++ tailWord_4753290).sum := by decide
  have hdescent : baseEnd_4753290 < baseStart_4753290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753301 : List Nat := [1, 3, 2, 1, 1, 3, 3, 4, 1, 2, 2]
def baseStart_4753301 : Nat := 118140960795 + 4753301 * 2 ^ 59
def prefixEnd_4753301 : Nat := 4983230072969 + 3 ^ 40 * 4753301 * 2
def baseEnd_4753301 : Nat := 2440728108497012421677473

theorem tailTrace_4753301 : CollatzResearch.WordTrace tailWord_4753301 prefixEnd_4753301 2440728108497012421677473 := by
  unfold tailWord_4753301
  simp only [CollatzResearch.WordTrace]
  refine ⟨173367130152609751025275757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115578086768406500683517171 173367130152609751025275757)
  ·
    refine ⟨65012673807228656634478409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173367130152609751025275757 65012673807228656634478409)
    ·
      refine ⟨48759505355421492475858807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65012673807228656634478409 48759505355421492475858807)
      ·
        refine ⟨73139258033132238713788211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48759505355421492475858807 73139258033132238713788211)
        ·
          refine ⟨109708887049698358070682317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73139258033132238713788211 109708887049698358070682317)
          ·
            refine ⟨41140832643636884276505869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109708887049698358070682317 41140832643636884276505869)
            ·
              refine ⟨15427812241363831603689701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41140832643636884276505869 15427812241363831603689701)
              ·
                refine ⟨2892714795255718425691819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15427812241363831603689701 2892714795255718425691819)
                ·
                  refine ⟨4339072192883577638537729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2892714795255718425691819 4339072192883577638537729)
                  ·
                    refine ⟨3254304144662683228903297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4339072192883577638537729 3254304144662683228903297)
                    ·
                      refine ⟨2440728108497012421677473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3254304144662683228903297 2440728108497012421677473)
                      ·
                        rfl

theorem cell23_4753301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 4, 1, 2, 2].length) (baseStart_4753301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753301 prefixEnd_4753301 := by exact prefixLift 4753301
  have htrace : WordTrace (prefixWord ++ tailWord_4753301) baseStart_4753301 baseEnd_4753301 := by
    simpa [prefixWord, tailWord_4753301, baseEnd_4753301] using wordTrace_append hprefix tailTrace_4753301
  have hstable : (prefixWord ++ tailWord_4753301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753301).length < 2 ^ (prefixWord ++ tailWord_4753301).sum := by decide
  have hdescent : baseEnd_4753301 < baseStart_4753301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753314 : List Nat := [3, 3, 1, 2, 3, 1, 2, 1, 1, 2, 4]
def baseStart_4753314 : Nat := 118140960795 + 4753314 * 2 ^ 59
def prefixEnd_4753314 : Nat := 4983230072969 + 3 ^ 40 * 4753314 * 2
def baseEnd_4753314 : Nat := 2440734783745520870814913

theorem tailTrace_4753314 : CollatzResearch.WordTrace tailWord_4753314 prefixEnd_4753314 2440734783745520870814913 := by
  unfold tailWord_4753314
  simp only [CollatzResearch.WordTrace]
  refine ⟨43341901075390663561374749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115578402867708436163665997 43341901075390663561374749)
  ·
    refine ⟨16253212903271498835515531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43341901075390663561374749 16253212903271498835515531)
    ·
      refine ⟨24379819354907248253273297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16253212903271498835515531 24379819354907248253273297)
      ·
        refine ⟨18284864516180436189954973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24379819354907248253273297 18284864516180436189954973)
        ·
          refine ⟨6856824193567663571233115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18284864516180436189954973 6856824193567663571233115)
          ·
            refine ⟨10285236290351495356849673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6856824193567663571233115 10285236290351495356849673)
            ·
              refine ⟨7713927217763621517637255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10285236290351495356849673 7713927217763621517637255)
              ·
                refine ⟨11570890826645432276455883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7713927217763621517637255 11570890826645432276455883)
                ·
                  refine ⟨17356336239968148414683825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11570890826645432276455883 17356336239968148414683825)
                  ·
                    refine ⟨13017252179976111311012869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17356336239968148414683825 13017252179976111311012869)
                    ·
                      refine ⟨2440734783745520870814913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13017252179976111311012869 2440734783745520870814913)
                      ·
                        rfl

theorem cell23_4753314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_4753314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753314 prefixEnd_4753314 := by exact prefixLift 4753314
  have htrace : WordTrace (prefixWord ++ tailWord_4753314) baseStart_4753314 baseEnd_4753314 := by
    simpa [prefixWord, tailWord_4753314, baseEnd_4753314] using wordTrace_append hprefix tailTrace_4753314
  have hstable : (prefixWord ++ tailWord_4753314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753314).length < 2 ^ (prefixWord ++ tailWord_4753314).sum := by decide
  have hdescent : baseEnd_4753314 < baseStart_4753314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753323 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 10]
def baseStart_4753323 : Nat := 118140960795 + 4753323 * 2 ^ 59
def prefixEnd_4753323 : Nat := 4983230072969 + 3 ^ 40 * 4753323 * 2
def baseEnd_4753323 : Nat := 2440739405071411335602371

theorem tailTrace_4753323 : CollatzResearch.WordTrace tailWord_4753323 prefixEnd_4753323 2440739405071411335602371 := by
  unfold tailWord_4753323
  simp only [CollatzResearch.WordTrace]
  refine ⟨173367932558530048782576623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115578621705686699188384415 173367932558530048782576623)
  ·
    refine ⟨260051898837795073173864935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173367932558530048782576623 260051898837795073173864935)
    ·
      refine ⟨390077848256692609760797403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260051898837795073173864935 390077848256692609760797403)
      ·
        refine ⟨585116772385038914641196105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390077848256692609760797403 585116772385038914641196105)
        ·
          refine ⟨438837579288779185980897079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 585116772385038914641196105 438837579288779185980897079)
          ·
            refine ⟨658256368933168778971345619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 438837579288779185980897079 658256368933168778971345619)
            ·
              refine ⟨987384553399753168457018429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 658256368933168778971345619 987384553399753168457018429)
              ·
                refine ⟨370269207524907438171381911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 987384553399753168457018429 370269207524907438171381911)
                ·
                  refine ⟨555403811287361157257072867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 370269207524907438171381911 555403811287361157257072867)
                  ·
                    refine ⟨833105716931041735885609301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 555403811287361157257072867 833105716931041735885609301)
                    ·
                      refine ⟨2440739405071411335602371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 833105716931041735885609301 2440739405071411335602371)
                      ·
                        rfl

theorem cell23_4753323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 10].length) (baseStart_4753323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753323 prefixEnd_4753323 := by exact prefixLift 4753323
  have htrace : WordTrace (prefixWord ++ tailWord_4753323) baseStart_4753323 baseEnd_4753323 := by
    simpa [prefixWord, tailWord_4753323, baseEnd_4753323] using wordTrace_append hprefix tailTrace_4753323
  have hstable : (prefixWord ++ tailWord_4753323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753323).length < 2 ^ (prefixWord ++ tailWord_4753323).sum := by decide
  have hdescent : baseEnd_4753323 < baseStart_4753323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753327 : List Nat := [1, 1, 2, 1, 2, 2, 3, 3, 3, 3, 2]
def baseStart_4753327 : Nat := 118140960795 + 4753327 * 2 ^ 59
def prefixEnd_4753327 : Nat := 4983230072969 + 3 ^ 40 * 4753327 * 2
def baseEnd_4753327 : Nat := 2440741458994029319952353

theorem tailTrace_4753327 : CollatzResearch.WordTrace tailWord_4753327 prefixEnd_4753327 2440741458994029319952353 := by
  unfold tailWord_4753327
  simp only [CollatzResearch.WordTrace]
  refine ⟨173368078450515557465722235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115578718967010371643814823 173368078450515557465722235)
  ·
    refine ⟨260052117675773336198583353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173368078450515557465722235 260052117675773336198583353)
    ·
      refine ⟨195039088256830002148937515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260052117675773336198583353 195039088256830002148937515)
      ·
        refine ⟨292558632385245003223406273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195039088256830002148937515 292558632385245003223406273)
        ·
          refine ⟨219418974288933752417554705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292558632385245003223406273 219418974288933752417554705)
          ·
            refine ⟨164564230716700314313166029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219418974288933752417554705 164564230716700314313166029)
            ·
              refine ⟨61711586518762617867437261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 164564230716700314313166029 61711586518762617867437261)
              ·
                refine ⟨23141844944535981700288973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61711586518762617867437261 23141844944535981700288973)
                ·
                  refine ⟨8678191854200993137608365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23141844944535981700288973 8678191854200993137608365)
                  ·
                    refine ⟨3254321945325372426603137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8678191854200993137608365 3254321945325372426603137)
                    ·
                      refine ⟨2440741458994029319952353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3254321945325372426603137 2440741458994029319952353)
                      ·
                        rfl

theorem cell23_4753327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 3, 2].length) (baseStart_4753327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753327 prefixEnd_4753327 := by exact prefixLift 4753327
  have htrace : WordTrace (prefixWord ++ tailWord_4753327) baseStart_4753327 baseEnd_4753327 := by
    simpa [prefixWord, tailWord_4753327, baseEnd_4753327] using wordTrace_append hprefix tailTrace_4753327
  have hstable : (prefixWord ++ tailWord_4753327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753327).length < 2 ^ (prefixWord ++ tailWord_4753327).sum := by decide
  have hdescent : baseEnd_4753327 < baseStart_4753327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753344 : List Nat := [2, 1, 1, 2, 3, 2, 3, 3, 1, 3, 2]
def baseStart_4753344 : Nat := 118140960795 + 4753344 * 2 ^ 59
def prefixEnd_4753344 : Nat := 4983230072969 + 3 ^ 40 * 4753344 * 2
def baseEnd_4753344 : Nat := 2440750188165155753439775

theorem tailTrace_4753344 : CollatzResearch.WordTrace tailWord_4753344 prefixEnd_4753344 2440750188165155753439775 := by
  unfold tailWord_4753344
  simp only [CollatzResearch.WordTrace]
  refine ⟨86684349245726984684545543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115579132327635979579394057 86684349245726984684545543)
  ·
    refine ⟨130026523868590477026818315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86684349245726984684545543 130026523868590477026818315)
    ·
      refine ⟨195039785802885715540227473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130026523868590477026818315 195039785802885715540227473)
      ·
        refine ⟨146279839352164286655170605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195039785802885715540227473 146279839352164286655170605)
        ·
          refine ⟨54854939757061607495688977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146279839352164286655170605 54854939757061607495688977)
          ·
            refine ⟨41141204817796205621766733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54854939757061607495688977 41141204817796205621766733)
            ·
              refine ⟨15427951806673577108162525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41141204817796205621766733 15427951806673577108162525)
              ·
                refine ⟨5785481927502591415560947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15427951806673577108162525 5785481927502591415560947)
                ·
                  refine ⟨8678222891253887123341421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5785481927502591415560947 8678222891253887123341421)
                  ·
                    refine ⟨3254333584220207671253033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8678222891253887123341421 3254333584220207671253033)
                    ·
                      refine ⟨2440750188165155753439775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3254333584220207671253033 2440750188165155753439775)
                      ·
                        rfl

theorem cell23_4753344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 1, 3, 2].length) (baseStart_4753344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753344 prefixEnd_4753344 := by exact prefixLift 4753344
  have htrace : WordTrace (prefixWord ++ tailWord_4753344) baseStart_4753344 baseEnd_4753344 := by
    simpa [prefixWord, tailWord_4753344, baseEnd_4753344] using wordTrace_append hprefix tailTrace_4753344
  have hstable : (prefixWord ++ tailWord_4753344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753344).length < 2 ^ (prefixWord ++ tailWord_4753344).sum := by decide
  have hdescent : baseEnd_4753344 < baseStart_4753344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753360 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 3]
def baseStart_4753360 : Nat := 118140960795 + 4753360 * 2 ^ 59
def prefixEnd_4753360 : Nat := 4983230072969 + 3 ^ 40 * 4753360 * 2
def baseEnd_4753360 : Nat := 2440758403855627690839701

theorem tailTrace_4753360 : CollatzResearch.WordTrace tailWord_4753360 prefixEnd_4753360 2440758403855627690839701 := by
  unfold tailWord_4753360
  simp only [CollatzResearch.WordTrace]
  refine ⟨86684641029698002050836767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115579521372930669401115689 86684641029698002050836767)
  ·
    refine ⟨130026961544547003076255151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86684641029698002050836767 130026961544547003076255151)
    ·
      refine ⟨195040442316820504614382727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130026961544547003076255151 195040442316820504614382727)
      ·
        refine ⟨292560663475230756921574091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195040442316820504614382727 292560663475230756921574091)
        ·
          refine ⟨438840995212846135382361137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292560663475230756921574091 438840995212846135382361137)
          ·
            refine ⟨329130746409634601536770853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 438840995212846135382361137 329130746409634601536770853)
            ·
              refine ⟨61712014951806487788144535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 329130746409634601536770853 61712014951806487788144535)
              ·
                refine ⟨92568022427709731682216803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61712014951806487788144535 92568022427709731682216803)
                ·
                  refine ⟨138852033641564597523325205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92568022427709731682216803 138852033641564597523325205)
                  ·
                    refine ⟨6508689076948340508905869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 138852033641564597523325205 6508689076948340508905869)
                    ·
                      refine ⟨2440758403855627690839701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6508689076948340508905869 2440758403855627690839701)
                      ·
                        rfl

theorem cell23_4753360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 3].length) (baseStart_4753360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753360 prefixEnd_4753360 := by exact prefixLift 4753360
  have htrace : WordTrace (prefixWord ++ tailWord_4753360) baseStart_4753360 baseEnd_4753360 := by
    simpa [prefixWord, tailWord_4753360, baseEnd_4753360] using wordTrace_append hprefix tailTrace_4753360
  have hstable : (prefixWord ++ tailWord_4753360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753360).length < 2 ^ (prefixWord ++ tailWord_4753360).sum := by decide
  have hdescent : baseEnd_4753360 < baseStart_4753360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753380 : List Nat := [2, 3, 1, 1, 1, 1, 3, 4, 7]
def baseStart_4753380 : Nat := 118140960795 + 4753380 * 2 ^ 59
def prefixEnd_4753380 : Nat := 4983230072969 + 3 ^ 40 * 4753380 * 2
def baseEnd_4753380 : Nat := 271196519274301956954401

theorem tailTrace_4753380 : CollatzResearch.WordTrace tailWord_4753380 prefixEnd_4753380 271196519274301956954401 := by
  unfold tailWord_4753380
  simp only [CollatzResearch.WordTrace]
  refine ⟨86685005759661773758700797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115580007679549031678267729 86685005759661773758700797)
  ·
    refine ⟨32506877159873165159512799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86685005759661773758700797 32506877159873165159512799)
    ·
      refine ⟨48760315739809747739269199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32506877159873165159512799 48760315739809747739269199)
      ·
        refine ⟨73140473609714621608903799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48760315739809747739269199 73140473609714621608903799)
        ·
          refine ⟨109710710414571932413355699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73140473609714621608903799 109710710414571932413355699)
          ·
            refine ⟨164566065621857898620033549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109710710414571932413355699 164566065621857898620033549)
            ·
              refine ⟨61712274608196711982512581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 164566065621857898620033549 61712274608196711982512581)
              ·
                refine ⟨11571051489036883496721109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61712274608196711982512581 11571051489036883496721109)
                ·
                  refine ⟨271196519274301956954401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11571051489036883496721109 271196519274301956954401)
                  ·
                    rfl

theorem cell23_4753380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 7].length) (baseStart_4753380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753380 prefixEnd_4753380 := by exact prefixLift 4753380
  have htrace : WordTrace (prefixWord ++ tailWord_4753380) baseStart_4753380 baseEnd_4753380 := by
    simpa [prefixWord, tailWord_4753380, baseEnd_4753380] using wordTrace_append hprefix tailTrace_4753380
  have hstable : (prefixWord ++ tailWord_4753380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753380).length < 2 ^ (prefixWord ++ tailWord_4753380).sum := by decide
  have hdescent : baseEnd_4753380 < baseStart_4753380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753501 : List Nat := [1, 4, 4, 1, 1, 2, 1, 1, 1, 4, 3]
def baseStart_4753501 : Nat := 118140960795 + 4753501 * 2 ^ 59
def prefixEnd_4753501 : Nat := 4983230072969 + 3 ^ 40 * 4753501 * 2
def baseEnd_4753501 : Nat := 2440830804627911639176553

theorem tailTrace_4753501 : CollatzResearch.WordTrace tailWord_4753501 prefixEnd_4753501 2440830804627911639176553 := by
  unfold tailWord_4753501
  simp only [CollatzResearch.WordTrace]
  refine ⟨173374424751885185182556357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115582949834590123455037571 173374424751885185182556357)
  ·
    refine ⟨32507704640978472221729317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173374424751885185182556357 32507704640978472221729317)
    ·
      refine ⟨6095194620183463541574247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32507704640978472221729317 6095194620183463541574247)
      ·
        refine ⟨9142791930275195312361371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6095194620183463541574247 9142791930275195312361371)
        ·
          refine ⟨13714187895412792968542057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9142791930275195312361371 13714187895412792968542057)
          ·
            refine ⟨10285640921559594726406543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13714187895412792968542057 10285640921559594726406543)
            ·
              refine ⟨15428461382339392089609815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10285640921559594726406543 15428461382339392089609815)
              ·
                refine ⟨23142692073509088134414723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15428461382339392089609815 23142692073509088134414723)
                ·
                  refine ⟨34714038110263632201622085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23142692073509088134414723 34714038110263632201622085)
                  ·
                    refine ⟨6508882145674431037804141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34714038110263632201622085 6508882145674431037804141)
                    ·
                      refine ⟨2440830804627911639176553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6508882145674431037804141 2440830804627911639176553)
                      ·
                        rfl

theorem cell23_4753501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_4753501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753501 prefixEnd_4753501 := by exact prefixLift 4753501
  have htrace : WordTrace (prefixWord ++ tailWord_4753501) baseStart_4753501 baseEnd_4753501 := by
    simpa [prefixWord, tailWord_4753501, baseEnd_4753501] using wordTrace_append hprefix tailTrace_4753501
  have hstable : (prefixWord ++ tailWord_4753501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753501).length < 2 ^ (prefixWord ++ tailWord_4753501).sum := by decide
  have hdescent : baseEnd_4753501 < baseStart_4753501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753557 : List Nat := [1, 3, 2, 1, 1, 1, 3, 2, 3, 1, 5]
def baseStart_4753557 : Nat := 118140960795 + 4753557 * 2 ^ 59
def prefixEnd_4753557 : Nat := 4983230072969 + 3 ^ 40 * 4753557 * 2
def baseEnd_4753557 : Nat := 2440859559544563420076295

theorem tailTrace_4753557 : CollatzResearch.WordTrace tailWord_4753557 prefixEnd_4753557 2440859559544563420076295 := by
  unfold tailWord_4753557
  simp only [CollatzResearch.WordTrace]
  refine ⟨173376467239682306746594925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115584311493121537831063283 173376467239682306746594925)
  ·
    refine ⟨65016175214880865029973097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173376467239682306746594925 65016175214880865029973097)
    ·
      refine ⟨48762131411160648772479823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65016175214880865029973097 48762131411160648772479823)
      ·
        refine ⟨73143197116740973158719735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48762131411160648772479823 73143197116740973158719735)
        ·
          refine ⟨109714795675111459738079603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73143197116740973158719735 109714795675111459738079603)
          ·
            refine ⟨164572193512667189607119405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109714795675111459738079603 164572193512667189607119405)
            ·
              refine ⟨61714572567250196102669777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 164572193512667189607119405 61714572567250196102669777)
              ·
                refine ⟨46285929425437647077002333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61714572567250196102669777 46285929425437647077002333)
                ·
                  refine ⟨17357223534539117653875875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46285929425437647077002333 17357223534539117653875875)
                  ·
                    refine ⟨26035835301808676480813813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17357223534539117653875875 26035835301808676480813813)
                    ·
                      refine ⟨2440859559544563420076295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26035835301808676480813813 2440859559544563420076295)
                      ·
                        rfl

theorem cell23_4753557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_4753557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753557 prefixEnd_4753557 := by exact prefixLift 4753557
  have htrace : WordTrace (prefixWord ++ tailWord_4753557) baseStart_4753557 baseEnd_4753557 := by
    simpa [prefixWord, tailWord_4753557, baseEnd_4753557] using wordTrace_append hprefix tailTrace_4753557
  have hstable : (prefixWord ++ tailWord_4753557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753557).length < 2 ^ (prefixWord ++ tailWord_4753557).sum := by decide
  have hdescent : baseEnd_4753557 < baseStart_4753557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753564 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 6, 4]
def baseStart_4753564 : Nat := 118140960795 + 4753564 * 2 ^ 59
def prefixEnd_4753564 : Nat := 4983230072969 + 3 ^ 40 * 4753564 * 2
def baseEnd_4753564 : Nat := 813621051303048297562921

theorem tailTrace_4753564 : CollatzResearch.WordTrace tailWord_4753564 prefixEnd_4753564 813621051303048297562921 := by
  unfold tailWord_4753564
  simp only [CollatzResearch.WordTrace]
  refine ⟨86688361275328473471049873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115584481700437964628066497 86688361275328473471049873)
  ·
    refine ⟨65016270956496355103287405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86688361275328473471049873 65016270956496355103287405)
    ·
      refine ⟨24381101608686133163732777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65016270956496355103287405 24381101608686133163732777)
      ·
        refine ⟨18285826206514599872799583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24381101608686133163732777 18285826206514599872799583)
        ·
          refine ⟨27428739309771899809199375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18285826206514599872799583 27428739309771899809199375)
          ·
            refine ⟨41143108964657849713799063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27428739309771899809199375 41143108964657849713799063)
            ·
              refine ⟨61714663446986774570698595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41143108964657849713799063 61714663446986774570698595)
              ·
                refine ⟨92571995170480161856047893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61714663446986774570698595 92571995170480161856047893)
                ·
                  refine ⟨4339312273616257587002245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 92571995170480161856047893 4339312273616257587002245)
                  ·
                    refine ⟨813621051303048297562921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4339312273616257587002245 813621051303048297562921)
                    ·
                      rfl

theorem cell23_4753564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_4753564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753564 prefixEnd_4753564 := by exact prefixLift 4753564
  have htrace : WordTrace (prefixWord ++ tailWord_4753564) baseStart_4753564 baseEnd_4753564 := by
    simpa [prefixWord, tailWord_4753564, baseEnd_4753564] using wordTrace_append hprefix tailTrace_4753564
  have hstable : (prefixWord ++ tailWord_4753564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753564).length < 2 ^ (prefixWord ++ tailWord_4753564).sum := by decide
  have hdescent : baseEnd_4753564 < baseStart_4753564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753565 : List Nat := [1, 4, 2, 1, 1, 5, 1, 3, 1, 1, 3]
def baseStart_4753565 : Nat := 118140960795 + 4753565 * 2 ^ 59
def prefixEnd_4753565 : Nat := 4983230072969 + 3 ^ 40 * 4753565 * 2
def baseEnd_4753565 : Nat := 2440863667389799388776259

theorem tailTrace_4753565 : CollatzResearch.WordTrace tailWord_4753565 prefixEnd_4753565 2440863667389799388776259 := by
  unfold tailWord_4753565
  simp only [CollatzResearch.WordTrace]
  refine ⟨173376759023653324112886149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115584506015768882741924099 173376759023653324112886149)
  ·
    refine ⟨32508142316934998271166153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173376759023653324112886149 32508142316934998271166153)
    ·
      refine ⟨24381106737701248703374615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32508142316934998271166153 24381106737701248703374615)
      ·
        refine ⟨36571660106551873055061923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24381106737701248703374615 36571660106551873055061923)
        ·
          refine ⟨54857490159827809582592885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36571660106551873055061923 54857490159827809582592885)
          ·
            refine ⟨5142889702483857148368083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54857490159827809582592885 5142889702483857148368083)
            ·
              refine ⟨7714334553725785722552125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5142889702483857148368083 7714334553725785722552125)
              ·
                refine ⟨2892875457647169645957047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7714334553725785722552125 2892875457647169645957047)
                ·
                  refine ⟨4339313186470754468935571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2892875457647169645957047 4339313186470754468935571)
                  ·
                    refine ⟨6508969779706131703403357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4339313186470754468935571 6508969779706131703403357)
                    ·
                      refine ⟨2440863667389799388776259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6508969779706131703403357 2440863667389799388776259)
                      ·
                        rfl

theorem cell23_4753565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 3, 1, 1, 3].length) (baseStart_4753565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753565 prefixEnd_4753565 := by exact prefixLift 4753565
  have htrace : WordTrace (prefixWord ++ tailWord_4753565) baseStart_4753565 baseEnd_4753565 := by
    simpa [prefixWord, tailWord_4753565, baseEnd_4753565] using wordTrace_append hprefix tailTrace_4753565
  have hstable : (prefixWord ++ tailWord_4753565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753565).length < 2 ^ (prefixWord ++ tailWord_4753565).sum := by decide
  have hdescent : baseEnd_4753565 < baseStart_4753565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753581 : List Nat := [1, 5, 2, 1, 2, 1, 2, 1, 4, 4]
def baseStart_4753581 : Nat := 118140960795 + 4753581 * 2 ^ 59
def prefixEnd_4753581 : Nat := 4983230072969 + 3 ^ 40 * 4753581 * 2
def baseEnd_4753581 : Nat := 813623961026757108725395

theorem tailTrace_4753581 : CollatzResearch.WordTrace tailWord_4753581 prefixEnd_4753581 813623961026757108725395 := by
  unfold tailWord_4753581
  simp only [CollatzResearch.WordTrace]
  refine ⟨173377342591595358845468597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115584895061063572563645731 173377342591595358845468597)
  ·
    refine ⟨16254125867962064891762681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 173377342591595358845468597 16254125867962064891762681)
    ·
      refine ⟨12190594400971548668822011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16254125867962064891762681 12190594400971548668822011)
      ·
        refine ⟨18285891601457323003233017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12190594400971548668822011 18285891601457323003233017)
        ·
          refine ⟨13714418701092992252424763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18285891601457323003233017 13714418701092992252424763)
          ·
            refine ⟨20571628051639488378637145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13714418701092992252424763 20571628051639488378637145)
            ·
              refine ⟨15428721038729616283977859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20571628051639488378637145 15428721038729616283977859)
              ·
                refine ⟨23143081558094424425966789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15428721038729616283977859 23143081558094424425966789)
                ·
                  refine ⟨4339327792142704579868773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23143081558094424425966789 4339327792142704579868773)
                  ·
                    refine ⟨813623961026757108725395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4339327792142704579868773 813623961026757108725395)
                    ·
                      rfl

theorem cell23_4753581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_4753581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753581 prefixEnd_4753581 := by exact prefixLift 4753581
  have htrace : WordTrace (prefixWord ++ tailWord_4753581) baseStart_4753581 baseEnd_4753581 := by
    simpa [prefixWord, tailWord_4753581, baseEnd_4753581] using wordTrace_append hprefix tailTrace_4753581
  have hstable : (prefixWord ++ tailWord_4753581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753581).length < 2 ^ (prefixWord ++ tailWord_4753581).sum := by decide
  have hdescent : baseEnd_4753581 < baseStart_4753581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753582 : List Nat := [4, 1, 4, 2, 1, 2, 1, 1, 3, 1, 3]
def baseStart_4753582 : Nat := 118140960795 + 4753582 * 2 ^ 59
def prefixEnd_4753582 : Nat := 4983230072969 + 3 ^ 40 * 4753582 * 2
def baseEnd_4753582 : Nat := 2440872396560925822263681

theorem tailTrace_4753582 : CollatzResearch.WordTrace tailWord_4753582 prefixEnd_4753582 2440872396560925822263681 := by
  unfold tailWord_4753582
  simp only [CollatzResearch.WordTrace]
  refine ⟨21672172383073967002031875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115584919376394490677503333 21672172383073967002031875)
  ·
    refine ⟨32508258574610950503047813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21672172383073967002031875 32508258574610950503047813)
    ·
      refine ⟨6095298482739553219321465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32508258574610950503047813 6095298482739553219321465)
      ·
        refine ⟨4571473862054664914491099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6095298482739553219321465 4571473862054664914491099)
        ·
          refine ⟨6857210793081997371736649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4571473862054664914491099 6857210793081997371736649)
          ·
            refine ⟨5142908094811498028802487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6857210793081997371736649 5142908094811498028802487)
            ·
              refine ⟨7714362142217247043203731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5142908094811498028802487 7714362142217247043203731)
              ·
                refine ⟨11571543213325870564805597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7714362142217247043203731 11571543213325870564805597)
                ·
                  refine ⟨4339328704997201461802099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11571543213325870564805597 4339328704997201461802099)
                  ·
                    refine ⟨6508993057495802192703149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4339328704997201461802099 6508993057495802192703149)
                    ·
                      refine ⟨2440872396560925822263681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6508993057495802192703149 2440872396560925822263681)
                      ·
                        rfl

theorem cell23_4753582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_4753582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753582 prefixEnd_4753582 := by exact prefixLift 4753582
  have htrace : WordTrace (prefixWord ++ tailWord_4753582) baseStart_4753582 baseEnd_4753582 := by
    simpa [prefixWord, tailWord_4753582, baseEnd_4753582] using wordTrace_append hprefix tailTrace_4753582
  have hstable : (prefixWord ++ tailWord_4753582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753582).length < 2 ^ (prefixWord ++ tailWord_4753582).sum := by decide
  have hdescent : baseEnd_4753582 < baseStart_4753582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753597 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 1, 4, 6]
def baseStart_4753597 : Nat := 118140960795 + 4753597 * 2 ^ 59
def prefixEnd_4753597 : Nat := 4983230072969 + 3 ^ 40 * 4753597 * 2
def baseEnd_4753597 : Nat := 2440880098770743263576111

theorem tailTrace_4753597 : CollatzResearch.WordTrace tailWord_4753597 prefixEnd_4753597 2440880098770743263576111 := by
  unfold tailWord_4753597
  simp only [CollatzResearch.WordTrace]
  refine ⟨173377926159537393578051045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115585284106358262385367363 173377926159537393578051045)
  ·
    refine ⟨32508361154913261295884571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173377926159537393578051045 32508361154913261295884571)
    ·
      refine ⟨48762541732369891943826857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32508361154913261295884571 48762541732369891943826857)
      ·
        refine ⟨36571906299277418957870143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48762541732369891943826857 36571906299277418957870143)
        ·
          refine ⟨54857859448916128436805215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36571906299277418957870143 54857859448916128436805215)
          ·
            refine ⟨82286789173374192655207823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54857859448916128436805215 82286789173374192655207823)
            ·
              refine ⟨123430183760061288982811735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82286789173374192655207823 123430183760061288982811735)
              ·
                refine ⟨185145275640091933474217603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123430183760061288982811735 185145275640091933474217603)
                ·
                  refine ⟨277717913460137900211326405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 185145275640091933474217603 277717913460137900211326405)
                  ·
                    refine ⟨52072108773775856289623701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 277717913460137900211326405 52072108773775856289623701)
                    ·
                      refine ⟨2440880098770743263576111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52072108773775856289623701 2440880098770743263576111)
                      ·
                        rfl

theorem cell23_4753597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_4753597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753597 prefixEnd_4753597 := by exact prefixLift 4753597
  have htrace : WordTrace (prefixWord ++ tailWord_4753597) baseStart_4753597 baseEnd_4753597 := by
    simpa [prefixWord, tailWord_4753597, baseEnd_4753597] using wordTrace_append hprefix tailTrace_4753597
  have hstable : (prefixWord ++ tailWord_4753597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753597).length < 2 ^ (prefixWord ++ tailWord_4753597).sum := by decide
  have hdescent : baseEnd_4753597 < baseStart_4753597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753598 : List Nat := [4, 2, 1, 1, 4, 1, 1, 3, 2, 4]
def baseStart_4753598 : Nat := 118140960795 + 4753598 * 2 ^ 59
def prefixEnd_4753598 : Nat := 4983230072969 + 3 ^ 40 * 4753598 * 2
def baseEnd_4753598 : Nat := 813626870750465919887869

theorem tailTrace_4753598 : CollatzResearch.WordTrace tailWord_4753598 prefixEnd_4753598 813626870750465919887869 := by
  unfold tailWord_4753598
  simp only [CollatzResearch.WordTrace]
  refine ⟨21672245329066721343604681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115585308421689180499224965 21672245329066721343604681)
  ·
    refine ⟨16254183996800041007703511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21672245329066721343604681 16254183996800041007703511)
    ·
      refine ⟨24381275995200061511555267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16254183996800041007703511 24381275995200061511555267)
      ·
        refine ⟨36571913992800092267332901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24381275995200061511555267 36571913992800092267332901)
        ·
          refine ⟨6857233873650017300124919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36571913992800092267332901 6857233873650017300124919)
          ·
            refine ⟨10285850810475025950187379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6857233873650017300124919 10285850810475025950187379)
            ·
              refine ⟨15428776215712538925281069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10285850810475025950187379 15428776215712538925281069)
              ·
                refine ⟨5785791080892202096980401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15428776215712538925281069 5785791080892202096980401)
                ·
                  refine ⟨4339343310669151572735301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5785791080892202096980401 4339343310669151572735301)
                  ·
                    refine ⟨813626870750465919887869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4339343310669151572735301 813626870750465919887869)
                    ·
                      rfl

theorem cell23_4753598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_4753598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753598 prefixEnd_4753598 := by exact prefixLift 4753598
  have htrace : WordTrace (prefixWord ++ tailWord_4753598) baseStart_4753598 baseEnd_4753598 := by
    simpa [prefixWord, tailWord_4753598, baseEnd_4753598] using wordTrace_append hprefix tailTrace_4753598
  have hstable : (prefixWord ++ tailWord_4753598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753598).length < 2 ^ (prefixWord ++ tailWord_4753598).sum := by decide
  have hdescent : baseEnd_4753598 < baseStart_4753598 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753617 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 1, 4, 5]
def baseStart_4753617 : Nat := 118140960795 + 4753617 * 2 ^ 59
def prefixEnd_4753617 : Nat := 4983230072969 + 3 ^ 40 * 4753617 * 2
def baseEnd_4753617 : Nat := 2440890368383833185326019

theorem tailTrace_4753617 : CollatzResearch.WordTrace tailWord_4753617 prefixEnd_4753617 2440890368383833185326019 := by
  unfold tailWord_4753617
  simp only [CollatzResearch.WordTrace]
  refine ⟨173378655619464936993779105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115585770412976624662519403 173378655619464936993779105)
  ·
    refine ⟨130033991714598702745334329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173378655619464936993779105 130033991714598702745334329)
    ·
      refine ⟨97525493785949027059000747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130033991714598702745334329 97525493785949027059000747)
      ·
        refine ⟨146288240678923540588501121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97525493785949027059000747 146288240678923540588501121)
        ·
          refine ⟨109716180509192655441375841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146288240678923540588501121 109716180509192655441375841)
          ·
            refine ⟨82287135381894491581031881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109716180509192655441375841 82287135381894491581031881)
            ·
              refine ⟨61715351536420868685773911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82287135381894491581031881 61715351536420868685773911)
              ·
                refine ⟨92573027304631303028660867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61715351536420868685773911 92573027304631303028660867)
                ·
                  refine ⟨138859540956946954542991301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92573027304631303028660867 138859540956946954542991301)
                  ·
                    refine ⟨26036163929427553976810869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 138859540956946954542991301 26036163929427553976810869)
                    ·
                      refine ⟨2440890368383833185326019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26036163929427553976810869 2440890368383833185326019)
                      ·
                        rfl

theorem cell23_4753617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_4753617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753617 prefixEnd_4753617 := by exact prefixLift 4753617
  have htrace : WordTrace (prefixWord ++ tailWord_4753617) baseStart_4753617 baseEnd_4753617 := by
    simpa [prefixWord, tailWord_4753617, baseEnd_4753617] using wordTrace_append hprefix tailTrace_4753617
  have hstable : (prefixWord ++ tailWord_4753617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753617).length < 2 ^ (prefixWord ++ tailWord_4753617).sum := by decide
  have hdescent : baseEnd_4753617 < baseStart_4753617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753627 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 1, 5, 4]
def baseStart_4753627 : Nat := 118140960795 + 4753627 * 2 ^ 59
def prefixEnd_4753627 : Nat := 4983230072969 + 3 ^ 40 * 4753627 * 2
def baseEnd_4753627 : Nat := 2440895503190378146200973

theorem tailTrace_4753627 : CollatzResearch.WordTrace tailWord_4753627 prefixEnd_4753627 2440895503190378146200973 := by
  unfold tailWord_4753627
  simp only [CollatzResearch.WordTrace]
  refine ⟨173379020349428708701643135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115586013566285805801095423 173379020349428708701643135)
  ·
    refine ⟨260068530524143063052464703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173379020349428708701643135 260068530524143063052464703)
    ·
      refine ⟨390102795786214594578697055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260068530524143063052464703 390102795786214594578697055)
      ·
        refine ⟨585154193679321891868045583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390102795786214594578697055 585154193679321891868045583)
        ·
          refine ⟨877731290518982837802068375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 585154193679321891868045583 877731290518982837802068375)
          ·
            refine ⟨1316596935778474256703102563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 877731290518982837802068375 1316596935778474256703102563)
            ·
              refine ⟨1974895403667711385054653845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1316596935778474256703102563 1974895403667711385054653845)
              ·
                refine ⟨92573222046923971174436899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1974895403667711385054653845 92573222046923971174436899)
                ·
                  refine ⟨138859833070385956761655349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92573222046923971174436899 138859833070385956761655349)
                  ·
                    refine ⟨13018109350348683446405189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 138859833070385956761655349 13018109350348683446405189)
                    ·
                      refine ⟨2440895503190378146200973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13018109350348683446405189 2440895503190378146200973)
                      ·
                        rfl

theorem cell23_4753627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5, 4].length) (baseStart_4753627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753627 prefixEnd_4753627 := by exact prefixLift 4753627
  have htrace : WordTrace (prefixWord ++ tailWord_4753627) baseStart_4753627 baseEnd_4753627 := by
    simpa [prefixWord, tailWord_4753627, baseEnd_4753627] using wordTrace_append hprefix tailTrace_4753627
  have hstable : (prefixWord ++ tailWord_4753627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753627).length < 2 ^ (prefixWord ++ tailWord_4753627).sum := by decide
  have hdescent : baseEnd_4753627 < baseStart_4753627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753639 : List Nat := [1, 1, 5, 3, 1, 3, 2, 2, 1, 2, 2]
def baseStart_4753639 : Nat := 118140960795 + 4753639 * 2 ^ 59
def prefixEnd_4753639 : Nat := 4983230072969 + 3 ^ 40 * 4753639 * 2
def baseEnd_4753639 : Nat := 2440901664958232099250919

theorem tailTrace_4753639 : CollatzResearch.WordTrace tailWord_4753639 prefixEnd_4753639 2440901664958232099250919 := by
  unfold tailWord_4753639
  simp only [CollatzResearch.WordTrace]
  refine ⟨173379458025385234751079971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115586305350256823167386647 173379458025385234751079971)
  ·
    refine ⟨260069187038077852126619957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173379458025385234751079971 260069187038077852126619957)
    ·
      refine ⟨24381486284819798636870621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 260069187038077852126619957 24381486284819798636870621)
      ·
        refine ⟨9143057356807424488826483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24381486284819798636870621 9143057356807424488826483)
        ·
          refine ⟨13714586035211136733239725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9143057356807424488826483 13714586035211136733239725)
          ·
            refine ⟨5142969763204176274964897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13714586035211136733239725 5142969763204176274964897)
            ·
              refine ⟨3857227322403132206223673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5142969763204176274964897 3857227322403132206223673)
              ·
                refine ⟨2892920491802349154667755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3857227322403132206223673 2892920491802349154667755)
                ·
                  refine ⟨4339380737703523732001633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2892920491802349154667755 4339380737703523732001633)
                  ·
                    refine ⟨3254535553277642799001225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4339380737703523732001633 3254535553277642799001225)
                    ·
                      refine ⟨2440901664958232099250919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3254535553277642799001225 2440901664958232099250919)
                      ·
                        rfl

theorem cell23_4753639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_4753639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753639 prefixEnd_4753639 := by exact prefixLift 4753639
  have htrace : WordTrace (prefixWord ++ tailWord_4753639) baseStart_4753639 baseEnd_4753639 := by
    simpa [prefixWord, tailWord_4753639, baseEnd_4753639] using wordTrace_append hprefix tailTrace_4753639
  have hstable : (prefixWord ++ tailWord_4753639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753639).length < 2 ^ (prefixWord ++ tailWord_4753639).sum := by decide
  have hdescent : baseEnd_4753639 < baseStart_4753639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753654 : List Nat := [5, 1, 1, 1, 1, 1, 3, 1, 1, 8]
def baseStart_4753654 : Nat := 118140960795 + 4753654 * 2 ^ 59
def prefixEnd_4753654 : Nat := 4983230072969 + 3 ^ 40 * 4753654 * 2
def baseEnd_4753654 : Nat := 813636455722683180187783

theorem tailTrace_4753654 : CollatzResearch.WordTrace tailWord_4753654 prefixEnd_4753654 813636455722683180187783 := by
  unfold tailWord_4753654
  simp only [CollatzResearch.WordTrace]
  refine ⟨10836250320020680769554751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115586670080220594875250677 10836250320020680769554751)
  ·
    refine ⟨16254375480031021154332127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10836250320020680769554751 16254375480031021154332127)
    ·
      refine ⟨24381563220046531731498191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16254375480031021154332127 24381563220046531731498191)
      ·
        refine ⟨36572344830069797597247287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24381563220046531731498191 36572344830069797597247287)
        ·
          refine ⟨54858517245104696395870931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36572344830069797597247287 54858517245104696395870931)
          ·
            refine ⟨82287775867657044593806397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54858517245104696395870931 82287775867657044593806397)
            ·
              refine ⟨30857915950371391722677399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82287775867657044593806397 30857915950371391722677399)
              ·
                refine ⟨46286873925557087584016099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30857915950371391722677399 46286873925557087584016099)
                ·
                  refine ⟨69430310888335631376024149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46286873925557087584016099 69430310888335631376024149)
                  ·
                    refine ⟨813636455722683180187783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 69430310888335631376024149 813636455722683180187783)
                    ·
                      rfl

theorem cell23_4753654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_4753654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753654 prefixEnd_4753654 := by exact prefixLift 4753654
  have htrace : WordTrace (prefixWord ++ tailWord_4753654) baseStart_4753654 baseEnd_4753654 := by
    simpa [prefixWord, tailWord_4753654, baseEnd_4753654] using wordTrace_append hprefix tailTrace_4753654
  have hstable : (prefixWord ++ tailWord_4753654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753654).length < 2 ^ (prefixWord ++ tailWord_4753654).sum := by decide
  have hdescent : baseEnd_4753654 < baseStart_4753654 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753678 : List Nat := [4, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2]
def baseStart_4753678 : Nat := 118140960795 + 4753678 * 2 ^ 59
def prefixEnd_4753678 : Nat := 4983230072969 + 3 ^ 40 * 4753678 * 2
def baseEnd_4753678 : Nat := 2440921690703757446663239

theorem tailTrace_4753678 : CollatzResearch.WordTrace tailWord_4753678 prefixEnd_4753678 2440921690703757446663239 := by
  unfold tailWord_4753678
  simp only [CollatzResearch.WordTrace]
  refine ⟨21672610059030493051468711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115587253648162629607833125 21672610059030493051468711)
  ·
    refine ⟨32508915088545739577203067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21672610059030493051468711 32508915088545739577203067)
    ·
      refine ⟨48763372632818609365804601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32508915088545739577203067 48763372632818609365804601)
      ·
        refine ⟨36572529474613957024353451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48763372632818609365804601 36572529474613957024353451)
        ·
          refine ⟨54858794211920935536530177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36572529474613957024353451 54858794211920935536530177)
          ·
            refine ⟨41144095658940701652397633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54858794211920935536530177 41144095658940701652397633)
            ·
              refine ⟨30858071744205526239298225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41144095658940701652397633 30858071744205526239298225)
              ·
                refine ⟨23143553808154144679473669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30858071744205526239298225 23143553808154144679473669)
                ·
                  refine ⟨4339416339028902127401313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23143553808154144679473669 4339416339028902127401313)
                  ·
                    refine ⟨3254562254271676595550985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4339416339028902127401313 3254562254271676595550985)
                    ·
                      refine ⟨2440921690703757446663239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3254562254271676595550985 2440921690703757446663239)
                      ·
                        rfl

theorem cell23_4753678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2].length) (baseStart_4753678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753678 prefixEnd_4753678 := by exact prefixLift 4753678
  have htrace : WordTrace (prefixWord ++ tailWord_4753678) baseStart_4753678 baseEnd_4753678 := by
    simpa [prefixWord, tailWord_4753678, baseEnd_4753678] using wordTrace_append hprefix tailTrace_4753678
  have hstable : (prefixWord ++ tailWord_4753678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753678).length < 2 ^ (prefixWord ++ tailWord_4753678).sum := by decide
  have hdescent : baseEnd_4753678 < baseStart_4753678 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753695 : List Nat := [1, 1, 2, 4, 3, 1, 3, 2, 2, 2, 2]
def baseStart_4753695 : Nat := 118140960795 + 4753695 * 2 ^ 59
def prefixEnd_4753695 : Nat := 4983230072969 + 3 ^ 40 * 4753695 * 2
def baseEnd_4753695 : Nat := 2440930419874883880150661

theorem tailTrace_4753695 : CollatzResearch.WordTrace tailWord_4753695 prefixEnd_4753695 2440930419874883880150661 := by
  unfold tailWord_4753695
  simp only [CollatzResearch.WordTrace]
  refine ⟨173381500513182356315118539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115587667008788237543412359 173381500513182356315118539)
  ·
    refine ⟨260072250769773534472677809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173381500513182356315118539 260072250769773534472677809)
    ·
      refine ⟨195054188077330150854508357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260072250769773534472677809 195054188077330150854508357)
      ·
        refine ⟨36572660264499403285220317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 195054188077330150854508357 36572660264499403285220317)
        ·
          refine ⟨13714747599187276231957619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36572660264499403285220317 13714747599187276231957619)
          ·
            refine ⟨20572121398780914347936429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13714747599187276231957619 20572121398780914347936429)
            ·
              refine ⟨7714545524542842880476161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20572121398780914347936429 7714545524542842880476161)
              ·
                refine ⟨5785909143407132160357121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7714545524542842880476161 5785909143407132160357121)
                ·
                  refine ⟨4339431857555349120267841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5785909143407132160357121 4339431857555349120267841)
                  ·
                    refine ⟨3254573893166511840200881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4339431857555349120267841 3254573893166511840200881)
                    ·
                      refine ⟨2440930419874883880150661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3254573893166511840200881 2440930419874883880150661)
                      ·
                        rfl

theorem cell23_4753695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2, 2, 2, 2].length) (baseStart_4753695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753695 prefixEnd_4753695 := by exact prefixLift 4753695
  have htrace : WordTrace (prefixWord ++ tailWord_4753695) baseStart_4753695 baseEnd_4753695 := by
    simpa [prefixWord, tailWord_4753695, baseEnd_4753695] using wordTrace_append hprefix tailTrace_4753695
  have hstable : (prefixWord ++ tailWord_4753695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753695).length < 2 ^ (prefixWord ++ tailWord_4753695).sum := by decide
  have hdescent : baseEnd_4753695 < baseStart_4753695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753701 : List Nat := [1, 3, 1, 2, 5, 1, 2, 1, 7]
def baseStart_4753701 : Nat := 118140960795 + 4753701 * 2 ^ 59
def prefixEnd_4753701 : Nat := 4983230072969 + 3 ^ 40 * 4753701 * 2
def baseEnd_4753701 : Nat := 271214833417645650741737

theorem tailTrace_4753701 : CollatzResearch.WordTrace tailWord_4753701 prefixEnd_4753701 271214833417645650741737 := by
  unfold tailWord_4753701
  simp only [CollatzResearch.WordTrace]
  refine ⟨173381719351160619339836957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115587812900773746226557971 173381719351160619339836957)
  ·
    refine ⟨65018144756685232252438859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173381719351160619339836957 65018144756685232252438859)
    ·
      refine ⟨97527217135027848378658289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65018144756685232252438859 97527217135027848378658289)
      ·
        refine ⟨73145412851270886283993717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97527217135027848378658289 73145412851270886283993717)
        ·
          refine ⟨6857382454806645589124411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73145412851270886283993717 6857382454806645589124411)
          ·
            refine ⟨10286073682209968383686617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6857382454806645589124411 10286073682209968383686617)
            ·
              refine ⟨7714555261657476287764963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10286073682209968383686617 7714555261657476287764963)
              ·
                refine ⟨11571832892486214431647445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7714555261657476287764963 11571832892486214431647445)
                ·
                  refine ⟨271214833417645650741737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11571832892486214431647445 271214833417645650741737)
                  ·
                    rfl

theorem cell23_4753701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 7].length) (baseStart_4753701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753701 prefixEnd_4753701 := by exact prefixLift 4753701
  have htrace : WordTrace (prefixWord ++ tailWord_4753701) baseStart_4753701 baseEnd_4753701 := by
    simpa [prefixWord, tailWord_4753701, baseEnd_4753701] using wordTrace_append hprefix tailTrace_4753701
  have hstable : (prefixWord ++ tailWord_4753701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753701).length < 2 ^ (prefixWord ++ tailWord_4753701).sum := by decide
  have hdescent : baseEnd_4753701 < baseStart_4753701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753751 : List Nat := [1, 1, 3, 2, 3, 1, 3, 2, 2, 1, 4]
def baseStart_4753751 : Nat := 118140960795 + 4753751 * 2 ^ 59
def prefixEnd_4753751 : Nat := 4983230072969 + 3 ^ 40 * 4753751 * 2
def baseEnd_4753751 : Nat := 2440959174791535661050403

theorem tailTrace_4753751 : CollatzResearch.WordTrace tailWord_4753751 prefixEnd_4753751 2440959174791535661050403 := by
  unfold tailWord_4753751
  simp only [CollatzResearch.WordTrace]
  refine ⟨173383543000979477879157107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115589028667319651919438071 173383543000979477879157107)
  ·
    refine ⟨260075314501469216818735661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173383543000979477879157107 260075314501469216818735661)
    ·
      refine ⟨97528242938050956307025873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 260075314501469216818735661 97528242938050956307025873)
      ·
        refine ⟨73146182203538217230269405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97528242938050956307025873 73146182203538217230269405)
        ·
          refine ⟨27429818326326831461351027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73146182203538217230269405 27429818326326831461351027)
          ·
            refine ⟨41144727489490247192026541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27429818326326831461351027 41144727489490247192026541)
            ·
              refine ⟨15429272808558842697009953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41144727489490247192026541 15429272808558842697009953)
              ·
                refine ⟨11571954606419132022757465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15429272808558842697009953 11571954606419132022757465)
                ·
                  refine ⟨8678965954814349017068099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11571954606419132022757465 8678965954814349017068099)
                  ·
                    refine ⟨13018448932221523525602149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8678965954814349017068099 13018448932221523525602149)
                    ·
                      refine ⟨2440959174791535661050403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13018448932221523525602149 2440959174791535661050403)
                      ·
                        rfl

theorem cell23_4753751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_4753751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753751 prefixEnd_4753751 := by exact prefixLift 4753751
  have htrace : WordTrace (prefixWord ++ tailWord_4753751) baseStart_4753751 baseEnd_4753751 := by
    simpa [prefixWord, tailWord_4753751, baseEnd_4753751] using wordTrace_append hprefix tailTrace_4753751
  have hstable : (prefixWord ++ tailWord_4753751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753751).length < 2 ^ (prefixWord ++ tailWord_4753751).sum := by decide
  have hdescent : baseEnd_4753751 < baseStart_4753751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753812 : List Nat := [2, 4, 2, 1, 3, 1, 1, 4, 1, 4]
def baseStart_4753812 : Nat := 118140960795 + 4753812 * 2 ^ 59
def prefixEnd_4753812 : Nat := 4983230072969 + 3 ^ 40 * 4753812 * 2
def baseEnd_4753812 : Nat := 813663499037153307462541

theorem tailTrace_4753812 : CollatzResearch.WordTrace tailWord_4753812 prefixEnd_4753812 813663499037153307462541 := by
  unfold tailWord_4753812
  simp only [CollatzResearch.WordTrace]
  refine ⟨86692883926879242648563845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115590511902505656864751793 86692883926879242648563845)
  ·
    refine ⟨16254915736289857996605721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86692883926879242648563845 16254915736289857996605721)
    ·
      refine ⟨12191186802217393497454291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16254915736289857996605721 12191186802217393497454291)
      ·
        refine ⟨18286780203326090246181437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12191186802217393497454291 18286780203326090246181437)
        ·
          refine ⟨6857542576247283842318039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18286780203326090246181437 6857542576247283842318039)
          ·
            refine ⟨10286313864370925763477059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6857542576247283842318039 10286313864370925763477059)
            ·
              refine ⟨15429470796556388645215589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10286313864370925763477059 15429470796556388645215589)
              ·
                refine ⟨2893025774354322870977923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15429470796556388645215589 2893025774354322870977923)
                ·
                  refine ⟨4339538661531484306466885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2893025774354322870977923 4339538661531484306466885)
                  ·
                    refine ⟨813663499037153307462541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4339538661531484306466885 813663499037153307462541)
                    ·
                      rfl

theorem cell23_4753812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_4753812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753812 prefixEnd_4753812 := by exact prefixLift 4753812
  have htrace : WordTrace (prefixWord ++ tailWord_4753812) baseStart_4753812 baseEnd_4753812 := by
    simpa [prefixWord, tailWord_4753812, baseEnd_4753812] using wordTrace_append hprefix tailTrace_4753812
  have hstable : (prefixWord ++ tailWord_4753812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753812).length < 2 ^ (prefixWord ++ tailWord_4753812).sum := by decide
  have hdescent : baseEnd_4753812 < baseStart_4753812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753828 : List Nat := [2, 3, 1, 2, 1, 1, 2, 2, 4, 3, 2]
def baseStart_4753828 : Nat := 118140960795 + 4753828 * 2 ^ 59
def prefixEnd_4753828 : Nat := 4983230072969 + 3 ^ 40 * 4753828 * 2
def baseEnd_4753828 : Nat := 2440998712801931859787549

theorem tailTrace_4753828 : CollatzResearch.WordTrace tailWord_4753828 prefixEnd_4753828 2440998712801931859787549 := by
  unfold tailWord_4753828
  simp only [CollatzResearch.WordTrace]
  refine ⟨86693175710850260014855069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115590900947800346686473425 86693175710850260014855069)
  ·
    refine ⟨32509940891568847505570651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86693175710850260014855069 32509940891568847505570651)
    ·
      refine ⟨48764911337353271258355977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32509940891568847505570651 48764911337353271258355977)
      ·
        refine ⟨36573683503014953443766983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48764911337353271258355977 36573683503014953443766983)
        ·
          refine ⟨54860525254522430165650475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36573683503014953443766983 54860525254522430165650475)
          ·
            refine ⟨82290787881783645248475713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54860525254522430165650475 82290787881783645248475713)
            ·
              refine ⟨61718090911337733936356785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82290787881783645248475713 61718090911337733936356785)
              ·
                refine ⟨46288568183503300452267589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61718090911337733936356785 46288568183503300452267589)
                ·
                  refine ⟨8679106534406868834800173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46288568183503300452267589 8679106534406868834800173)
                  ·
                    refine ⟨3254664950402575813050065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8679106534406868834800173 3254664950402575813050065)
                    ·
                      refine ⟨2440998712801931859787549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3254664950402575813050065 2440998712801931859787549)
                      ·
                        rfl

theorem cell23_4753828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 4, 3, 2].length) (baseStart_4753828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753828 prefixEnd_4753828 := by exact prefixLift 4753828
  have htrace : WordTrace (prefixWord ++ tailWord_4753828) baseStart_4753828 baseEnd_4753828 := by
    simpa [prefixWord, tailWord_4753828, baseEnd_4753828] using wordTrace_append hprefix tailTrace_4753828
  have hstable : (prefixWord ++ tailWord_4753828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753828).length < 2 ^ (prefixWord ++ tailWord_4753828).sum := by decide
  have hdescent : baseEnd_4753828 < baseStart_4753828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753845 : List Nat := [1, 3, 3, 2, 3, 1, 1, 1, 1, 5, 2]
def baseStart_4753845 : Nat := 118140960795 + 4753845 * 2 ^ 59
def prefixEnd_4753845 : Nat := 4983230072969 + 3 ^ 40 * 4753845 * 2
def baseEnd_4753845 : Nat := 2441007441973058293274971

theorem tailTrace_4753845 : CollatzResearch.WordTrace tailWord_4753845 prefixEnd_4753845 2441007441973058293274971 := by
  unfold tailWord_4753845
  simp only [CollatzResearch.WordTrace]
  refine ⟨173386971462638931933078989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115591314308425954622052659 173386971462638931933078989)
  ·
    refine ⟨65020114298489599474904621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173386971462638931933078989 65020114298489599474904621)
    ·
      refine ⟨24382542861933599803089233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65020114298489599474904621 24382542861933599803089233)
      ·
        refine ⟨18286907146450199852316925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24382542861933599803089233 18286907146450199852316925)
        ·
          refine ⟨6857590179918824944618847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18286907146450199852316925 6857590179918824944618847)
          ·
            refine ⟨10286385269878237416928271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6857590179918824944618847 10286385269878237416928271)
            ·
              refine ⟨15429577904817356125392407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10286385269878237416928271 15429577904817356125392407)
              ·
                refine ⟨23144366857226034188088611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15429577904817356125392407 23144366857226034188088611)
                ·
                  refine ⟨34716550285839051282132917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23144366857226034188088611 34716550285839051282132917)
                  ·
                    refine ⟨3254676589297411057699961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34716550285839051282132917 3254676589297411057699961)
                    ·
                      refine ⟨2441007441973058293274971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3254676589297411057699961 2441007441973058293274971)
                      ·
                        rfl

theorem cell23_4753845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_4753845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753845 prefixEnd_4753845 := by exact prefixLift 4753845
  have htrace : WordTrace (prefixWord ++ tailWord_4753845) baseStart_4753845 baseEnd_4753845 := by
    simpa [prefixWord, tailWord_4753845, baseEnd_4753845] using wordTrace_append hprefix tailTrace_4753845
  have hstable : (prefixWord ++ tailWord_4753845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753845).length < 2 ^ (prefixWord ++ tailWord_4753845).sum := by decide
  have hdescent : baseEnd_4753845 < baseStart_4753845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753852 : List Nat := [2, 2, 2, 4, 1, 1, 1, 5, 1, 1, 3]
def baseStart_4753852 : Nat := 118140960795 + 4753852 * 2 ^ 59
def prefixEnd_4753852 : Nat := 4983230072969 + 3 ^ 40 * 4753852 * 2
def baseEnd_4753852 : Nat := 2441011036337639765887439

theorem tailTrace_4753852 : CollatzResearch.WordTrace tailWord_4753852 prefixEnd_4753852 2441011036337639765887439 := by
  unfold tailWord_4753852
  simp only [CollatzResearch.WordTrace]
  refine ⟨86693613386806786064291905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115591484515742381419055873 86693613386806786064291905)
  ·
    refine ⟨65020210040105089548218929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86693613386806786064291905 65020210040105089548218929)
    ·
      refine ⟨48765157530078817161164197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65020210040105089548218929 48765157530078817161164197)
      ·
        refine ⟨9143467036889778217718287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48765157530078817161164197 9143467036889778217718287)
        ·
          refine ⟨13715200555334667326577431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9143467036889778217718287 13715200555334667326577431)
          ·
            refine ⟨20572800833002000989866147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13715200555334667326577431 20572800833002000989866147)
            ·
              refine ⟨30859201249503001484799221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20572800833002000989866147 30859201249503001484799221)
              ·
                refine ⟨2893050117140906389199927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30859201249503001484799221 2893050117140906389199927)
                ·
                  refine ⟨4339575175711359583799891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2893050117140906389199927 4339575175711359583799891)
                  ·
                    refine ⟨6509362763567039375699837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4339575175711359583799891 6509362763567039375699837)
                    ·
                      refine ⟨2441011036337639765887439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6509362763567039375699837 2441011036337639765887439)
                      ·
                        rfl

theorem cell23_4753852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_4753852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753852 prefixEnd_4753852 := by exact prefixLift 4753852
  have htrace : WordTrace (prefixWord ++ tailWord_4753852) baseStart_4753852 baseEnd_4753852 := by
    simpa [prefixWord, tailWord_4753852, baseEnd_4753852] using wordTrace_append hprefix tailTrace_4753852
  have hstable : (prefixWord ++ tailWord_4753852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753852).length < 2 ^ (prefixWord ++ tailWord_4753852).sum := by decide
  have hdescent : baseEnd_4753852 < baseStart_4753852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753895 : List Nat := [1, 1, 5, 2, 1, 1, 4, 2, 1, 2, 3]
def baseStart_4753895 : Nat := 118140960795 + 4753895 * 2 ^ 59
def prefixEnd_4753895 : Nat := 4983230072969 + 3 ^ 40 * 4753895 * 2
def baseEnd_4753895 : Nat := 2441033116005783097649741

theorem tailTrace_4753895 : CollatzResearch.WordTrace tailWord_4753895 prefixEnd_4753895 2441033116005783097649741 := by
  unfold tailWord_4753895
  simp only [CollatzResearch.WordTrace]
  refine ⟨173388795112457790472399139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115592530074971860314932759 173388795112457790472399139)
  ·
    refine ⟨260083192668686685708598709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173388795112457790472399139 260083192668686685708598709)
    ·
      refine ⟨24382799312689376785181129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 260083192668686685708598709 24382799312689376785181129)
      ·
        refine ⟨18287099484517032588885847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24382799312689376785181129 18287099484517032588885847)
        ·
          refine ⟨27430649226775548883328771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18287099484517032588885847 27430649226775548883328771)
          ·
            refine ⟨41145973840163323324993157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27430649226775548883328771 41145973840163323324993157)
            ·
              refine ⟨7714870095030623123436217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41145973840163323324993157 7714870095030623123436217)
              ·
                refine ⟨5786152571272967342577163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7714870095030623123436217 5786152571272967342577163)
                ·
                  refine ⟨8679228856909451013865745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5786152571272967342577163 8679228856909451013865745)
                  ·
                    refine ⟨6509421642682088260399309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8679228856909451013865745 6509421642682088260399309)
                    ·
                      refine ⟨2441033116005783097649741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6509421642682088260399309 2441033116005783097649741)
                      ·
                        rfl

theorem cell23_4753895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_4753895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753895 prefixEnd_4753895 := by exact prefixLift 4753895
  have htrace : WordTrace (prefixWord ++ tailWord_4753895) baseStart_4753895 baseEnd_4753895 := by
    simpa [prefixWord, tailWord_4753895, baseEnd_4753895] using wordTrace_append hprefix tailTrace_4753895
  have hstable : (prefixWord ++ tailWord_4753895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753895).length < 2 ^ (prefixWord ++ tailWord_4753895).sum := by decide
  have hdescent : baseEnd_4753895 < baseStart_4753895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753898 : List Nat := [3, 1, 3, 1, 3, 1, 4, 7]
def baseStart_4753898 : Nat := 118140960795 + 4753898 * 2 ^ 59
def prefixEnd_4753898 : Nat := 4983230072969 + 3 ^ 40 * 4753898 * 2
def baseEnd_4753898 : Nat := 90408690979546169848601

theorem tailTrace_4753898 : CollatzResearch.WordTrace tailWord_4753898 prefixEnd_4753898 90408690979546169848601 := by
  unfold tailWord_4753898
  simp only [CollatzResearch.WordTrace]
  refine ⟨43347226132861730496189587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115592603020964614656505565 43347226132861730496189587)
  ·
    refine ⟨65020839199292595744284381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43347226132861730496189587 65020839199292595744284381)
    ·
      refine ⟨24382814699734723404106643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65020839199292595744284381 24382814699734723404106643)
      ·
        refine ⟨36574222049602085106159965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24382814699734723404106643 36574222049602085106159965)
        ·
          refine ⟨13715333268600781914809987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36574222049602085106159965 13715333268600781914809987)
          ·
            refine ⟨20572999902901172872214981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13715333268600781914809987 20572999902901172872214981)
            ·
              refine ⟨3857437481793969913540309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20572999902901172872214981 3857437481793969913540309)
              ·
                refine ⟨90408690979546169848601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3857437481793969913540309 90408690979546169848601)
                ·
                  rfl

theorem cell23_4753898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 7].length) (baseStart_4753898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753898 prefixEnd_4753898 := by exact prefixLift 4753898
  have htrace : WordTrace (prefixWord ++ tailWord_4753898) baseStart_4753898 baseEnd_4753898 := by
    simpa [prefixWord, tailWord_4753898, baseEnd_4753898] using wordTrace_append hprefix tailTrace_4753898
  have hstable : (prefixWord ++ tailWord_4753898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753898).length < 2 ^ (prefixWord ++ tailWord_4753898).sum := by decide
  have hdescent : baseEnd_4753898 < baseStart_4753898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753941 : List Nat := [1, 3, 2, 1, 3, 1, 2, 1, 1, 8]
def baseStart_4753941 : Nat := 118140960795 + 4753941 * 2 ^ 59
def prefixEnd_4753941 : Nat := 4983230072969 + 3 ^ 40 * 4753941 * 2
def baseEnd_4753941 : Nat := 813685578705296639224843

theorem tailTrace_4753941 : CollatzResearch.WordTrace tailWord_4753941 prefixEnd_4753941 813685578705296639224843 := by
  unfold tailWord_4753941
  simp only [CollatzResearch.WordTrace]
  refine ⟨173390472870291140328573677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115593648580194093552382451 173390472870291140328573677)
  ·
    refine ⟨65021427326359177623215129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173390472870291140328573677 65021427326359177623215129)
    ·
      refine ⟨48766070494769383217411347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65021427326359177623215129 48766070494769383217411347)
      ·
        refine ⟨73149105742154074826117021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48766070494769383217411347 73149105742154074826117021)
        ·
          refine ⟨27430914653307778059793883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73149105742154074826117021 27430914653307778059793883)
          ·
            refine ⟨41146371979961667089690825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27430914653307778059793883 41146371979961667089690825)
            ·
              refine ⟨30859778984971250317268119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41146371979961667089690825 30859778984971250317268119)
              ·
                refine ⟨46289668477456875475902179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30859778984971250317268119 46289668477456875475902179)
                ·
                  refine ⟨69434502716185313213853269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46289668477456875475902179 69434502716185313213853269)
                  ·
                    refine ⟨813685578705296639224843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 69434502716185313213853269 813685578705296639224843)
                    ·
                      rfl

theorem cell23_4753941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_4753941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753941 prefixEnd_4753941 := by exact prefixLift 4753941
  have htrace : WordTrace (prefixWord ++ tailWord_4753941) baseStart_4753941 baseEnd_4753941 := by
    simpa [prefixWord, tailWord_4753941, baseEnd_4753941] using wordTrace_append hprefix tailTrace_4753941
  have hstable : (prefixWord ++ tailWord_4753941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753941).length < 2 ^ (prefixWord ++ tailWord_4753941).sum := by decide
  have hdescent : baseEnd_4753941 < baseStart_4753941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753952 : List Nat := [2, 1, 1, 6, 2, 1, 1, 1, 3, 3, 2]
def baseStart_4753952 : Nat := 118140960795 + 4753952 * 2 ^ 59
def prefixEnd_4753952 : Nat := 4983230072969 + 3 ^ 40 * 4753952 * 2
def baseEnd_4753952 : Nat := 2441062384403089374636979

theorem tailTrace_4753952 : CollatzResearch.WordTrace tailWord_4753952 prefixEnd_4753952 2441062384403089374636979 := by
  unfold tailWord_4753952
  simp only [CollatzResearch.WordTrace]
  refine ⟨86695437036625644603612055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115593916048834192804816073 86695437036625644603612055)
  ·
    refine ⟨130043155554938466905418083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86695437036625644603612055 130043155554938466905418083)
    ·
      refine ⟨195064733332407700358127125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130043155554938466905418083 195064733332407700358127125)
      ·
        refine ⟨9143659374956610954287209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 195064733332407700358127125 9143659374956610954287209)
        ·
          refine ⟨6857744531217458215715407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9143659374956610954287209 6857744531217458215715407)
          ·
            refine ⟨10286616796826187323573111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6857744531217458215715407 10286616796826187323573111)
            ·
              refine ⟨15429925195239280985359667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10286616796826187323573111 15429925195239280985359667)
              ·
                refine ⟨23144887792858921478039501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15429925195239280985359667 23144887792858921478039501)
                ·
                  refine ⟨8679332922322095554264813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23144887792858921478039501 8679332922322095554264813)
                  ·
                    refine ⟨3254749845870785832849305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8679332922322095554264813 3254749845870785832849305)
                    ·
                      refine ⟨2441062384403089374636979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3254749845870785832849305 2441062384403089374636979)
                      ·
                        rfl

theorem cell23_4753952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_4753952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753952 prefixEnd_4753952 := by exact prefixLift 4753952
  have htrace : WordTrace (prefixWord ++ tailWord_4753952) baseStart_4753952 baseEnd_4753952 := by
    simpa [prefixWord, tailWord_4753952, baseEnd_4753952] using wordTrace_append hprefix tailTrace_4753952
  have hstable : (prefixWord ++ tailWord_4753952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753952).length < 2 ^ (prefixWord ++ tailWord_4753952).sum := by decide
  have hdescent : baseEnd_4753952 < baseStart_4753952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4753998 : List Nat := [4, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3]
def baseStart_4753998 : Nat := 118140960795 + 4753998 * 2 ^ 59
def prefixEnd_4753998 : Nat := 4983230072969 + 3 ^ 40 * 4753998 * 2
def baseEnd_4753998 : Nat := 2441086004513196194661767

theorem tailTrace_4753998 : CollatzResearch.WordTrace tailWord_4753998 prefixEnd_4753998 2441086004513196194661767 := by
  unfold tailWord_4753998
  simp only [CollatzResearch.WordTrace]
  refine ⟨21674068978885579882924831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115595034554056426042265765 21674068978885579882924831)
  ·
    refine ⟨32511103468328369824387247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21674068978885579882924831 32511103468328369824387247)
    ·
      refine ⟨48766655202492554736580871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32511103468328369824387247 48766655202492554736580871)
      ·
        refine ⟨73149982803738832104871307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48766655202492554736580871 73149982803738832104871307)
        ·
          refine ⟨109724974205608248157306961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73149982803738832104871307 109724974205608248157306961)
          ·
            refine ⟨82293730654206186117980221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109724974205608248157306961 82293730654206186117980221)
            ·
              refine ⟨30860148995327319794242583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82293730654206186117980221 30860148995327319794242583)
              ·
                refine ⟨46290223492990979691363875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30860148995327319794242583 46290223492990979691363875)
                ·
                  refine ⟨69435335239486469537045813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46290223492990979691363875 69435335239486469537045813)
                  ·
                    refine ⟨6509562678701856519098045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 69435335239486469537045813 6509562678701856519098045)
                    ·
                      refine ⟨2441086004513196194661767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6509562678701856519098045 2441086004513196194661767)
                      ·
                        rfl

theorem cell23_4753998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3].length) (baseStart_4753998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4753998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4753998 prefixEnd_4753998 := by exact prefixLift 4753998
  have htrace : WordTrace (prefixWord ++ tailWord_4753998) baseStart_4753998 baseEnd_4753998 := by
    simpa [prefixWord, tailWord_4753998, baseEnd_4753998] using wordTrace_append hprefix tailTrace_4753998
  have hstable : (prefixWord ++ tailWord_4753998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4753998).length < 2 ^ (prefixWord ++ tailWord_4753998).sum := by decide
  have hdescent : baseEnd_4753998 < baseStart_4753998 := by decide
  rcases family_descends (prefixWord ++ tailWord_4753998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4754050 : List Nat := [3, 4, 3, 1, 2, 1, 1, 1, 1, 4, 2]
def baseStart_4754050 : Nat := 118140960795 + 4754050 * 2 ^ 59
def prefixEnd_4754050 : Nat := 4983230072969 + 3 ^ 40 * 4754050 * 2
def baseEnd_4754050 : Nat := 2441112705507229991211529

theorem tailTrace_4754050 : CollatzResearch.WordTrace tailWord_4754050 prefixEnd_4754050 2441112705507229991211529 := by
  unfold tailWord_4754050
  simp only [CollatzResearch.WordTrace]
  refine ⟨43348612106724062986072901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115596298951264167962861069 43348612106724062986072901)
  ·
    refine ⟨8127864770010761809888669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43348612106724062986072901 8127864770010761809888669)
    ·
      refine ⟨3047949288754035678708251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8127864770010761809888669 3047949288754035678708251)
      ·
        refine ⟨4571923933131053518062377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3047949288754035678708251 4571923933131053518062377)
        ·
          refine ⟨3428942949848290138546783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4571923933131053518062377 3428942949848290138546783)
          ·
            refine ⟨5143414424772435207820175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3428942949848290138546783 5143414424772435207820175)
            ·
              refine ⟨7715121637158652811730263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5143414424772435207820175 7715121637158652811730263)
              ·
                refine ⟨11572682455737979217595395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7715121637158652811730263 11572682455737979217595395)
                ·
                  refine ⟨17359023683606968826393093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11572682455737979217595395 17359023683606968826393093)
                  ·
                    refine ⟨3254816940676306654948705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17359023683606968826393093 3254816940676306654948705)
                    ·
                      refine ⟨2441112705507229991211529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3254816940676306654948705 2441112705507229991211529)
                      ·
                        rfl

theorem cell23_4754050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_4754050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4754050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4754050 prefixEnd_4754050 := by exact prefixLift 4754050
  have htrace : WordTrace (prefixWord ++ tailWord_4754050) baseStart_4754050 baseEnd_4754050 := by
    simpa [prefixWord, tailWord_4754050, baseEnd_4754050] using wordTrace_append hprefix tailTrace_4754050
  have hstable : (prefixWord ++ tailWord_4754050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4754050).length < 2 ^ (prefixWord ++ tailWord_4754050).sum := by decide
  have hdescent : baseEnd_4754050 < baseStart_4754050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4754050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4754055 : List Nat := [1, 1, 4, 2, 1, 2, 1, 3, 2, 4, 2]
def baseStart_4754055 : Nat := 118140960795 + 4754055 * 2 ^ 59
def prefixEnd_4754055 : Nat := 4983230072969 + 3 ^ 40 * 4754055 * 2
def baseEnd_4754055 : Nat := 2441115272910502471649005

theorem tailTrace_4754055 : CollatzResearch.WordTrace tailWord_4754055 prefixEnd_4754055 2441115272910502471649005 := by
  unfold tailWord_4754055
  simp only [CollatzResearch.WordTrace]
  refine ⟨173394630791878137798223619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115596420527918758532149079 173394630791878137798223619)
  ·
    refine ⟨260091946187817206697335429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173394630791878137798223619 260091946187817206697335429)
    ·
      refine ⟨48767239910215726255750393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 260091946187817206697335429 48767239910215726255750393)
      ·
        refine ⟨36575429932661794691812795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48767239910215726255750393 36575429932661794691812795)
        ·
          refine ⟨54863144898992692037719193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36575429932661794691812795 54863144898992692037719193)
          ·
            refine ⟨41147358674244519028289395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54863144898992692037719193 41147358674244519028289395)
            ·
              refine ⟨61721038011366778542434093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41147358674244519028289395 61721038011366778542434093)
              ·
                refine ⟨23145389254262541953412785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61721038011366778542434093 23145389254262541953412785)
                ·
                  refine ⟨17359041940696906465059589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23145389254262541953412785 17359041940696906465059589)
                  ·
                    refine ⟨3254820363880669962198673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17359041940696906465059589 3254820363880669962198673)
                    ·
                      refine ⟨2441115272910502471649005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3254820363880669962198673 2441115272910502471649005)
                      ·
                        rfl

theorem cell23_4754055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 4, 2].length) (baseStart_4754055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4754055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4754055 prefixEnd_4754055 := by exact prefixLift 4754055
  have htrace : WordTrace (prefixWord ++ tailWord_4754055) baseStart_4754055 baseEnd_4754055 := by
    simpa [prefixWord, tailWord_4754055, baseEnd_4754055] using wordTrace_append hprefix tailTrace_4754055
  have hstable : (prefixWord ++ tailWord_4754055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4754055).length < 2 ^ (prefixWord ++ tailWord_4754055).sum := by decide
  have hdescent : baseEnd_4754055 < baseStart_4754055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4754055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4754099 : List Nat := [1, 1, 1, 2, 3, 5, 3, 2, 1, 4]
def baseStart_4754099 : Nat := 118140960795 + 4754099 * 2 ^ 59
def prefixEnd_4754099 : Nat := 4983230072969 + 3 ^ 40 * 4754099 * 2
def baseEnd_4754099 : Nat := 813712622019766766499601

theorem tailTrace_4754099 : CollatzResearch.WordTrace tailWord_4754099 prefixEnd_4754099 813712622019766766499601 := by
  unfold tailWord_4754099
  simp only [CollatzResearch.WordTrace]
  refine ⟨173396235603718733312825351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115597490402479155541883567 173396235603718733312825351)
  ·
    refine ⟨260094353405578099969238027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173396235603718733312825351 260094353405578099969238027)
    ·
      refine ⟨390141530108367149953857041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260094353405578099969238027 390141530108367149953857041)
      ·
        refine ⟨292606147581275362465392781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 390141530108367149953857041 292606147581275362465392781)
        ·
          refine ⟨109727305342978260924522293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 292606147581275362465392781 109727305342978260924522293)
          ·
            refine ⟨10286934875904211961673965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 109727305342978260924522293 10286934875904211961673965)
            ·
              refine ⟨3857600578464079485627737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10286934875904211961673965 3857600578464079485627737)
              ·
                refine ⟨2893200433848059614220803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3857600578464079485627737 2893200433848059614220803)
                ·
                  refine ⟨4339800650772089421331205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2893200433848059614220803 4339800650772089421331205)
                  ·
                    refine ⟨813712622019766766499601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4339800650772089421331205 813712622019766766499601)
                    ·
                      rfl

theorem cell23_4754099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 2, 1, 4].length) (baseStart_4754099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4754099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4754099 prefixEnd_4754099 := by exact prefixLift 4754099
  have htrace : WordTrace (prefixWord ++ tailWord_4754099) baseStart_4754099 baseEnd_4754099 := by
    simpa [prefixWord, tailWord_4754099, baseEnd_4754099] using wordTrace_append hprefix tailTrace_4754099
  have hstable : (prefixWord ++ tailWord_4754099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4754099).length < 2 ^ (prefixWord ++ tailWord_4754099).sum := by decide
  have hdescent : baseEnd_4754099 < baseStart_4754099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4754099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4754112 : List Nat := [2, 1, 1, 2, 4, 4, 2, 1, 6]
def baseStart_4754112 : Nat := 118140960795 + 4754112 * 2 ^ 59
def prefixEnd_4754112 : Nat := 4983230072969 + 3 ^ 40 * 4754112 * 2
def baseEnd_4754112 : Nat := 271238282367534305404027

theorem tailTrace_4754112 : CollatzResearch.WordTrace tailWord_4754112 prefixEnd_4754112 271238282367534305404027 := by
  unfold tailWord_4754112
  simp only [CollatzResearch.WordTrace]
  refine ⟨86698354876335818266524295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115597806501781091022032393 86698354876335818266524295)
  ·
    refine ⟨130047532314503727399786443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86698354876335818266524295 130047532314503727399786443)
    ·
      refine ⟨195071298471755591099679665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130047532314503727399786443 195071298471755591099679665)
      ·
        refine ⟨146303473853816693324759749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195071298471755591099679665 146303473853816693324759749)
        ·
          refine ⟨27431901347590629998392453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 146303473853816693324759749 27431901347590629998392453)
          ·
            refine ⟨5143481502673243124698585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27431901347590629998392453 5143481502673243124698585)
            ·
              refine ⟨3857611127004932343523939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5143481502673243124698585 3857611127004932343523939)
              ·
                refine ⟨5786416690507398515285909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3857611127004932343523939 5786416690507398515285909)
                ·
                  refine ⟨271238282367534305404027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5786416690507398515285909 271238282367534305404027)
                  ·
                    rfl

theorem cell23_4754112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 1, 6].length) (baseStart_4754112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4754112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4754112 prefixEnd_4754112 := by exact prefixLift 4754112
  have htrace : WordTrace (prefixWord ++ tailWord_4754112) baseStart_4754112 baseEnd_4754112 := by
    simpa [prefixWord, tailWord_4754112, baseEnd_4754112] using wordTrace_append hprefix tailTrace_4754112
  have hstable : (prefixWord ++ tailWord_4754112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4754112).length < 2 ^ (prefixWord ++ tailWord_4754112).sum := by decide
  have hdescent : baseEnd_4754112 < baseStart_4754112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4754112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4754172 : List Nat := [2, 2, 2, 1, 3, 2, 2, 3, 2, 4]
def baseStart_4754172 : Nat := 118140960795 + 4754172 * 2 ^ 59
def prefixEnd_4754172 : Nat := 4983230072969 + 3 ^ 40 * 4754172 * 2
def baseEnd_4754172 : Nat := 813725116715692837961989

theorem tailTrace_4754172 : CollatzResearch.WordTrace tailWord_4754172 prefixEnd_4754172 813725116715692837961989 := by
  unfold tailWord_4754172
  simp only [CollatzResearch.WordTrace]
  refine ⟨86699449066227133390116385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115599265421636177853488513 86699449066227133390116385)
  ·
    refine ⟨65024586799670350042587289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86699449066227133390116385 65024586799670350042587289)
    ·
      refine ⟨48768440099752762531940467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65024586799670350042587289 48768440099752762531940467)
      ·
        refine ⟨73152660149629143797910701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48768440099752762531940467 73152660149629143797910701)
        ·
          refine ⟨27432247556110928924216513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73152660149629143797910701 27432247556110928924216513)
          ·
            refine ⟨20574185667083196693162385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27432247556110928924216513 20574185667083196693162385)
            ·
              refine ⟨15430639250312397519871789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20574185667083196693162385 15430639250312397519871789)
              ·
                refine ⟨5786489718867149069951921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15430639250312397519871789 5786489718867149069951921)
                ·
                  refine ⟨4339867289150361802463941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5786489718867149069951921 4339867289150361802463941)
                  ·
                    refine ⟨813725116715692837961989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4339867289150361802463941 813725116715692837961989)
                    ·
                      rfl

theorem cell23_4754172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3, 2, 4].length) (baseStart_4754172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4754172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4754172 prefixEnd_4754172 := by exact prefixLift 4754172
  have htrace : WordTrace (prefixWord ++ tailWord_4754172) baseStart_4754172 baseEnd_4754172 := by
    simpa [prefixWord, tailWord_4754172, baseEnd_4754172] using wordTrace_append hprefix tailTrace_4754172
  have hstable : (prefixWord ++ tailWord_4754172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4754172).length < 2 ^ (prefixWord ++ tailWord_4754172).sum := by decide
  have hdescent : baseEnd_4754172 < baseStart_4754172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4754172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4754195 : List Nat := [1, 1, 1, 2, 1, 3, 3, 4, 1, 3, 3]
def baseStart_4754195 : Nat := 118140960795 + 4754195 * 2 ^ 59
def prefixEnd_4754195 : Nat := 4983230072969 + 3 ^ 40 * 4754195 * 2
def baseEnd_4754195 : Nat := 2441187160202131923898361

theorem tailTrace_4754195 : CollatzResearch.WordTrace tailWord_4754195 prefixEnd_4754195 2441187160202131923898361 := by
  unfold tailWord_4754195
  simp only [CollatzResearch.WordTrace]
  refine ⟨173399737011370941708320039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115599824674247294472213359 173399737011370941708320039)
  ·
    refine ⟨260099605517056412562480059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173399737011370941708320039 260099605517056412562480059)
    ·
      refine ⟨390149408275584618843720089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260099605517056412562480059 390149408275584618843720089)
      ·
        refine ⟨292612056206688464132790067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 390149408275584618843720089 292612056206688464132790067)
        ·
          refine ⟨438918084310032696199185101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292612056206688464132790067 438918084310032696199185101)
          ·
            refine ⟨164594281616262261074694413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 438918084310032696199185101 164594281616262261074694413)
            ·
              refine ⟨61722855606098347903010405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 164594281616262261074694413 61722855606098347903010405)
              ·
                refine ⟨11573035426143440231814451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61722855606098347903010405 11573035426143440231814451)
                ·
                  refine ⟨17359553139215160347721677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11573035426143440231814451 17359553139215160347721677)
                  ·
                    refine ⟨6509832427205685130395629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17359553139215160347721677 6509832427205685130395629)
                    ·
                      refine ⟨2441187160202131923898361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6509832427205685130395629 2441187160202131923898361)
                      ·
                        rfl

theorem cell23_4754195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 3, 3].length) (baseStart_4754195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4754195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4754195 prefixEnd_4754195 := by exact prefixLift 4754195
  have htrace : WordTrace (prefixWord ++ tailWord_4754195) baseStart_4754195 baseEnd_4754195 := by
    simpa [prefixWord, tailWord_4754195, baseEnd_4754195] using wordTrace_append hprefix tailTrace_4754195
  have hstable : (prefixWord ++ tailWord_4754195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4754195).length < 2 ^ (prefixWord ++ tailWord_4754195).sum := by decide
  have hdescent : baseEnd_4754195 < baseStart_4754195 := by decide
  rcases family_descends (prefixWord ++ tailWord_4754195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4754199 : List Nat := [1, 1, 3, 4, 3, 1, 1, 3, 1, 2, 3]
def baseStart_4754199 : Nat := 118140960795 + 4754199 * 2 ^ 59
def prefixEnd_4754199 : Nat := 4983230072969 + 3 ^ 40 * 4754199 * 2
def baseEnd_4754199 : Nat := 2441189214124749908248343

theorem tailTrace_4754199 : CollatzResearch.WordTrace tailWord_4754199 prefixEnd_4754199 2441189214124749908248343 := by
  unfold tailWord_4754199
  simp only [CollatzResearch.WordTrace]
  refine ⟨173399882903356450391465651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115599921935570966927643767 173399882903356450391465651)
  ·
    refine ⟨260099824355034675587198477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173399882903356450391465651 260099824355034675587198477)
    ·
      refine ⟨97537434133138003345199429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 260099824355034675587198477 97537434133138003345199429)
      ·
        refine ⟨18288268899963375627224893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97537434133138003345199429 18288268899963375627224893)
        ·
          refine ⟨6858100837486265860209335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18288268899963375627224893 6858100837486265860209335)
          ·
            refine ⟨10287151256229398790314003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6858100837486265860209335 10287151256229398790314003)
            ·
              refine ⟨15430726884344098185471005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10287151256229398790314003 15430726884344098185471005)
              ·
                refine ⟨5786522581629036819551627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15430726884344098185471005 5786522581629036819551627)
                ·
                  refine ⟨8679783872443555229327441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5786522581629036819551627 8679783872443555229327441)
                  ·
                    refine ⟨6509837904332666421995581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8679783872443555229327441 6509837904332666421995581)
                    ·
                      refine ⟨2441189214124749908248343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6509837904332666421995581 2441189214124749908248343)
                      ·
                        rfl

theorem cell23_4754199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_4754199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4754199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4754199 prefixEnd_4754199 := by exact prefixLift 4754199
  have htrace : WordTrace (prefixWord ++ tailWord_4754199) baseStart_4754199 baseEnd_4754199 := by
    simpa [prefixWord, tailWord_4754199, baseEnd_4754199] using wordTrace_append hprefix tailTrace_4754199
  have hstable : (prefixWord ++ tailWord_4754199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4754199).length < 2 ^ (prefixWord ++ tailWord_4754199).sum := by decide
  have hdescent : baseEnd_4754199 < baseStart_4754199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4754199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4754229 : List Nat := [1, 3, 3, 1, 3, 3, 1, 1, 1, 3, 3]
def baseStart_4754229 : Nat := 118140960795 + 4754229 * 2 ^ 59
def prefixEnd_4754229 : Nat := 4983230072969 + 3 ^ 40 * 4754229 * 2
def baseEnd_4754229 : Nat := 2441204618544384790873205

theorem tailTrace_4754229 : CollatzResearch.WordTrace tailWord_4754229 prefixEnd_4754229 2441204618544384790873205 := by
  unfold tailWord_4754229
  simp only [CollatzResearch.WordTrace]
  refine ⟨173400977093247765515057741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115600651395498510343371827 173400977093247765515057741)
  ·
    refine ⟨65025366409967912068146653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173400977093247765515057741 65025366409967912068146653)
    ·
      refine ⟨24384512403737967025554995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65025366409967912068146653 24384512403737967025554995)
      ·
        refine ⟨36576768605606950538332493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24384512403737967025554995 36576768605606950538332493)
        ·
          refine ⟨13716288227102606451874685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36576768605606950538332493 13716288227102606451874685)
          ·
            refine ⟨5143608085163477419453007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13716288227102606451874685 5143608085163477419453007)
            ·
              refine ⟨7715412127745216129179511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5143608085163477419453007 7715412127745216129179511)
              ·
                refine ⟨11573118191617824193769267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7715412127745216129179511 11573118191617824193769267)
                ·
                  refine ⟨17359677287426736290653901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11573118191617824193769267 17359677287426736290653901)
                  ·
                    refine ⟨6509878982785026108995213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17359677287426736290653901 6509878982785026108995213)
                    ·
                      refine ⟨2441204618544384790873205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6509878982785026108995213 2441204618544384790873205)
                      ·
                        rfl

theorem cell23_4754229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_4754229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4754229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4754229 prefixEnd_4754229 := by exact prefixLift 4754229
  have htrace : WordTrace (prefixWord ++ tailWord_4754229) baseStart_4754229 baseEnd_4754229 := by
    simpa [prefixWord, tailWord_4754229, baseEnd_4754229] using wordTrace_append hprefix tailTrace_4754229
  have hstable : (prefixWord ++ tailWord_4754229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4754229).length < 2 ^ (prefixWord ++ tailWord_4754229).sum := by decide
  have hdescent : baseEnd_4754229 < baseStart_4754229 := by decide
  rcases family_descends (prefixWord ++ tailWord_4754229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4754239 : List Nat := [1, 1, 2, 2, 5, 1, 1, 4, 1, 3, 2]
def baseStart_4754239 : Nat := 118140960795 + 4754239 * 2 ^ 59
def prefixEnd_4754239 : Nat := 4983230072969 + 3 ^ 40 * 4754239 * 2
def baseEnd_4754239 : Nat := 2441209753350929751748159

theorem tailTrace_4754239 : CollatzResearch.WordTrace tailWord_4754239 prefixEnd_4754239 2441209753350929751748159 := by
  unfold tailWord_4754239
  simp only [CollatzResearch.WordTrace]
  refine ⟨173401341823211537222921771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115600894548807691481947847 173401341823211537222921771)
  ·
    refine ⟨260102012734817305834382657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173401341823211537222921771 260102012734817305834382657)
    ·
      refine ⟨195076509551112979375786993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260102012734817305834382657 195076509551112979375786993)
      ·
        refine ⟨146307382163334734531840245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195076509551112979375786993 146307382163334734531840245)
        ·
          refine ⟨13716317077812631362360023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 146307382163334734531840245 13716317077812631362360023)
          ·
            refine ⟨20574475616718947043540035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13716317077812631362360023 20574475616718947043540035)
            ·
              refine ⟨30861713425078420565310053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20574475616718947043540035 30861713425078420565310053)
              ·
                refine ⟨5786571267202203855995635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30861713425078420565310053 5786571267202203855995635)
                ·
                  refine ⟨8679856900803305783993453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5786571267202203855995635 8679856900803305783993453)
                  ·
                    refine ⟨3254946337801239668997545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8679856900803305783993453 3254946337801239668997545)
                    ·
                      refine ⟨2441209753350929751748159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3254946337801239668997545 2441209753350929751748159)
                      ·
                        rfl

theorem cell23_4754239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4, 1, 3, 2].length) (baseStart_4754239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4754239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4754239 prefixEnd_4754239 := by exact prefixLift 4754239
  have htrace : WordTrace (prefixWord ++ tailWord_4754239) baseStart_4754239 baseEnd_4754239 := by
    simpa [prefixWord, tailWord_4754239, baseEnd_4754239] using wordTrace_append hprefix tailTrace_4754239
  have hstable : (prefixWord ++ tailWord_4754239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4754239).length < 2 ^ (prefixWord ++ tailWord_4754239).sum := by decide
  have hdescent : baseEnd_4754239 < baseStart_4754239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4754239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4754315 : List Nat := [1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 5]
def baseStart_4754315 : Nat := 118140960795 + 4754315 * 2 ^ 59
def prefixEnd_4754315 : Nat := 4983230072969 + 3 ^ 40 * 4754315 * 2
def baseEnd_4754315 : Nat := 2441248777880671454397809

theorem tailTrace_4754315 : CollatzResearch.WordTrace tailWord_4754315 prefixEnd_4754315 2441248777880671454397809 := by
  unfold tailWord_4754315
  simp only [CollatzResearch.WordTrace]
  refine ⟨173404113770936202202688399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115602742513957468135125599 173404113770936202202688399)
  ·
    refine ⟨260106170656404303304032599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173404113770936202202688399 260106170656404303304032599)
    ·
      refine ⟨390159255984606454956048899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260106170656404303304032599 390159255984606454956048899)
      ·
        refine ⟨585238883976909682434073349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390159255984606454956048899 585238883976909682434073349)
        ·
          refine ⟨109732290745670565456388753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 585238883976909682434073349 109732290745670565456388753)
          ·
            refine ⟨82299218059252924092291565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109732290745670565456388753 82299218059252924092291565)
            ·
              refine ⟨30862206772219846534609337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82299218059252924092291565 30862206772219846534609337)
              ·
                refine ⟨23146655079164884900957003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30862206772219846534609337 23146655079164884900957003)
                ·
                  refine ⟨34719982618747327351435505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23146655079164884900957003 34719982618747327351435505)
                  ·
                    refine ⟨26039986964060495513576629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34719982618747327351435505 26039986964060495513576629)
                    ·
                      refine ⟨2441248777880671454397809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26039986964060495513576629 2441248777880671454397809)
                      ·
                        rfl

theorem cell23_4754315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 5].length) (baseStart_4754315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4754315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4754315 prefixEnd_4754315 := by exact prefixLift 4754315
  have htrace : WordTrace (prefixWord ++ tailWord_4754315) baseStart_4754315 baseEnd_4754315 := by
    simpa [prefixWord, tailWord_4754315, baseEnd_4754315] using wordTrace_append hprefix tailTrace_4754315
  have hstable : (prefixWord ++ tailWord_4754315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4754315).length < 2 ^ (prefixWord ++ tailWord_4754315).sum := by decide
  have hdescent : baseEnd_4754315 < baseStart_4754315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4754315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4754355 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 1, 6, 4]
def baseStart_4754355 : Nat := 118140960795 + 4754355 * 2 ^ 59
def prefixEnd_4754355 : Nat := 4983230072969 + 3 ^ 40 * 4754355 * 2
def baseEnd_4754355 : Nat := 2441269317106851297897625

theorem tailTrace_4754355 : CollatzResearch.WordTrace tailWord_4754355 prefixEnd_4754355 2441269317106851297897625 := by
  unfold tailWord_4754355
  simp only [CollatzResearch.WordTrace]
  refine ⟨173405572690791289034144519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115603715127194192689429679 173405572690791289034144519)
  ·
    refine ⟨260108359036186933551216779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173405572690791289034144519 260108359036186933551216779)
    ·
      refine ⟨390162538554280400326825169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260108359036186933551216779 390162538554280400326825169)
      ·
        refine ⟨292621903915710300245118877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 390162538554280400326825169 292621903915710300245118877)
        ·
          refine ⟨109733213968391362591919579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 292621903915710300245118877 109733213968391362591919579)
          ·
            refine ⟨164599820952587043887879369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109733213968391362591919579 164599820952587043887879369)
            ·
              refine ⟨123449865714440282915909527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164599820952587043887879369 123449865714440282915909527)
              ·
                refine ⟨185174798571660424373864291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123449865714440282915909527 185174798571660424373864291)
                ·
                  refine ⟨277762197857490636560796437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 185174798571660424373864291 277762197857490636560796437)
                  ·
                    refine ⟨13020103024569873588787333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 277762197857490636560796437 13020103024569873588787333)
                    ·
                      refine ⟨2441269317106851297897625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13020103024569873588787333 2441269317106851297897625)
                      ·
                        rfl

theorem cell23_4754355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6, 4].length) (baseStart_4754355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4754355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4754355 prefixEnd_4754355 := by exact prefixLift 4754355
  have htrace : WordTrace (prefixWord ++ tailWord_4754355) baseStart_4754355 baseEnd_4754355 := by
    simpa [prefixWord, tailWord_4754355, baseEnd_4754355] using wordTrace_append hprefix tailTrace_4754355
  have hstable : (prefixWord ++ tailWord_4754355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4754355).length < 2 ^ (prefixWord ++ tailWord_4754355).sum := by decide
  have hdescent : baseEnd_4754355 < baseStart_4754355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4754355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4754356 : List Nat := [2, 5, 2, 1, 1, 1, 3, 1, 2, 5]
def baseStart_4754356 : Nat := 118140960795 + 4754356 * 2 ^ 59
def prefixEnd_4754356 : Nat := 4983230072969 + 3 ^ 40 * 4754356 * 2
def baseEnd_4754356 : Nat := 813756610195835264661707

theorem tailTrace_4754356 : CollatzResearch.WordTrace tailWord_4754356 prefixEnd_4754356 813756610195835264661707 := by
  unfold tailWord_4754356
  simp only [CollatzResearch.WordTrace]
  refine ⟨86702804581893833102465461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115603739442525110803287281 86702804581893833102465461)
  ·
    refine ⟨8128387929552546853356137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86702804581893833102465461 8128387929552546853356137)
    ·
      refine ⟨6096290947164410140017103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8128387929552546853356137 6096290947164410140017103)
      ·
        refine ⟨9144436420746615210025655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6096290947164410140017103 9144436420746615210025655)
        ·
          refine ⟨13716654631119922815038483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9144436420746615210025655 13716654631119922815038483)
          ·
            refine ⟨20574981946679884222557725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13716654631119922815038483 20574981946679884222557725)
            ·
              refine ⟨7715618230004956583459147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20574981946679884222557725 7715618230004956583459147)
              ·
                refine ⟨11573427345007434875188721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7715618230004956583459147 11573427345007434875188721)
                ·
                  refine ⟨8680070508755576156391541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11573427345007434875188721 8680070508755576156391541)
                  ·
                    refine ⟨813756610195835264661707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8680070508755576156391541 813756610195835264661707)
                    ·
                      rfl

theorem cell23_4754356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_4754356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4754356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4754356 prefixEnd_4754356 := by exact prefixLift 4754356
  have htrace : WordTrace (prefixWord ++ tailWord_4754356) baseStart_4754356 baseEnd_4754356 := by
    simpa [prefixWord, tailWord_4754356, baseEnd_4754356] using wordTrace_append hprefix tailTrace_4754356
  have hstable : (prefixWord ++ tailWord_4754356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4754356).length < 2 ^ (prefixWord ++ tailWord_4754356).sum := by decide
  have hdescent : baseEnd_4754356 < baseStart_4754356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4754356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4754362 : List Nat := [3, 1, 1, 1, 2, 1, 5, 1, 1, 4, 3]
def baseStart_4754362 : Nat := 118140960795 + 4754362 * 2 ^ 59
def prefixEnd_4754362 : Nat := 4983230072969 + 3 ^ 40 * 4754362 * 2
def baseEnd_4754362 : Nat := 2441272911471432770510093

theorem tailTrace_4754362 : CollatzResearch.WordTrace tailWord_4754362 prefixEnd_4754362 2441272911471432770510093 := by
  unfold tailWord_4754362
  simp only [CollatzResearch.WordTrace]
  refine ⟨43351457000441482307412335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115603885334510619486432893 43351457000441482307412335)
  ·
    refine ⟨65027185500662223461118503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43351457000441482307412335 65027185500662223461118503)
    ·
      refine ⟨97540778250993335191677755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65027185500662223461118503 97540778250993335191677755)
      ·
        refine ⟨146311167376490002787516633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97540778250993335191677755 146311167376490002787516633)
        ·
          refine ⟨109733375532367502090637475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146311167376490002787516633 109733375532367502090637475)
          ·
            refine ⟨164600063298551253135956213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109733375532367502090637475 164600063298551253135956213)
            ·
              refine ⟨15431255934239179981495895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 164600063298551253135956213 15431255934239179981495895)
              ·
                refine ⟨23146883901358769972243843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15431255934239179981495895 23146883901358769972243843)
                ·
                  refine ⟨34720325852038154958365765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23146883901358769972243843 34720325852038154958365765)
                  ·
                    refine ⟨6510061097257154054693581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34720325852038154958365765 6510061097257154054693581)
                    ·
                      refine ⟨2441272911471432770510093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6510061097257154054693581 2441272911471432770510093)
                      ·
                        rfl

theorem cell23_4754362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 1, 4, 3].length) (baseStart_4754362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4754362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4754362 prefixEnd_4754362 := by exact prefixLift 4754362
  have htrace : WordTrace (prefixWord ++ tailWord_4754362) baseStart_4754362 baseEnd_4754362 := by
    simpa [prefixWord, tailWord_4754362, baseEnd_4754362] using wordTrace_append hprefix tailTrace_4754362
  have hstable : (prefixWord ++ tailWord_4754362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4754362).length < 2 ^ (prefixWord ++ tailWord_4754362).sum := by decide
  have hdescent : baseEnd_4754362 < baseStart_4754362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4754362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4754382 : List Nat := [4, 1, 1, 1, 2, 4, 1, 1, 8]
def baseStart_4754382 : Nat := 118140960795 + 4754382 * 2 ^ 59
def prefixEnd_4754382 : Nat := 4983230072969 + 3 ^ 40 * 4754382 * 2
def baseEnd_4754382 : Nat := 271253686787169188028889

theorem tailTrace_4754382 : CollatzResearch.WordTrace tailWord_4754382 prefixEnd_4754382 271253686787169188028889 := by
  unfold tailWord_4754382
  simp only [CollatzResearch.WordTrace]
  refine ⟨21675819682711684080672175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115604371641128981763584933 21675819682711684080672175)
  ·
    refine ⟨32513729524067526121008263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21675819682711684080672175 32513729524067526121008263)
    ·
      refine ⟨48770594286101289181512395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32513729524067526121008263 48770594286101289181512395)
      ·
        refine ⟨73155891429151933772268593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48770594286101289181512395 73155891429151933772268593)
        ·
          refine ⟨54866918571863950329201445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73155891429151933772268593 54866918571863950329201445)
          ·
            refine ⟨10287547232224490686725271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54866918571863950329201445 10287547232224490686725271)
            ·
              refine ⟨15431320848336736030087907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10287547232224490686725271 15431320848336736030087907)
              ·
                refine ⟨23146981272505104045131861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15431320848336736030087907 23146981272505104045131861)
                ·
                  refine ⟨271253686787169188028889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23146981272505104045131861 271253686787169188028889)
                  ·
                    rfl

theorem cell23_4754382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 8].length) (baseStart_4754382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4754382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4754382 prefixEnd_4754382 := by exact prefixLift 4754382
  have htrace : WordTrace (prefixWord ++ tailWord_4754382) baseStart_4754382 baseEnd_4754382 := by
    simpa [prefixWord, tailWord_4754382, baseEnd_4754382] using wordTrace_append hprefix tailTrace_4754382
  have hstable : (prefixWord ++ tailWord_4754382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4754382).length < 2 ^ (prefixWord ++ tailWord_4754382).sum := by decide
  have hdescent : baseEnd_4754382 < baseStart_4754382 := by decide
  rcases family_descends (prefixWord ++ tailWord_4754382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4754385 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 1, 1, 8]
def baseStart_4754385 : Nat := 118140960795 + 4754385 * 2 ^ 59
def prefixEnd_4754385 : Nat := 4983230072969 + 3 ^ 40 * 4754385 * 2
def baseEnd_4754385 : Nat := 2441284721526486180522487

theorem tailTrace_4754385 : CollatzResearch.WordTrace tailWord_4754385 prefixEnd_4754385 2441284721526486180522487 := by
  unfold tailWord_4754385
  simp only [CollatzResearch.WordTrace]
  refine ⟨173406666880682604157736609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115604444587121736105157739 173406666880682604157736609)
  ·
    refine ⟨130055000160511953118302457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173406666880682604157736609 130055000160511953118302457)
    ·
      refine ⟨97541250120383964838726843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130055000160511953118302457 97541250120383964838726843)
      ·
        refine ⟨146311875180575947258090265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97541250120383964838726843 146311875180575947258090265)
        ·
          refine ⟨109733906385431960443567699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146311875180575947258090265 109733906385431960443567699)
          ·
            refine ⟨164600859578147940665351549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109733906385431960443567699 164600859578147940665351549)
            ·
              refine ⟨61725322341805477749506831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 164600859578147940665351549 61725322341805477749506831)
              ·
                refine ⟨92587983512708216624260247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61725322341805477749506831 92587983512708216624260247)
                ·
                  refine ⟨138881975269062324936390371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92587983512708216624260247 138881975269062324936390371)
                  ·
                    refine ⟨208322962903593487404585557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 138881975269062324936390371 208322962903593487404585557)
                    ·
                      refine ⟨2441284721526486180522487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 208322962903593487404585557 2441284721526486180522487)
                      ·
                        rfl

theorem cell23_4754385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_4754385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4754385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4754385 prefixEnd_4754385 := by exact prefixLift 4754385
  have htrace : WordTrace (prefixWord ++ tailWord_4754385) baseStart_4754385 baseEnd_4754385 := by
    simpa [prefixWord, tailWord_4754385, baseEnd_4754385] using wordTrace_append hprefix tailTrace_4754385
  have hstable : (prefixWord ++ tailWord_4754385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4754385).length < 2 ^ (prefixWord ++ tailWord_4754385).sum := by decide
  have hdescent : baseEnd_4754385 < baseStart_4754385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4754385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4754386 : List Nat := [3, 2, 2, 3, 1, 2, 2, 1, 3, 4]
def baseStart_4754386 : Nat := 118140960795 + 4754386 * 2 ^ 59
def prefixEnd_4754386 : Nat := 4983230072969 + 3 ^ 40 * 4754386 * 2
def baseEnd_4754386 : Nat := 813761745002380225536661

theorem tailTrace_4754386 : CollatzResearch.WordTrace tailWord_4754386 prefixEnd_4754386 813761745002380225536661 := by
  unfold tailWord_4754386
  simp only [CollatzResearch.WordTrace]
  refine ⟨43351675838419745332130753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115604468902452654219015341 43351675838419745332130753)
  ·
    refine ⟨32513756878814808999098065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43351675838419745332130753 32513756878814808999098065)
    ·
      refine ⟨24385317659111106749323549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32513756878814808999098065 24385317659111106749323549)
      ·
        refine ⟨9144494122166665030996331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24385317659111106749323549 9144494122166665030996331)
        ·
          refine ⟨13716741183249997546494497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9144494122166665030996331 13716741183249997546494497)
          ·
            refine ⟨10287555887437498159870873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13716741183249997546494497 10287555887437498159870873)
            ·
              refine ⟨7715666915578123619903155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10287555887437498159870873 7715666915578123619903155)
              ·
                refine ⟨11573500373367185429854733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7715666915578123619903155 11573500373367185429854733)
                ·
                  refine ⟨4340062640012694536195525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11573500373367185429854733 4340062640012694536195525)
                  ·
                    refine ⟨813761745002380225536661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4340062640012694536195525 813761745002380225536661)
                    ·
                      rfl

theorem cell23_4754386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_4754386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4754386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4754386 prefixEnd_4754386 := by exact prefixLift 4754386
  have htrace : WordTrace (prefixWord ++ tailWord_4754386) baseStart_4754386 baseEnd_4754386 := by
    simpa [prefixWord, tailWord_4754386, baseEnd_4754386] using wordTrace_append hprefix tailTrace_4754386
  have hstable : (prefixWord ++ tailWord_4754386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4754386).length < 2 ^ (prefixWord ++ tailWord_4754386).sum := by decide
  have hdescent : baseEnd_4754386 < baseStart_4754386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4754386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4754466 : List Nat := [3, 3, 1, 1, 1, 3, 3, 2, 1, 1, 4]
def baseStart_4754466 : Nat := 118140960795 + 4754466 * 2 ^ 59
def prefixEnd_4754466 : Nat := 4983230072969 + 3 ^ 40 * 4754466 * 2
def baseEnd_4754466 : Nat := 2441326313459500363609615

theorem tailTrace_4754466 : CollatzResearch.WordTrace tailWord_4754466 prefixEnd_4754466 2441326313459500363609615 := by
  unfold tailWord_4754466
  simp only [CollatzResearch.WordTrace]
  refine ⟨43352405298347288747858813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115606414128926103327623501 43352405298347288747858813)
  ·
    refine ⟨16257151986880233280447055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43352405298347288747858813 16257151986880233280447055)
    ·
      refine ⟨24385727980320349920670583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16257151986880233280447055 24385727980320349920670583)
      ·
        refine ⟨36578591970480524881005875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24385727980320349920670583 36578591970480524881005875)
        ·
          refine ⟨54867887955720787321508813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36578591970480524881005875 54867887955720787321508813)
          ·
            refine ⟨20575457983395295245565805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54867887955720787321508813 20575457983395295245565805)
            ·
              refine ⟨7715796743773235717087177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20575457983395295245565805 7715796743773235717087177)
              ·
                refine ⟨5786847557829926787815383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7715796743773235717087177 5786847557829926787815383)
                ·
                  refine ⟨8680271336744890181723075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5786847557829926787815383 8680271336744890181723075)
                  ·
                    refine ⟨13020407005117335272584613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8680271336744890181723075 13020407005117335272584613)
                    ·
                      refine ⟨2441326313459500363609615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13020407005117335272584613 2441326313459500363609615)
                      ·
                        rfl

theorem cell23_4754466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_4754466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4754466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4754466 prefixEnd_4754466 := by exact prefixLift 4754466
  have htrace : WordTrace (prefixWord ++ tailWord_4754466) baseStart_4754466 baseEnd_4754466 := by
    simpa [prefixWord, tailWord_4754466, baseEnd_4754466] using wordTrace_append hprefix tailTrace_4754466
  have hstable : (prefixWord ++ tailWord_4754466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4754466).length < 2 ^ (prefixWord ++ tailWord_4754466).sum := by decide
  have hdescent : baseEnd_4754466 < baseStart_4754466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4754466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4754469 : List Nat := [1, 3, 1, 2, 2, 2, 3, 1, 3, 2, 3]
def baseStart_4754469 : Nat := 118140960795 + 4754469 * 2 ^ 59
def prefixEnd_4754469 : Nat := 4983230072969 + 3 ^ 40 * 4754469 * 2
def baseEnd_4754469 : Nat := 2441327853901463851872101

theorem tailTrace_4754469 : CollatzResearch.WordTrace tailWord_4754469 prefixEnd_4754469 2441327853901463851872101 := by
  unfold tailWord_4754469
  simp only [CollatzResearch.WordTrace]
  refine ⟨173409730612378286503794461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115606487074918857669196307 173409730612378286503794461)
  ·
    refine ⟨65028648979641857438922923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173409730612378286503794461 65028648979641857438922923)
    ·
      refine ⟨97542973469462786158384385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65028648979641857438922923 97542973469462786158384385)
      ·
        refine ⟨73157230102097089618788289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97542973469462786158384385 73157230102097089618788289)
        ·
          refine ⟨54867922576572817214091217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73157230102097089618788289 54867922576572817214091217)
          ·
            refine ⟨41150941932429612910568413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54867922576572817214091217 41150941932429612910568413)
            ·
              refine ⟨15431603224661104841463155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41150941932429612910568413 15431603224661104841463155)
              ·
                refine ⟨23147404836991657262194733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15431603224661104841463155 23147404836991657262194733)
                ·
                  refine ⟨8680276813871871473323025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23147404836991657262194733 8680276813871871473323025)
                  ·
                    refine ⟨6510207610403903604992269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8680276813871871473323025 6510207610403903604992269)
                    ·
                      refine ⟨2441327853901463851872101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6510207610403903604992269 2441327853901463851872101)
                      ·
                        rfl

theorem cell23_4754469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3, 2, 3].length) (baseStart_4754469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4754469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4754469 prefixEnd_4754469 := by exact prefixLift 4754469
  have htrace : WordTrace (prefixWord ++ tailWord_4754469) baseStart_4754469 baseEnd_4754469 := by
    simpa [prefixWord, tailWord_4754469, baseEnd_4754469] using wordTrace_append hprefix tailTrace_4754469
  have hstable : (prefixWord ++ tailWord_4754469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4754469).length < 2 ^ (prefixWord ++ tailWord_4754469).sum := by decide
  have hdescent : baseEnd_4754469 < baseStart_4754469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4754469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4754483 : List Nat := [1, 1, 1, 2, 4, 1, 1, 7, 1, 2, 2]
def baseStart_4754483 : Nat := 118140960795 + 4754483 * 2 ^ 59
def prefixEnd_4754483 : Nat := 4983230072969 + 3 ^ 40 * 4754483 * 2
def baseEnd_4754483 : Nat := 2441335042630626797097037

theorem tailTrace_4754483 : CollatzResearch.WordTrace tailWord_4754483 prefixEnd_4754483 2441335042630626797097037 := by
  unfold tailWord_4754483
  simp only [CollatzResearch.WordTrace]
  refine ⟨173410241234327566894804103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115606827489551711263202735 173410241234327566894804103)
  ·
    refine ⟨260115361851491350342206155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173410241234327566894804103 260115361851491350342206155)
    ·
      refine ⟨390173042777237025513309233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260115361851491350342206155 390173042777237025513309233)
      ·
        refine ⟨292629782082927769134981925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 390173042777237025513309233 292629782082927769134981925)
        ·
          refine ⟨54868084140548956712809111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 292629782082927769134981925 54868084140548956712809111)
          ·
            refine ⟨82302126210823435069213667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54868084140548956712809111 82302126210823435069213667)
            ·
              refine ⟨123453189316235152603820501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82302126210823435069213667 123453189316235152603820501)
              ·
                refine ⟨2893434124599261389152043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 123453189316235152603820501 2893434124599261389152043)
                ·
                  refine ⟨4340151186898892083728065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2893434124599261389152043 4340151186898892083728065)
                  ·
                    refine ⟨3255113390174169062796049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4340151186898892083728065 3255113390174169062796049)
                    ·
                      refine ⟨2441335042630626797097037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3255113390174169062796049 2441335042630626797097037)
                      ·
                        rfl

theorem cell23_4754483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 7, 1, 2, 2].length) (baseStart_4754483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4754483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4754483 prefixEnd_4754483 := by exact prefixLift 4754483
  have htrace : WordTrace (prefixWord ++ tailWord_4754483) baseStart_4754483 baseEnd_4754483 := by
    simpa [prefixWord, tailWord_4754483, baseEnd_4754483] using wordTrace_append hprefix tailTrace_4754483
  have hstable : (prefixWord ++ tailWord_4754483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4754483).length < 2 ^ (prefixWord ++ tailWord_4754483).sum := by decide
  have hdescent : baseEnd_4754483 < baseStart_4754483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4754483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4754486 : List Nat := [5, 1, 2, 1, 1, 2, 3, 1, 1, 1, 5]
def baseStart_4754486 : Nat := 118140960795 + 4754486 * 2 ^ 59
def prefixEnd_4754486 : Nat := 4983230072969 + 3 ^ 40 * 4754486 * 2
def baseEnd_4754486 : Nat := 2441336583072590285359523

theorem tailTrace_4754486 : CollatzResearch.WordTrace tailWord_4754486 prefixEnd_4754486 2441336583072590285359523 := by
  unfold tailWord_4754486
  simp only [CollatzResearch.WordTrace]
  refine ⟨10838146915832293650447707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115606900435544465604775541 10838146915832293650447707)
  ·
    refine ⟨16257220373748440475671561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10838146915832293650447707 16257220373748440475671561)
    ·
      refine ⟨12192915280311330356753671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16257220373748440475671561 12192915280311330356753671)
      ·
        refine ⟨18289372920466995535130507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12192915280311330356753671 18289372920466995535130507)
        ·
          refine ⟨27434059380700493302695761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18289372920466995535130507 27434059380700493302695761)
          ·
            refine ⟨20575544535525369977021821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27434059380700493302695761 20575544535525369977021821)
            ·
              refine ⟨7715829200822013741383183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20575544535525369977021821 7715829200822013741383183)
              ·
                refine ⟨11573743801233020612074775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7715829200822013741383183 11573743801233020612074775)
                ·
                  refine ⟨17360615701849530918112163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11573743801233020612074775 17360615701849530918112163)
                  ·
                    refine ⟨26040923552774296377168245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17360615701849530918112163 26040923552774296377168245)
                    ·
                      refine ⟨2441336583072590285359523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26040923552774296377168245 2441336583072590285359523)
                      ·
                        rfl

theorem cell23_4754486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_4754486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4754486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4754486 prefixEnd_4754486 := by exact prefixLift 4754486
  have htrace : WordTrace (prefixWord ++ tailWord_4754486) baseStart_4754486 baseEnd_4754486 := by
    simpa [prefixWord, tailWord_4754486, baseEnd_4754486] using wordTrace_append hprefix tailTrace_4754486
  have hstable : (prefixWord ++ tailWord_4754486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4754486).length < 2 ^ (prefixWord ++ tailWord_4754486).sum := by decide
  have hdescent : baseEnd_4754486 < baseStart_4754486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4754486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4754532 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 3, 8]
def baseStart_4754532 : Nat := 118140960795 + 4754532 * 2 ^ 59
def prefixEnd_4754532 : Nat := 4983230072969 + 3 ^ 40 * 4754532 * 2
def baseEnd_4754532 : Nat := 813786734394232368461437

theorem tailTrace_4754532 : CollatzResearch.WordTrace tailWord_4754532 prefixEnd_4754532 813786734394232368461437 := by
  unfold tailWord_4754532
  simp only [CollatzResearch.WordTrace]
  refine ⟨86706014205575024131668925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115608018940766698842225233 86706014205575024131668925)
  ·
    refine ⟨32514755327090634049375847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86706014205575024131668925 32514755327090634049375847)
    ·
      refine ⟨48772132990635951074063771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32514755327090634049375847 48772132990635951074063771)
      ·
        refine ⟨73158199485953926611095657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48772132990635951074063771 73158199485953926611095657)
        ·
          refine ⟨54868649614465444958321743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73158199485953926611095657 54868649614465444958321743)
          ·
            refine ⟨82302974421698167437482615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54868649614465444958321743 82302974421698167437482615)
            ·
              refine ⟨123454461632547251156223923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82302974421698167437482615 123454461632547251156223923)
              ·
                refine ⟨185181692448820876734335885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123454461632547251156223923 185181692448820876734335885)
                ·
                  refine ⟨69443134668307828775375957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 185181692448820876734335885 69443134668307828775375957)
                  ·
                    refine ⟨813786734394232368461437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 69443134668307828775375957 813786734394232368461437)
                    ·
                      rfl

theorem cell23_4754532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_4754532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4754532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4754532 prefixEnd_4754532 := by exact prefixLift 4754532
  have htrace : WordTrace (prefixWord ++ tailWord_4754532) baseStart_4754532 baseEnd_4754532 := by
    simpa [prefixWord, tailWord_4754532, baseEnd_4754532] using wordTrace_append hprefix tailTrace_4754532
  have hstable : (prefixWord ++ tailWord_4754532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4754532).length < 2 ^ (prefixWord ++ tailWord_4754532).sum := by decide
  have hdescent : baseEnd_4754532 < baseStart_4754532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4754532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4754569 : List Nat := [1, 2, 1, 1, 4, 3, 2, 1, 2, 2, 4]
def baseStart_4754569 : Nat := 118140960795 + 4754569 * 2 ^ 59
def prefixEnd_4754569 : Nat := 4983230072969 + 3 ^ 40 * 4754569 * 2
def baseEnd_4754569 : Nat := 2441379201966913460621641

theorem tailTrace_4754569 : CollatzResearch.WordTrace tailWord_4754569 prefixEnd_4754569 2441379201966913460621641 := by
  unfold tailWord_4754569
  simp only [CollatzResearch.WordTrace]
  refine ⟨173413377912016003582434761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115608918608010669054956507 173413377912016003582434761)
  ·
    refine ⟨130060033434012002686826071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173413377912016003582434761 130060033434012002686826071)
    ·
      refine ⟨195090050151018004030239107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130060033434012002686826071 195090050151018004030239107)
      ·
        refine ⟨292635075226527006045358661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195090050151018004030239107 292635075226527006045358661)
        ·
          refine ⟨54869076604973813633504749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 292635075226527006045358661 54869076604973813633504749)
          ·
            refine ⟨20575903726865180112564281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54869076604973813633504749 20575903726865180112564281)
            ·
              refine ⟨15431927795148885084423211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20575903726865180112564281 15431927795148885084423211)
              ·
                refine ⟨23147891692723327626634817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15431927795148885084423211 23147891692723327626634817)
                ·
                  refine ⟨17360918769542495719976113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23147891692723327626634817 17360918769542495719976113)
                  ·
                    refine ⟨13020689077156871789982085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17360918769542495719976113 13020689077156871789982085)
                    ·
                      refine ⟨2441379201966913460621641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13020689077156871789982085 2441379201966913460621641)
                      ·
                        rfl

theorem cell23_4754569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 2, 4].length) (baseStart_4754569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4754569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4754569 prefixEnd_4754569 := by exact prefixLift 4754569
  have htrace : WordTrace (prefixWord ++ tailWord_4754569) baseStart_4754569 baseEnd_4754569 := by
    simpa [prefixWord, tailWord_4754569, baseEnd_4754569] using wordTrace_append hprefix tailTrace_4754569
  have hstable : (prefixWord ++ tailWord_4754569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4754569).length < 2 ^ (prefixWord ++ tailWord_4754569).sum := by decide
  have hdescent : baseEnd_4754569 < baseStart_4754569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4754569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4754572 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 1, 1, 9]
def baseStart_4754572 : Nat := 118140960795 + 4754572 * 2 ^ 59
def prefixEnd_4754572 : Nat := 4983230072969 + 3 ^ 40 * 4754572 * 2
def baseEnd_4754572 : Nat := 2441380742408876948884127

theorem tailTrace_4754572 : CollatzResearch.WordTrace tailWord_4754572 prefixEnd_4754572 2441380742408876948884127 := by
  unfold tailWord_4754572
  simp only [CollatzResearch.WordTrace]
  refine ⟨86706743665502567547396985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115608991554003423396529313 86706743665502567547396985)
  ·
    refine ⟨65030057749126925660547739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86706743665502567547396985 65030057749126925660547739)
    ·
      refine ⟨97545086623690388490821609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65030057749126925660547739 97545086623690388490821609)
      ·
        refine ⟨73158814967767791368116207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97545086623690388490821609 73158814967767791368116207)
        ·
          refine ⟨109738222451651687052174311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73158814967767791368116207 109738222451651687052174311)
          ·
            refine ⟨164607333677477530578261467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109738222451651687052174311 164607333677477530578261467)
            ·
              refine ⟨246911000516216295867392201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164607333677477530578261467 246911000516216295867392201)
              ·
                refine ⟨185183250387162221900544151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 246911000516216295867392201 185183250387162221900544151)
                ·
                  refine ⟨277774875580743332850816227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 185183250387162221900544151 277774875580743332850816227)
                  ·
                    refine ⟨416662313371114999276224341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 277774875580743332850816227 416662313371114999276224341)
                    ·
                      refine ⟨2441380742408876948884127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 416662313371114999276224341 2441380742408876948884127)
                      ·
                        rfl

theorem cell23_4754572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_4754572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4754572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4754572 prefixEnd_4754572 := by exact prefixLift 4754572
  have htrace : WordTrace (prefixWord ++ tailWord_4754572) baseStart_4754572 baseEnd_4754572 := by
    simpa [prefixWord, tailWord_4754572, baseEnd_4754572] using wordTrace_append hprefix tailTrace_4754572
  have hstable : (prefixWord ++ tailWord_4754572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4754572).length < 2 ^ (prefixWord ++ tailWord_4754572).sum := by decide
  have hdescent : baseEnd_4754572 < baseStart_4754572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4754572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4754590 : List Nat := [4, 3, 1, 1, 2, 1, 1, 2, 4, 2, 2]
def baseStart_4754590 : Nat := 118140960795 + 4754590 * 2 ^ 59
def prefixEnd_4754590 : Nat := 4983230072969 + 3 ^ 40 * 4754590 * 2
def baseEnd_4754590 : Nat := 2441389985060657878459045

theorem tailTrace_4754590 : CollatzResearch.WordTrace tailWord_4754590 prefixEnd_4754590 2441389985060657878459045 := by
  unfold tailWord_4754590
  simp only [CollatzResearch.WordTrace]
  refine ⟨21676767980617490521118653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115609429229959949445966149 21676767980617490521118653)
  ·
    refine ⟨8128787992731558945419495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21676767980617490521118653 8128787992731558945419495)
    ·
      refine ⟨12193181989097338418129243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8128787992731558945419495 12193181989097338418129243)
      ·
        refine ⟨18289772983646007627193865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12193181989097338418129243 18289772983646007627193865)
        ·
          refine ⟨13717329737734505720395399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18289772983646007627193865 13717329737734505720395399)
          ·
            refine ⟨20575994606601758580593099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13717329737734505720395399 20575994606601758580593099)
            ·
              refine ⟨30863991909902637870889649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20575994606601758580593099 30863991909902637870889649)
              ·
                refine ⟨23147993932426978403167237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30863991909902637870889649 23147993932426978403167237)
                ·
                  refine ⟨4340248862330058450593857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23147993932426978403167237 4340248862330058450593857)
                  ·
                    refine ⟨3255186646747543837945393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4340248862330058450593857 3255186646747543837945393)
                    ·
                      refine ⟨2441389985060657878459045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3255186646747543837945393 2441389985060657878459045)
                      ·
                        rfl

theorem cell23_4754590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_4754590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4754590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4754590 prefixEnd_4754590 := by exact prefixLift 4754590
  have htrace : WordTrace (prefixWord ++ tailWord_4754590) baseStart_4754590 baseEnd_4754590 := by
    simpa [prefixWord, tailWord_4754590, baseEnd_4754590] using wordTrace_append hprefix tailTrace_4754590
  have hstable : (prefixWord ++ tailWord_4754590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4754590).length < 2 ^ (prefixWord ++ tailWord_4754590).sum := by decide
  have hdescent : baseEnd_4754590 < baseStart_4754590 := by decide
  rcases family_descends (prefixWord ++ tailWord_4754590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4754624 : List Nat := [2, 1, 1, 2, 7, 1, 2, 1, 2, 2, 2]
def baseStart_4754624 : Nat := 118140960795 + 4754624 * 2 ^ 59
def prefixEnd_4754624 : Nat := 4983230072969 + 3 ^ 40 * 4754624 * 2
def baseEnd_4754624 : Nat := 2441407443402910745433889

theorem tailTrace_4754624 : CollatzResearch.WordTrace tailWord_4754624 prefixEnd_4754624 2441407443402910745433889 := by
  unfold tailWord_4754624
  simp only [CollatzResearch.WordTrace]
  refine ⟨86707691963408373987843463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115610255951211165317124617 86707691963408373987843463)
  ·
    refine ⟨130061537945112560981765195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86707691963408373987843463 130061537945112560981765195)
    ·
      refine ⟨195092306917668841472647793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130061537945112560981765195 195092306917668841472647793)
      ·
        refine ⟨146319230188251631104485845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195092306917668841472647793 146319230188251631104485845)
        ·
          refine ⟨3429356957537147604011387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 146319230188251631104485845 3429356957537147604011387)
          ·
            refine ⟨5144035436305721406017081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3429356957537147604011387 5144035436305721406017081)
            ·
              refine ⟨3858026577229291054512811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5144035436305721406017081 3858026577229291054512811)
              ·
                refine ⟨5787039865843936581769217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3858026577229291054512811 5787039865843936581769217)
                ·
                  refine ⟨4340279899382952436326913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5787039865843936581769217 4340279899382952436326913)
                  ·
                    refine ⟨3255209924537214327245185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4340279899382952436326913 3255209924537214327245185)
                    ·
                      refine ⟨2441407443402910745433889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3255209924537214327245185 2441407443402910745433889)
                      ·
                        rfl

theorem cell23_4754624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 1, 2, 2, 2].length) (baseStart_4754624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4754624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4754624 prefixEnd_4754624 := by exact prefixLift 4754624
  have htrace : WordTrace (prefixWord ++ tailWord_4754624) baseStart_4754624 baseEnd_4754624 := by
    simpa [prefixWord, tailWord_4754624, baseEnd_4754624] using wordTrace_append hprefix tailTrace_4754624
  have hstable : (prefixWord ++ tailWord_4754624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4754624).length < 2 ^ (prefixWord ++ tailWord_4754624).sum := by decide
  have hdescent : baseEnd_4754624 < baseStart_4754624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4754624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4754629 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 6, 1, 4]
def baseStart_4754629 : Nat := 118140960795 + 4754629 * 2 ^ 59
def prefixEnd_4754629 : Nat := 4983230072969 + 3 ^ 40 * 4754629 * 2
def baseEnd_4754629 : Nat := 2441410010806183225871365

theorem tailTrace_4754629 : CollatzResearch.WordTrace tailWord_4754629 prefixEnd_4754629 2441410010806183225871365 := by
  unfold tailWord_4754629
  simp only [CollatzResearch.WordTrace]
  refine ⟨173415566291798633829618941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115610377527865755886412627 173415566291798633829618941)
  ·
    refine ⟨65030837359424487686107103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173415566291798633829618941 65030837359424487686107103)
    ·
      refine ⟨97546256039136731529160655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65030837359424487686107103 97546256039136731529160655)
      ·
        refine ⟨146319384058705097293740983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97546256039136731529160655 146319384058705097293740983)
        ·
          refine ⟨219479076088057645940611475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146319384058705097293740983 219479076088057645940611475)
          ·
            refine ⟨329218614132086468910917213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219479076088057645940611475 329218614132086468910917213)
            ·
              refine ⟨123456980299532425841593955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 329218614132086468910917213 123456980299532425841593955)
              ·
                refine ⟨185185470449298638762390933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123456980299532425841593955 185185470449298638762390933)
                ·
                  refine ⟨8680568927310873691987075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 185185470449298638762390933 8680568927310873691987075)
                  ·
                    refine ⟨13020853390966310537980613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8680568927310873691987075 13020853390966310537980613)
                    ·
                      refine ⟨2441410010806183225871365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13020853390966310537980613 2441410010806183225871365)
                      ·
                        rfl

theorem cell23_4754629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6, 1, 4].length) (baseStart_4754629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4754629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4754629 prefixEnd_4754629 := by exact prefixLift 4754629
  have htrace : WordTrace (prefixWord ++ tailWord_4754629) baseStart_4754629 baseEnd_4754629 := by
    simpa [prefixWord, tailWord_4754629, baseEnd_4754629] using wordTrace_append hprefix tailTrace_4754629
  have hstable : (prefixWord ++ tailWord_4754629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4754629).length < 2 ^ (prefixWord ++ tailWord_4754629).sum := by decide
  have hdescent : baseEnd_4754629 < baseStart_4754629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4754629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4754690 : List Nat := [3, 4, 1, 1, 3, 1, 1, 2, 3, 4]
def baseStart_4754690 : Nat := 118140960795 + 4754690 * 2 ^ 59
def prefixEnd_4754690 : Nat := 4983230072969 + 3 ^ 40 * 4754690 * 2
def baseEnd_4754690 : Nat := 813813777708702495736195

theorem tailTrace_4754690 : CollatzResearch.WordTrace tailWord_4754690 prefixEnd_4754690 813813777708702495736195 := by
  unfold tailWord_4754690
  simp only [CollatzResearch.WordTrace]
  refine ⟨43354447786144410311897381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115611860763051760831726349 43354447786144410311897381)
  ·
    refine ⟨8128958959902076933480759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43354447786144410311897381 8128958959902076933480759)
    ·
      refine ⟨12193438439853115400221139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8128958959902076933480759 12193438439853115400221139)
      ·
        refine ⟨18290157659779673100331709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12193438439853115400221139 18290157659779673100331709)
        ·
          refine ⟨6858809122417377412624391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18290157659779673100331709 6858809122417377412624391)
          ·
            refine ⟨10288213683626066118936587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6858809122417377412624391 10288213683626066118936587)
            ·
              refine ⟨15432320525439099178404881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10288213683626066118936587 15432320525439099178404881)
              ·
                refine ⟨11574240394079324383803661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15432320525439099178404881 11574240394079324383803661)
                ·
                  refine ⟨4340340147779746643926373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11574240394079324383803661 4340340147779746643926373)
                  ·
                    refine ⟨813813777708702495736195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4340340147779746643926373 813813777708702495736195)
                    ·
                      rfl

theorem cell23_4754690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_4754690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4754690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4754690 prefixEnd_4754690 := by exact prefixLift 4754690
  have htrace : WordTrace (prefixWord ++ tailWord_4754690) baseStart_4754690 baseEnd_4754690 := by
    simpa [prefixWord, tailWord_4754690, baseEnd_4754690] using wordTrace_append hprefix tailTrace_4754690
  have hstable : (prefixWord ++ tailWord_4754690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4754690).length < 2 ^ (prefixWord ++ tailWord_4754690).sum := by decide
  have hdescent : baseEnd_4754690 < baseStart_4754690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4754690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4754709 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 2, 4, 5]
def baseStart_4754709 : Nat := 118140960795 + 4754709 * 2 ^ 59
def prefixEnd_4754709 : Nat := 4983230072969 + 3 ^ 40 * 4754709 * 2
def baseEnd_4754709 : Nat := 2441451089258542912870997

theorem tailTrace_4754709 : CollatzResearch.WordTrace tailWord_4754709 prefixEnd_4754709 2441451089258542912870997 := by
  unfold tailWord_4754709
  simp only [CollatzResearch.WordTrace]
  refine ⟨173418484131508807492531181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115612322754339204995020787 173418484131508807492531181)
  ·
    refine ⟨65031931549315802809699193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173418484131508807492531181 65031931549315802809699193)
    ·
      refine ⟨48773948661986852107274395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65031931549315802809699193 48773948661986852107274395)
      ·
        refine ⟨73160922992980278160911593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48773948661986852107274395 73160922992980278160911593)
        ·
          refine ⟨54870692244735208620683695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73160922992980278160911593 54870692244735208620683695)
          ·
            refine ⟨82306038367102812931025543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54870692244735208620683695 82306038367102812931025543)
            ·
              refine ⟨123459057550654219396538315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82306038367102812931025543 123459057550654219396538315)
              ·
                refine ⟨185188586325981329094807473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123459057550654219396538315 185188586325981329094807473)
                ·
                  refine ⟨138891439744485996821105605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 185188586325981329094807473 138891439744485996821105605)
                  ·
                    refine ⟨26042144952091124403957301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 138891439744485996821105605 26042144952091124403957301)
                    ·
                      refine ⟨2441451089258542912870997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26042144952091124403957301 2441451089258542912870997)
                      ·
                        rfl

theorem cell23_4754709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_4754709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4754709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4754709 prefixEnd_4754709 := by exact prefixLift 4754709
  have htrace : WordTrace (prefixWord ++ tailWord_4754709) baseStart_4754709 baseEnd_4754709 := by
    simpa [prefixWord, tailWord_4754709, baseEnd_4754709] using wordTrace_append hprefix tailTrace_4754709
  have hstable : (prefixWord ++ tailWord_4754709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4754709).length < 2 ^ (prefixWord ++ tailWord_4754709).sum := by decide
  have hdescent : baseEnd_4754709 < baseStart_4754709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4754709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4754720 : List Nat := [2, 1, 1, 5, 4, 1, 1, 2, 6]
def baseStart_4754720 : Nat := 118140960795 + 4754720 * 2 ^ 59
def prefixEnd_4754720 : Nat := 4983230072969 + 3 ^ 40 * 4754720 * 2
def baseEnd_4754720 : Nat := 271272970838415818870383

theorem tailTrace_4754720 : CollatzResearch.WordTrace tailWord_4754720 prefixEnd_4754720 271272970838415818870383 := by
  unfold tailWord_4754720
  simp only [CollatzResearch.WordTrace]
  refine ⟨86709442667234478185590807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115612590222979304247454409 86709442667234478185590807)
  ·
    refine ⟨130064164000851717278386211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86709442667234478185590807 130064164000851717278386211)
    ·
      refine ⟨195096246001277575917579317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130064164000851717278386211 195096246001277575917579317)
      ·
        refine ⟨18290273062619772742273061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 195096246001277575917579317 18290273062619772742273061)
        ·
          refine ⟨3429426199241207389176199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18290273062619772742273061 3429426199241207389176199)
          ·
            refine ⟨5144139298861811083764299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3429426199241207389176199 5144139298861811083764299)
            ·
              refine ⟨7716208948292716625646449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5144139298861811083764299 7716208948292716625646449)
              ·
                refine ⟨5787156711219537469234837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7716208948292716625646449 5787156711219537469234837)
                ·
                  refine ⟨271272970838415818870383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5787156711219537469234837 271272970838415818870383)
                  ·
                    rfl

theorem cell23_4754720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 2, 6].length) (baseStart_4754720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4754720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4754720 prefixEnd_4754720 := by exact prefixLift 4754720
  have htrace : WordTrace (prefixWord ++ tailWord_4754720) baseStart_4754720 baseEnd_4754720 := by
    simpa [prefixWord, tailWord_4754720, baseEnd_4754720] using wordTrace_append hprefix tailTrace_4754720
  have hstable : (prefixWord ++ tailWord_4754720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4754720).length < 2 ^ (prefixWord ++ tailWord_4754720).sum := by decide
  have hdescent : baseEnd_4754720 < baseStart_4754720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4754720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4754730 : List Nat := [3, 1, 4, 2, 1, 1, 1, 3, 3, 1, 3]
def baseStart_4754730 : Nat := 118140960795 + 4754730 * 2 ^ 59
def prefixEnd_4754730 : Nat := 4983230072969 + 3 ^ 40 * 4754730 * 2
def baseEnd_4754730 : Nat := 2441461872352287330708401

theorem tailTrace_4754730 : CollatzResearch.WordTrace tailWord_4754730 prefixEnd_4754730 2441461872352287330708401 := by
  unfold tailWord_4754730
  simp only [CollatzResearch.WordTrace]
  refine ⟨43354812516108182019761411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115612833376288485386030429 43354812516108182019761411)
  ·
    refine ⟨65032218774162273029642117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43354812516108182019761411 65032218774162273029642117)
    ·
      refine ⟨12193541020155426193057897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65032218774162273029642117 12193541020155426193057897)
      ·
        refine ⟨9145155765116569644793423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12193541020155426193057897 9145155765116569644793423)
        ·
          refine ⟨13717733647674854467190135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9145155765116569644793423 13717733647674854467190135)
          ·
            refine ⟨20576600471512281700785203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13717733647674854467190135 20576600471512281700785203)
            ·
              refine ⟨30864900707268422551177805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20576600471512281700785203 30864900707268422551177805)
              ·
                refine ⟨11574337765225658456691677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30864900707268422551177805 11574337765225658456691677)
                ·
                  refine ⟨4340376661959621921259379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11574337765225658456691677 4340376661959621921259379)
                  ·
                    refine ⟨6510564992939432881889069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4340376661959621921259379 6510564992939432881889069)
                    ·
                      refine ⟨2441461872352287330708401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6510564992939432881889069 2441461872352287330708401)
                      ·
                        rfl

theorem cell23_4754730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_4754730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4754730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4754730 prefixEnd_4754730 := by exact prefixLift 4754730
  have htrace : WordTrace (prefixWord ++ tailWord_4754730) baseStart_4754730 baseEnd_4754730 := by
    simpa [prefixWord, tailWord_4754730, baseEnd_4754730] using wordTrace_append hprefix tailTrace_4754730
  have hstable : (prefixWord ++ tailWord_4754730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4754730).length < 2 ^ (prefixWord ++ tailWord_4754730).sum := by decide
  have hdescent : baseEnd_4754730 < baseStart_4754730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4754730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4754758 : List Nat := [6, 1, 1, 3, 2, 1, 1, 3, 1, 4]
def baseStart_4754758 : Nat := 118140960795 + 4754758 * 2 ^ 59
def prefixEnd_4754758 : Nat := 4983230072969 + 3 ^ 40 * 4754758 * 2
def baseEnd_4754758 : Nat := 813825416603537740386091

theorem tailTrace_4754758 : CollatzResearch.WordTrace tailWord_4754758 prefixEnd_4754758 813825416603537740386091 := by
  unfold tailWord_4754758
  simp only [CollatzResearch.WordTrace]
  refine ⟨5419383478385352776908279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 115613514205554192574043285 5419383478385352776908279)
  ·
    refine ⟨8129075217578029165362419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5419383478385352776908279 8129075217578029165362419)
    ·
      refine ⟨12193612826367043748043629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8129075217578029165362419 12193612826367043748043629)
      ·
        refine ⟨4572604809887641405516361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12193612826367043748043629 4572604809887641405516361)
        ·
          refine ⟨3429453607415731054137271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4572604809887641405516361 3429453607415731054137271)
          ·
            refine ⟨5144180411123596581205907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3429453607415731054137271 5144180411123596581205907)
            ·
              refine ⟨7716270616685394871808861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5144180411123596581205907 7716270616685394871808861)
              ·
                refine ⟨2893601481257023076928323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7716270616685394871808861 2893601481257023076928323)
                ·
                  refine ⟨4340402221885534615392485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2893601481257023076928323 4340402221885534615392485)
                  ·
                    refine ⟨813825416603537740386091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4340402221885534615392485 813825416603537740386091)
                    ·
                      rfl

theorem cell23_4754758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_4754758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4754758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4754758 prefixEnd_4754758 := by exact prefixLift 4754758
  have htrace : WordTrace (prefixWord ++ tailWord_4754758) baseStart_4754758 baseEnd_4754758 := by
    simpa [prefixWord, tailWord_4754758, baseEnd_4754758] using wordTrace_append hprefix tailTrace_4754758
  have hstable : (prefixWord ++ tailWord_4754758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4754758).length < 2 ^ (prefixWord ++ tailWord_4754758).sum := by decide
  have hdescent : baseEnd_4754758 < baseStart_4754758 := by decide
  rcases family_descends (prefixWord ++ tailWord_4754758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4754766 : List Nat := [4, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4]
def baseStart_4754766 : Nat := 118140960795 + 4754766 * 2 ^ 59
def prefixEnd_4754766 : Nat := 4983230072969 + 3 ^ 40 * 4754766 * 2
def baseEnd_4754766 : Nat := 2441480357655849189858235

theorem tailTrace_4754766 : CollatzResearch.WordTrace tailWord_4754766 prefixEnd_4754766 2441480357655849189858235 := by
  unfold tailWord_4754766
  simp only [CollatzResearch.WordTrace]
  refine ⟨21677570386537788278419519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115613708728201537484904101 21677570386537788278419519)
  ·
    refine ⟨32516355579806682417629279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21677570386537788278419519 32516355579806682417629279)
    ·
      refine ⟨48774533369710023626443919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32516355579806682417629279 48774533369710023626443919)
      ·
        refine ⟨73161800054565035439665879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48774533369710023626443919 73161800054565035439665879)
        ·
          refine ⟨109742700081847553159498819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73161800054565035439665879 109742700081847553159498819)
          ·
            refine ⟨164614050122771329739248229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109742700081847553159498819 164614050122771329739248229)
            ·
              refine ⟨30865134398019624326109043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 164614050122771329739248229 30865134398019624326109043)
              ·
                refine ⟨46297701597029436489163565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30865134398019624326109043 46297701597029436489163565)
                ·
                  refine ⟨17361638098886038683436337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46297701597029436489163565 17361638098886038683436337)
                  ·
                    refine ⟨13021228574164529012577253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17361638098886038683436337 13021228574164529012577253)
                    ·
                      refine ⟨2441480357655849189858235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13021228574164529012577253 2441480357655849189858235)
                      ·
                        rfl

theorem cell23_4754766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_4754766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4754766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4754766 prefixEnd_4754766 := by exact prefixLift 4754766
  have htrace : WordTrace (prefixWord ++ tailWord_4754766) baseStart_4754766 baseEnd_4754766 := by
    simpa [prefixWord, tailWord_4754766, baseEnd_4754766] using wordTrace_append hprefix tailTrace_4754766
  have hstable : (prefixWord ++ tailWord_4754766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4754766).length < 2 ^ (prefixWord ++ tailWord_4754766).sum := by decide
  have hdescent : baseEnd_4754766 < baseStart_4754766 := by decide
  rcases family_descends (prefixWord ++ tailWord_4754766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4754773 : List Nat := [1, 3, 2, 2, 3, 2, 2, 1, 1, 1, 5]
def baseStart_4754773 : Nat := 118140960795 + 4754773 * 2 ^ 59
def prefixEnd_4754773 : Nat := 4983230072969 + 3 ^ 40 * 4754773 * 2
def baseEnd_4754773 : Nat := 2441483952020430662470703

theorem tailTrace_4754773 : CollatzResearch.WordTrace tailWord_4754773 prefixEnd_4754773 2441483952020430662470703 := by
  unfold tailWord_4754773
  simp only [CollatzResearch.WordTrace]
  refine ⟨173420818403276946422860973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115613878935517964281907315 173420818403276946422860973)
  ·
    refine ⟨65032806901228854908572865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173420818403276946422860973 65032806901228854908572865)
    ·
      refine ⟨48774605175921641181429649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65032806901228854908572865 48774605175921641181429649)
      ·
        refine ⟨36580953881941230886072237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48774605175921641181429649 36580953881941230886072237)
        ·
          refine ⟨13717857705727961582277089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36580953881941230886072237 13717857705727961582277089)
          ·
            refine ⟨10288393279295971186707817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13717857705727961582277089 10288393279295971186707817)
            ·
              refine ⟨7716294959471978390030863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10288393279295971186707817 7716294959471978390030863)
              ·
                refine ⟨11574442439207967585046295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7716294959471978390030863 11574442439207967585046295)
                ·
                  refine ⟨17361663658811951377569443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11574442439207967585046295 17361663658811951377569443)
                  ·
                    refine ⟨26042495488217927066354165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17361663658811951377569443 26042495488217927066354165)
                    ·
                      refine ⟨2441483952020430662470703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26042495488217927066354165 2441483952020430662470703)
                      ·
                        rfl

theorem cell23_4754773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_4754773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4754773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4754773 prefixEnd_4754773 := by exact prefixLift 4754773
  have htrace : WordTrace (prefixWord ++ tailWord_4754773) baseStart_4754773 baseEnd_4754773 := by
    simpa [prefixWord, tailWord_4754773, baseEnd_4754773] using wordTrace_append hprefix tailTrace_4754773
  have hstable : (prefixWord ++ tailWord_4754773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4754773).length < 2 ^ (prefixWord ++ tailWord_4754773).sum := by decide
  have hdescent : baseEnd_4754773 < baseStart_4754773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4754773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4754781 : List Nat := [1, 4, 5, 1, 1, 2, 1, 1, 3, 1, 3]
def baseStart_4754781 : Nat := 118140960795 + 4754781 * 2 ^ 59
def prefixEnd_4754781 : Nat := 4983230072969 + 3 ^ 40 * 4754781 * 2
def baseEnd_4754781 : Nat := 2441488059865666631170667

theorem tailTrace_4754781 : CollatzResearch.WordTrace tailWord_4754781 prefixEnd_4754781 2441488059865666631170667 := by
  unfold tailWord_4754781
  simp only [CollatzResearch.WordTrace]
  refine ⟨173421110187247963789152197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115614073458165309192768131 173421110187247963789152197)
  ·
    refine ⟨32516458160108993210466037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173421110187247963789152197 32516458160108993210466037)
    ·
      refine ⟨3048417952510218113481191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32516458160108993210466037 3048417952510218113481191)
      ·
        refine ⟨4572626928765327170221787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3048417952510218113481191 4572626928765327170221787)
        ·
          refine ⟨6858940393147990755332681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4572626928765327170221787 6858940393147990755332681)
          ·
            refine ⟨5144205294860993066499511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6858940393147990755332681 5144205294860993066499511)
            ·
              refine ⟨7716307942291489599749267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5144205294860993066499511 7716307942291489599749267)
              ·
                refine ⟨11574461913437234399623901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7716307942291489599749267 11574461913437234399623901)
                ·
                  refine ⟨4340423217538962899858963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11574461913437234399623901 4340423217538962899858963)
                  ·
                    refine ⟨6510634826308444349788445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4340423217538962899858963 6510634826308444349788445)
                    ·
                      refine ⟨2441488059865666631170667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6510634826308444349788445 2441488059865666631170667)
                      ·
                        rfl

theorem cell23_4754781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_4754781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4754781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4754781 prefixEnd_4754781 := by exact prefixLift 4754781
  have htrace : WordTrace (prefixWord ++ tailWord_4754781) baseStart_4754781 baseEnd_4754781 := by
    simpa [prefixWord, tailWord_4754781, baseEnd_4754781] using wordTrace_append hprefix tailTrace_4754781
  have hstable : (prefixWord ++ tailWord_4754781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4754781).length < 2 ^ (prefixWord ++ tailWord_4754781).sum := by decide
  have hdescent : baseEnd_4754781 < baseStart_4754781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4754781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4754787 : List Nat := [1, 1, 1, 5, 2, 4, 1, 1, 3, 2, 2]
def baseStart_4754787 : Nat := 118140960795 + 4754787 * 2 ^ 59
def prefixEnd_4754787 : Nat := 4983230072969 + 3 ^ 40 * 4754787 * 2
def baseEnd_4754787 : Nat := 2441491140749593607695639

theorem tailTrace_4754787 : CollatzResearch.WordTrace tailWord_4754787 prefixEnd_4754787 2441491140749593607695639 := by
  unfold tailWord_4754787
  simp only [CollatzResearch.WordTrace]
  refine ⟨173421329025226226813870615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115614219350150817875913743 173421329025226226813870615)
  ·
    refine ⟨260131993537839340220805923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173421329025226226813870615 260131993537839340220805923)
    ·
      refine ⟨390197990306759010331208885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260131993537839340220805923 390197990306759010331208885)
      ·
        refine ⟨36581061591258657218550833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 390197990306759010331208885 36581061591258657218550833)
        ·
          refine ⟨27435796193443992913913125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36581061591258657218550833 27435796193443992913913125)
          ·
            refine ⟨5144211786270748671358711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27435796193443992913913125 5144211786270748671358711)
            ·
              refine ⟨7716317679406123007038067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5144211786270748671358711 7716317679406123007038067)
              ·
                refine ⟨11574476519109184510557101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7716317679406123007038067 11574476519109184510557101)
                ·
                  refine ⟨4340428694665944191458913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11574476519109184510557101 4340428694665944191458913)
                  ·
                    refine ⟨3255321520999458143594185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4340428694665944191458913 3255321520999458143594185)
                    ·
                      refine ⟨2441491140749593607695639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3255321520999458143594185 2441491140749593607695639)
                      ·
                        rfl

theorem cell23_4754787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 3, 2, 2].length) (baseStart_4754787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4754787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4754787 prefixEnd_4754787 := by exact prefixLift 4754787
  have htrace : WordTrace (prefixWord ++ tailWord_4754787) baseStart_4754787 baseEnd_4754787 := by
    simpa [prefixWord, tailWord_4754787, baseEnd_4754787] using wordTrace_append hprefix tailTrace_4754787
  have hstable : (prefixWord ++ tailWord_4754787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4754787).length < 2 ^ (prefixWord ++ tailWord_4754787).sum := by decide
  have hdescent : baseEnd_4754787 < baseStart_4754787 := by decide
  rcases family_descends (prefixWord ++ tailWord_4754787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4754797 : List Nat := [1, 5, 1, 1, 1, 5, 2, 1, 2, 4]
def baseStart_4754797 : Nat := 118140960795 + 4754797 * 2 ^ 59
def prefixEnd_4754797 : Nat := 4983230072969 + 3 ^ 40 * 4754797 * 2
def baseEnd_4754797 : Nat := 813832091852046189523531

theorem tailTrace_4754797 : CollatzResearch.WordTrace tailWord_4754797 prefixEnd_4754797 813832091852046189523531 := by
  unfold tailWord_4754797
  simp only [CollatzResearch.WordTrace]
  refine ⟨173421693755189998521734645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115614462503459999014489763 173421693755189998521734645)
  ·
    refine ⟨16258283789549062361412623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 173421693755189998521734645 16258283789549062361412623)
    ·
      refine ⟨24387425684323593542118935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16258283789549062361412623 24387425684323593542118935)
      ·
        refine ⟨36581138526485390313178403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24387425684323593542118935 36581138526485390313178403)
        ·
          refine ⟨54871707789728085469767605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36581138526485390313178403 54871707789728085469767605)
          ·
            refine ⟨5144222605287008012790713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54871707789728085469767605 5144222605287008012790713)
            ·
              refine ⟨3858166953965256009593035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5144222605287008012790713 3858166953965256009593035)
              ·
                refine ⟨5787250430947884014389553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3858166953965256009593035 5787250430947884014389553)
                ·
                  refine ⟨4340437823210913010792165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5787250430947884014389553 4340437823210913010792165)
                  ·
                    refine ⟨813832091852046189523531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4340437823210913010792165 813832091852046189523531)
                    ·
                      rfl

theorem cell23_4754797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_4754797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4754797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4754797 prefixEnd_4754797 := by exact prefixLift 4754797
  have htrace : WordTrace (prefixWord ++ tailWord_4754797) baseStart_4754797 baseEnd_4754797 := by
    simpa [prefixWord, tailWord_4754797, baseEnd_4754797] using wordTrace_append hprefix tailTrace_4754797
  have hstable : (prefixWord ++ tailWord_4754797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4754797).length < 2 ^ (prefixWord ++ tailWord_4754797).sum := by decide
  have hdescent : baseEnd_4754797 < baseStart_4754797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4754797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4754883 : List Nat := [1, 1, 1, 3, 1, 1, 5, 5, 5]
def baseStart_4754883 : Nat := 118140960795 + 4754883 * 2 ^ 59
def prefixEnd_4754883 : Nat := 4983230072969 + 3 ^ 40 * 4754883 * 2
def baseEnd_4754883 : Nat := 271282270543602803566133

theorem tailTrace_4754883 : CollatzResearch.WordTrace tailWord_4754883 prefixEnd_4754883 271282270543602803566133 := by
  unfold tailWord_4754883
  simp only [CollatzResearch.WordTrace]
  refine ⟨173424830432878435209365303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115616553621918956806243535 173424830432878435209365303)
  ·
    refine ⟨260137245649317652814047955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173424830432878435209365303 260137245649317652814047955)
    ·
      refine ⟨390205868473976479221071933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260137245649317652814047955 390205868473976479221071933)
      ·
        refine ⟨146327200677741179707901975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 390205868473976479221071933 146327200677741179707901975)
        ·
          refine ⟨219490801016611769561852963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146327200677741179707901975 219490801016611769561852963)
          ·
            refine ⟨329236201524917654342779445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219490801016611769561852963 329236201524917654342779445)
            ·
              refine ⟨30865893892961030094635573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 329236201524917654342779445 30865893892961030094635573)
              ·
                refine ⟨2893677552465096571372085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30865893892961030094635573 2893677552465096571372085)
                ·
                  refine ⟨271282270543602803566133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2893677552465096571372085 271282270543602803566133)
                  ·
                    rfl

theorem cell23_4754883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 5, 5].length) (baseStart_4754883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4754883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4754883 prefixEnd_4754883 := by exact prefixLift 4754883
  have htrace : WordTrace (prefixWord ++ tailWord_4754883) baseStart_4754883 baseEnd_4754883 := by
    simpa [prefixWord, tailWord_4754883, baseEnd_4754883] using wordTrace_append hprefix tailTrace_4754883
  have hstable : (prefixWord ++ tailWord_4754883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4754883).length < 2 ^ (prefixWord ++ tailWord_4754883).sum := by decide
  have hdescent : baseEnd_4754883 < baseStart_4754883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4754883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4754900 : List Nat := [2, 4, 1, 2, 3, 1, 2, 1, 7]
def baseStart_4754900 : Nat := 118140960795 + 4754900 * 2 ^ 59
def prefixEnd_4754900 : Nat := 4983230072969 + 3 ^ 40 * 4754900 * 2
def baseEnd_4754900 : Nat := 271283240451505740620291

theorem tailTrace_4754900 : CollatzResearch.WordTrace tailWord_4754900 prefixEnd_4754900 271283240451505740620291 := by
  unfold tailWord_4754900
  simp only [CollatzResearch.WordTrace]
  refine ⟨86712725236908423556367077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115616966982544564741822769 86712725236908423556367077)
  ·
    refine ⟨16258635981920329416818827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86712725236908423556367077 16258635981920329416818827)
    ·
      refine ⟨24387953972880494125228241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16258635981920329416818827 24387953972880494125228241)
      ·
        refine ⟨18290965479660370593921181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24387953972880494125228241 18290965479660370593921181)
        ·
          refine ⟨6859112054872638972720443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18290965479660370593921181 6859112054872638972720443)
          ·
            refine ⟨10288668082308958459080665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6859112054872638972720443 10288668082308958459080665)
            ·
              refine ⟨7716501061731718844310499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10288668082308958459080665 7716501061731718844310499)
              ·
                refine ⟨11574751592597578266465749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7716501061731718844310499 11574751592597578266465749)
                ·
                  refine ⟨271283240451505740620291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11574751592597578266465749 271283240451505740620291)
                  ·
                    rfl

theorem cell23_4754900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_4754900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4754900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4754900 prefixEnd_4754900 := by exact prefixLift 4754900
  have htrace : WordTrace (prefixWord ++ tailWord_4754900) baseStart_4754900 baseEnd_4754900 := by
    simpa [prefixWord, tailWord_4754900, baseEnd_4754900] using wordTrace_append hprefix tailTrace_4754900
  have hstable : (prefixWord ++ tailWord_4754900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4754900).length < 2 ^ (prefixWord ++ tailWord_4754900).sum := by decide
  have hdescent : baseEnd_4754900 < baseStart_4754900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4754900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4754903 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 1, 7, 2]
def baseStart_4754903 : Nat := 118140960795 + 4754903 * 2 ^ 59
def prefixEnd_4754903 : Nat := 4983230072969 + 3 ^ 40 * 4754903 * 2
def baseEnd_4754903 : Nat := 2441550704505515153845105

theorem tailTrace_4754903 : CollatzResearch.WordTrace tailWord_4754903 prefixEnd_4754903 2441550704505515153845105 := by
  unfold tailWord_4754903
  simp only [CollatzResearch.WordTrace]
  refine ⟨173425559892805978625093363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115617039928537319083395575 173425559892805978625093363)
  ·
    refine ⟨260138339839208967937640045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173425559892805978625093363 260138339839208967937640045)
    ·
      refine ⟨97551877439703362976615017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 260138339839208967937640045 97551877439703362976615017)
      ·
        refine ⟨73163908079777522232461263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97551877439703362976615017 73163908079777522232461263)
        ·
          refine ⟨109745862119666283348691895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73163908079777522232461263 109745862119666283348691895)
          ·
            refine ⟨164618793179499425023037843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109745862119666283348691895 164618793179499425023037843)
            ·
              refine ⟨246928189769249137534556765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164618793179499425023037843 246928189769249137534556765)
              ·
                refine ⟨92598071163468426575458787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 246928189769249137534556765 92598071163468426575458787)
                ·
                  refine ⟨138897106745202639863188181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92598071163468426575458787 138897106745202639863188181)
                  ·
                    refine ⟨3255400939340686871793473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 138897106745202639863188181 3255400939340686871793473)
                    ·
                      refine ⟨2441550704505515153845105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3255400939340686871793473 2441550704505515153845105)
                      ·
                        rfl

theorem cell23_4754903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 7, 2].length) (baseStart_4754903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4754903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4754903 prefixEnd_4754903 := by exact prefixLift 4754903
  have htrace : WordTrace (prefixWord ++ tailWord_4754903) baseStart_4754903 baseEnd_4754903 := by
    simpa [prefixWord, tailWord_4754903, baseEnd_4754903] using wordTrace_append hprefix tailTrace_4754903
  have hstable : (prefixWord ++ tailWord_4754903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4754903).length < 2 ^ (prefixWord ++ tailWord_4754903).sum := by decide
  have hdescent : baseEnd_4754903 < baseStart_4754903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4754903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4755040 : List Nat := [2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 4]
def baseStart_4755040 : Nat := 118140960795 + 4755040 * 2 ^ 59
def prefixEnd_4755040 : Nat := 4983230072969 + 3 ^ 40 * 4755040 * 2
def baseEnd_4755040 : Nat := 2441621051355181117831975

theorem tailTrace_4755040 : CollatzResearch.WordTrace tailWord_4755040 prefixEnd_4755040 2441621051355181117831975 := by
  unfold tailWord_4755040
  simp only [CollatzResearch.WordTrace]
  refine ⟨86715278346654825511415287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115620371128873100681887049 86715278346654825511415287)
  ·
    refine ⟨130072917519982238267122931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86715278346654825511415287 130072917519982238267122931)
    ·
      refine ⟨195109376279973357400684397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130072917519982238267122931 195109376279973357400684397)
      ·
        refine ⟨73166016104990009025256649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195109376279973357400684397 73166016104990009025256649)
        ·
          refine ⟨54874512078742506768942487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73166016104990009025256649 54874512078742506768942487)
          ·
            refine ⟨82311768118113760153413731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54874512078742506768942487 82311768118113760153413731)
            ·
              refine ⟨123467652177170640230120597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82311768118113760153413731 123467652177170640230120597)
              ·
                refine ⟨5787546195804873760786903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 123467652177170640230120597 5787546195804873760786903)
                ·
                  refine ⟨8681319293707310641180355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5787546195804873760786903 8681319293707310641180355)
                  ·
                    refine ⟨13021978940560965961770533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8681319293707310641180355 13021978940560965961770533)
                    ·
                      refine ⟨2441621051355181117831975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13021978940560965961770533 2441621051355181117831975)
                      ·
                        rfl

theorem cell23_4755040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 4].length) (baseStart_4755040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4755040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4755040 prefixEnd_4755040 := by exact prefixLift 4755040
  have htrace : WordTrace (prefixWord ++ tailWord_4755040) baseStart_4755040 baseEnd_4755040 := by
    simpa [prefixWord, tailWord_4755040, baseEnd_4755040] using wordTrace_append hprefix tailTrace_4755040
  have hstable : (prefixWord ++ tailWord_4755040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4755040).length < 2 ^ (prefixWord ++ tailWord_4755040).sum := by decide
  have hdescent : baseEnd_4755040 < baseStart_4755040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4755040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4755044 : List Nat := [2, 3, 1, 1, 2, 5, 1, 1, 2, 3, 2]
def baseStart_4755044 : Nat := 118140960795 + 4755044 * 2 ^ 59
def prefixEnd_4755044 : Nat := 4983230072969 + 3 ^ 40 * 4755044 * 2
def baseEnd_4755044 : Nat := 2441623105277799102181957

theorem tailTrace_4755044 : CollatzResearch.WordTrace tailWord_4755044 prefixEnd_4755044 2441623105277799102181957 := by
  unfold tailWord_4755044
  simp only [CollatzResearch.WordTrace]
  refine ⟨86715351292647579852988093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115620468390196773137317457 86715351292647579852988093)
  ·
    refine ⟨32518256734742842444870535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86715351292647579852988093 32518256734742842444870535)
    ·
      refine ⟨48777385102114263667305803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32518256734742842444870535 48777385102114263667305803)
      ·
        refine ⟨73166077653171395500958705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48777385102114263667305803 73166077653171395500958705)
        ·
          refine ⟨54874558239878546625719029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73166077653171395500958705 54874558239878546625719029)
          ·
            refine ⟨5144489834988613746161159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54874558239878546625719029 5144489834988613746161159)
            ·
              refine ⟨7716734752482920619241739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5144489834988613746161159 7716734752482920619241739)
              ·
                refine ⟨11575102128724380928862609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7716734752482920619241739 11575102128724380928862609)
                ·
                  refine ⟨8681326596543285696646957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11575102128724380928862609 8681326596543285696646957)
                  ·
                    refine ⟨3255497473703732136242609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8681326596543285696646957 3255497473703732136242609)
                    ·
                      refine ⟨2441623105277799102181957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3255497473703732136242609 2441623105277799102181957)
                      ·
                        rfl

theorem cell23_4755044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 2, 3, 2].length) (baseStart_4755044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4755044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4755044 prefixEnd_4755044 := by exact prefixLift 4755044
  have htrace : WordTrace (prefixWord ++ tailWord_4755044) baseStart_4755044 baseEnd_4755044 := by
    simpa [prefixWord, tailWord_4755044, baseEnd_4755044] using wordTrace_append hprefix tailTrace_4755044
  have hstable : (prefixWord ++ tailWord_4755044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4755044).length < 2 ^ (prefixWord ++ tailWord_4755044).sum := by decide
  have hdescent : baseEnd_4755044 < baseStart_4755044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4755044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4755050 : List Nat := [3, 1, 3, 2, 1, 2, 2, 2, 1, 6]
def baseStart_4755050 : Nat := 118140960795 + 4755050 * 2 ^ 59
def prefixEnd_4755050 : Nat := 4983230072969 + 3 ^ 40 * 4755050 * 2
def baseEnd_4755050 : Nat := 813875395387242026235643

theorem tailTrace_4755050 : CollatzResearch.WordTrace tailWord_4755050 prefixEnd_4755050 813875395387242026235643 := by
  unfold tailWord_4755050
  simp only [CollatzResearch.WordTrace]
  refine ⟨43357730355818355682673651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115620614282182281820463069 43357730355818355682673651)
  ·
    refine ⟨65036595533727533524010477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43357730355818355682673651 65036595533727533524010477)
    ·
      refine ⟨24388723325147825071503929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65036595533727533524010477 24388723325147825071503929)
      ·
        refine ⟨18291542493860868803627947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24388723325147825071503929 18291542493860868803627947)
        ·
          refine ⟨27437313740791303205441921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18291542493860868803627947 27437313740791303205441921)
          ·
            refine ⟨20577985305593477404081441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27437313740791303205441921 20577985305593477404081441)
            ·
              refine ⟨15433488979195108053061081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20577985305593477404081441 15433488979195108053061081)
              ·
                refine ⟨11575116734396331039795811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15433488979195108053061081 11575116734396331039795811)
                ·
                  refine ⟨17362675101594496559693717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11575116734396331039795811 17362675101594496559693717)
                  ·
                    refine ⟨813875395387242026235643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17362675101594496559693717 813875395387242026235643)
                    ·
                      rfl

theorem cell23_4755050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_4755050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4755050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4755050 prefixEnd_4755050 := by exact prefixLift 4755050
  have htrace : WordTrace (prefixWord ++ tailWord_4755050) baseStart_4755050 baseEnd_4755050 := by
    simpa [prefixWord, tailWord_4755050, baseEnd_4755050] using wordTrace_append hprefix tailTrace_4755050
  have hstable : (prefixWord ++ tailWord_4755050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4755050).length < 2 ^ (prefixWord ++ tailWord_4755050).sum := by decide
  have hdescent : baseEnd_4755050 < baseStart_4755050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4755050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4755093 : List Nat := [1, 3, 2, 1, 1, 1, 1, 4, 2, 7]
def baseStart_4755093 : Nat := 118140960795 + 4755093 * 2 ^ 59
def prefixEnd_4755093 : Nat := 4983230072969 + 3 ^ 40 * 4755093 * 2
def baseEnd_4755093 : Nat := 813882755276623136823077

theorem tailTrace_4755093 : CollatzResearch.WordTrace tailWord_4755093 prefixEnd_4755093 813882755276623136823077 := by
  unfold tailWord_4755093
  simp only [CollatzResearch.WordTrace]
  refine ⟨173432489762117641074509933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115621659841411760716339955 173432489762117641074509933)
  ·
    refine ⟨65037183660794115402941225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173432489762117641074509933 65037183660794115402941225)
    ·
      refine ⟨48777887745595586552205919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65037183660794115402941225 48777887745595586552205919)
      ·
        refine ⟨73166831618393379828308879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48777887745595586552205919 73166831618393379828308879)
        ·
          refine ⟨109750247427590069742463319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73166831618393379828308879 109750247427590069742463319)
          ·
            refine ⟨164625371141385104613694979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109750247427590069742463319 164625371141385104613694979)
            ·
              refine ⟨246938056712077656920542469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164625371141385104613694979 246938056712077656920542469)
              ·
                refine ⟨46300885633514560672601713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 246938056712077656920542469 46300885633514560672601713)
                ·
                  refine ⟨34725664225135920504451285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46300885633514560672601713 34725664225135920504451285)
                  ·
                    refine ⟨813882755276623136823077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34725664225135920504451285 813882755276623136823077)
                    ·
                      rfl

theorem cell23_4755093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_4755093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4755093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4755093 prefixEnd_4755093 := by exact prefixLift 4755093
  have htrace : WordTrace (prefixWord ++ tailWord_4755093) baseStart_4755093 baseEnd_4755093 := by
    simpa [prefixWord, tailWord_4755093, baseEnd_4755093] using wordTrace_append hprefix tailTrace_4755093
  have hstable : (prefixWord ++ tailWord_4755093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4755093).length < 2 ^ (prefixWord ++ tailWord_4755093).sum := by decide
  have hdescent : baseEnd_4755093 < baseStart_4755093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4755093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4755108 : List Nat := [2, 3, 1, 2, 2, 4, 1, 3, 1, 2, 2]
def baseStart_4755108 : Nat := 118140960795 + 4755108 * 2 ^ 59
def prefixEnd_4755108 : Nat := 4983230072969 + 3 ^ 40 * 4755108 * 2
def baseEnd_4755108 : Nat := 2441655968039686851781663

theorem tailTrace_4755108 : CollatzResearch.WordTrace tailWord_4755108 prefixEnd_4755108 2441655968039686851781663 := by
  unfold tailWord_4755108
  simp only [CollatzResearch.WordTrace]
  refine ⟨86716518428531649318152989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115622024571375532424203985 86716518428531649318152989)
  ·
    refine ⟨32518694410699368494307371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86716518428531649318152989 32518694410699368494307371)
    ·
      refine ⟨48778041616049052741461057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32518694410699368494307371 48778041616049052741461057)
      ·
        refine ⟨36583531212036789556095793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48778041616049052741461057 36583531212036789556095793)
        ·
          refine ⟨27437648409027592167071845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36583531212036789556095793 27437648409027592167071845)
          ·
            refine ⟨5144559076692673531325971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27437648409027592167071845 5144559076692673531325971)
            ·
              refine ⟨7716838615039010296988957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5144559076692673531325971 7716838615039010296988957)
              ·
                refine ⟨2893814480639628861370859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7716838615039010296988957 2893814480639628861370859)
                ·
                  refine ⟨4340721720959443292056289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2893814480639628861370859 4340721720959443292056289)
                  ·
                    refine ⟨3255541290719582469042217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4340721720959443292056289 3255541290719582469042217)
                    ·
                      refine ⟨2441655968039686851781663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3255541290719582469042217 2441655968039686851781663)
                      ·
                        rfl

theorem cell23_4755108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 3, 1, 2, 2].length) (baseStart_4755108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4755108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4755108 prefixEnd_4755108 := by exact prefixLift 4755108
  have htrace : WordTrace (prefixWord ++ tailWord_4755108) baseStart_4755108 baseEnd_4755108 := by
    simpa [prefixWord, tailWord_4755108, baseEnd_4755108] using wordTrace_append hprefix tailTrace_4755108
  have hstable : (prefixWord ++ tailWord_4755108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4755108).length < 2 ^ (prefixWord ++ tailWord_4755108).sum := by decide
  have hdescent : baseEnd_4755108 < baseStart_4755108 := by decide
  rcases family_descends (prefixWord ++ tailWord_4755108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4755125 : List Nat := [1, 3, 3, 3, 2, 1, 3, 2, 1, 2, 2]
def baseStart_4755125 : Nat := 118140960795 + 4755125 * 2 ^ 59
def prefixEnd_4755125 : Nat := 4983230072969 + 3 ^ 40 * 4755125 * 2
def baseEnd_4755125 : Nat := 2441664697210813285269085

theorem tailTrace_4755125 : CollatzResearch.WordTrace tailWord_4755125 prefixEnd_4755125 2441664697210813285269085 := by
  unfold tailWord_4755125
  simp only [CollatzResearch.WordTrace]
  refine ⟨173433656898001710539674829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115622437932001140359783219 173433656898001710539674829)
  ·
    refine ⟨65037621336750641452378061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173433656898001710539674829 65037621336750641452378061)
    ·
      refine ⟨24389108001281490544641773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65037621336750641452378061 24389108001281490544641773)
      ·
        refine ⟨9145915500480558954240665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24389108001281490544641773 9145915500480558954240665)
        ·
          refine ⟨6859436625360419215680499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9145915500480558954240665 6859436625360419215680499)
          ·
            refine ⟨10289154938040628823520749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6859436625360419215680499 10289154938040628823520749)
            ·
              refine ⟨3858433101765235808820281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10289154938040628823520749 3858433101765235808820281)
              ·
                refine ⟨2893824826323926856615211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3858433101765235808820281 2893824826323926856615211)
                ·
                  refine ⟨4340737239485890284922817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2893824826323926856615211 4340737239485890284922817)
                  ·
                    refine ⟨3255552929614417713692113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4340737239485890284922817 3255552929614417713692113)
                    ·
                      refine ⟨2441664697210813285269085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3255552929614417713692113 2441664697210813285269085)
                      ·
                        rfl

theorem cell23_4755125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_4755125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4755125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4755125 prefixEnd_4755125 := by exact prefixLift 4755125
  have htrace : WordTrace (prefixWord ++ tailWord_4755125) baseStart_4755125 baseEnd_4755125 := by
    simpa [prefixWord, tailWord_4755125, baseEnd_4755125] using wordTrace_append hprefix tailTrace_4755125
  have hstable : (prefixWord ++ tailWord_4755125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4755125).length < 2 ^ (prefixWord ++ tailWord_4755125).sum := by decide
  have hdescent : baseEnd_4755125 < baseStart_4755125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4755125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4755140 : List Nat := [2, 3, 3, 1, 1, 1, 2, 1, 1, 8]
def baseStart_4755140 : Nat := 118140960795 + 4755140 * 2 ^ 59
def prefixEnd_4755140 : Nat := 4983230072969 + 3 ^ 40 * 4755140 * 2
def baseEnd_4755140 : Nat := 813890799806876908860505

theorem tailTrace_4755140 : CollatzResearch.WordTrace tailWord_4755140 prefixEnd_4755140 813890799806876908860505 := by
  unfold tailWord_4755140
  simp only [CollatzResearch.WordTrace]
  refine ⟨86717101996473684050735437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115622802661964912067647249 86717101996473684050735437)
  ·
    refine ⟨32518913248677631519025789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86717101996473684050735437 32518913248677631519025789)
    ·
      refine ⟨12194592468254111819634671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32518913248677631519025789 12194592468254111819634671)
      ·
        refine ⟨18291888702381167729452007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12194592468254111819634671 18291888702381167729452007)
        ·
          refine ⟨27437833053571751594178011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18291888702381167729452007 27437833053571751594178011)
          ·
            refine ⟨41156749580357627391267017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27437833053571751594178011 41156749580357627391267017)
            ·
              refine ⟨30867562185268220543450263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41156749580357627391267017 30867562185268220543450263)
              ·
                refine ⟨46301343277902330815175395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30867562185268220543450263 46301343277902330815175395)
                ·
                  refine ⟨69452014916853496222763093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46301343277902330815175395 69452014916853496222763093)
                  ·
                    refine ⟨813890799806876908860505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 69452014916853496222763093 813890799806876908860505)
                    ·
                      rfl

theorem cell23_4755140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_4755140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4755140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4755140 prefixEnd_4755140 := by exact prefixLift 4755140
  have htrace : WordTrace (prefixWord ++ tailWord_4755140) baseStart_4755140 baseEnd_4755140 := by
    simpa [prefixWord, tailWord_4755140, baseEnd_4755140] using wordTrace_append hprefix tailTrace_4755140
  have hstable : (prefixWord ++ tailWord_4755140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4755140).length < 2 ^ (prefixWord ++ tailWord_4755140).sum := by decide
  have hdescent : baseEnd_4755140 < baseStart_4755140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4755140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4755150 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5]
def baseStart_4755150 : Nat := 118140960795 + 4755150 * 2 ^ 59
def prefixEnd_4755150 : Nat := 4983230072969 + 3 ^ 40 * 4755150 * 2
def baseEnd_4755150 : Nat := 2441677534227175687456469

theorem tailTrace_4755150 : CollatzResearch.WordTrace tailWord_4755150 prefixEnd_4755150 2441677534227175687456469 := by
  unfold tailWord_4755150
  simp only [CollatzResearch.WordTrace]
  refine ⟨21679321090363892476166863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115623045815274093206223269 21679321090363892476166863)
  ·
    refine ⟨32518981635545838714250295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21679321090363892476166863 32518981635545838714250295)
    ·
      refine ⟨48778472453318758071375443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32518981635545838714250295 48778472453318758071375443)
      ·
        refine ⟨73167708679978137107063165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48778472453318758071375443 73167708679978137107063165)
        ·
          refine ⟨27437890754991801415148687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73167708679978137107063165 27437890754991801415148687)
          ·
            refine ⟨41156836132487702122723031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27437890754991801415148687 41156836132487702122723031)
            ·
              refine ⟨61735254198731553184084547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41156836132487702122723031 61735254198731553184084547)
              ·
                refine ⟨92602881298097329776126821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61735254198731553184084547 92602881298097329776126821)
                ·
                  refine ⟨17363040243393249333023779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92602881298097329776126821 17363040243393249333023779)
                  ·
                    refine ⟨26044560365089873999535669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17363040243393249333023779 26044560365089873999535669)
                    ·
                      refine ⟨2441677534227175687456469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26044560365089873999535669 2441677534227175687456469)
                      ·
                        rfl

theorem cell23_4755150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_4755150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4755150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4755150 prefixEnd_4755150 := by exact prefixLift 4755150
  have htrace : WordTrace (prefixWord ++ tailWord_4755150) baseStart_4755150 baseEnd_4755150 := by
    simpa [prefixWord, tailWord_4755150, baseEnd_4755150] using wordTrace_append hprefix tailTrace_4755150
  have hstable : (prefixWord ++ tailWord_4755150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4755150).length < 2 ^ (prefixWord ++ tailWord_4755150).sum := by decide
  have hdescent : baseEnd_4755150 < baseStart_4755150 := by decide
  rcases family_descends (prefixWord ++ tailWord_4755150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4755181 : List Nat := [1, 5, 1, 2, 1, 2, 1, 4, 2, 2, 2]
def baseStart_4755181 : Nat := 118140960795 + 4755181 * 2 ^ 59
def prefixEnd_4755181 : Nat := 4983230072969 + 3 ^ 40 * 4755181 * 2
def baseEnd_4755181 : Nat := 2441693452127465066168827

theorem tailTrace_4755181 : CollatzResearch.WordTrace tailWord_4755181 prefixEnd_4755181 2441693452127465066168827 := by
  unfold tailWord_4755181
  simp only [CollatzResearch.WordTrace]
  refine ⟨173435699385798832103713397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115623799590532554735808931 173435699385798832103713397)
  ·
    refine ⟨16259596817418640509723131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 173435699385798832103713397 16259596817418640509723131)
    ·
      refine ⟨24389395226127960764584697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16259596817418640509723131 24389395226127960764584697)
      ·
        refine ⟨18292046419595970573438523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24389395226127960764584697 18292046419595970573438523)
        ·
          refine ⟨27438069629393955860157785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18292046419595970573438523 27438069629393955860157785)
          ·
            refine ⟨20578552222045466895118339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27438069629393955860157785 20578552222045466895118339)
            ·
              refine ⟨30867828333068200342677509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20578552222045466895118339 30867828333068200342677509)
              ·
                refine ⟨5787717812450287564252033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30867828333068200342677509 5787717812450287564252033)
                ·
                  refine ⟨4340788359337715673189025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5787717812450287564252033 4340788359337715673189025)
                  ·
                    refine ⟨3255591269503286754891769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4340788359337715673189025 3255591269503286754891769)
                    ·
                      refine ⟨2441693452127465066168827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3255591269503286754891769 2441693452127465066168827)
                      ·
                        rfl

theorem cell23_4755181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_4755181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4755181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4755181 prefixEnd_4755181 := by exact prefixLift 4755181
  have htrace : WordTrace (prefixWord ++ tailWord_4755181) baseStart_4755181 baseEnd_4755181 := by
    simpa [prefixWord, tailWord_4755181, baseEnd_4755181] using wordTrace_append hprefix tailTrace_4755181
  have hstable : (prefixWord ++ tailWord_4755181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4755181).length < 2 ^ (prefixWord ++ tailWord_4755181).sum := by decide
  have hdescent : baseEnd_4755181 < baseStart_4755181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4755181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4755254 : List Nat := [5, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4]
def baseStart_4755254 : Nat := 118140960795 + 4755254 * 2 ^ 59
def prefixEnd_4755254 : Nat := 4983230072969 + 3 ^ 40 * 4755254 * 2
def baseEnd_4755254 : Nat := 2441730936215243280555991

theorem tailTrace_4755254 : CollatzResearch.WordTrace tailWord_4755254 prefixEnd_4755254 2441730936215243280555991 := by
  unfold tailWord_4755254
  simp only [CollatzResearch.WordTrace]
  refine ⟨10839897619658397848195051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115625574609689577047413877 10839897619658397848195051)
  ·
    refine ⟨16259846429487596772292577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10839897619658397848195051 16259846429487596772292577)
    ·
      refine ⟨12194884822115697579219433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16259846429487596772292577 12194884822115697579219433)
      ·
        refine ⟨9146163616586773184414575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12194884822115697579219433 9146163616586773184414575)
        ·
          refine ⟨13719245424880159776621863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9146163616586773184414575 13719245424880159776621863)
          ·
            refine ⟨20578868137320239664932795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13719245424880159776621863 20578868137320239664932795)
            ·
              refine ⟨30868302205980359497399193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20578868137320239664932795 30868302205980359497399193)
              ·
                refine ⟨23151226654485269623049395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30868302205980359497399193 23151226654485269623049395)
                ·
                  refine ⟨34726839981727904434574093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23151226654485269623049395 34726839981727904434574093)
                  ·
                    refine ⟨13022564993147964162965285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34726839981727904434574093 13022564993147964162965285)
                    ·
                      refine ⟨2441730936215243280555991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13022564993147964162965285 2441730936215243280555991)
                      ·
                        rfl

theorem cell23_4755254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_4755254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4755254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4755254 prefixEnd_4755254 := by exact prefixLift 4755254
  have htrace : WordTrace (prefixWord ++ tailWord_4755254) baseStart_4755254 baseEnd_4755254 := by
    simpa [prefixWord, tailWord_4755254, baseEnd_4755254] using wordTrace_append hprefix tailTrace_4755254
  have hstable : (prefixWord ++ tailWord_4755254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4755254).length < 2 ^ (prefixWord ++ tailWord_4755254).sum := by decide
  have hdescent : baseEnd_4755254 < baseStart_4755254 := by decide
  rcases family_descends (prefixWord ++ tailWord_4755254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4755281 : List Nat := [1, 2, 2, 1, 5, 1, 3, 3, 1, 4]
def baseStart_4755281 : Nat := 118140960795 + 4755281 * 2 ^ 59
def prefixEnd_4755281 : Nat := 4983230072969 + 3 ^ 40 * 4755281 * 2
def baseEnd_4755281 : Nat := 813914933397638224972789

theorem tailTrace_4755281 : CollatzResearch.WordTrace tailWord_4755281 prefixEnd_4755281 813914933397638224972789 := by
  unfold tailWord_4755281
  simp only [CollatzResearch.WordTrace]
  refine ⟨173439346685436549182353697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115626231123624366121569131 173439346685436549182353697)
  ·
    refine ⟨130079510014077411886765273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173439346685436549182353697 130079510014077411886765273)
    ·
      refine ⟨97559632510558058915073955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130079510014077411886765273 97559632510558058915073955)
      ·
        refine ⟨146339448765837088372610933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97559632510558058915073955 146339448765837088372610933)
        ·
          refine ⟨13719323321797227034932275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 146339448765837088372610933 13719323321797227034932275)
          ·
            refine ⟨20578984982695840552398413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13719323321797227034932275 20578984982695840552398413)
            ·
              refine ⟨7717119368510940207149405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20578984982695840552398413 7717119368510940207149405)
              ·
                refine ⟨2893919763191602577681027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7717119368510940207149405 2893919763191602577681027)
                ·
                  refine ⟨4340879644787403866521541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2893919763191602577681027 4340879644787403866521541)
                  ·
                    refine ⟨813914933397638224972789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4340879644787403866521541 813914933397638224972789)
                    ·
                      rfl

theorem cell23_4755281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 3, 1, 4].length) (baseStart_4755281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4755281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4755281 prefixEnd_4755281 := by exact prefixLift 4755281
  have htrace : WordTrace (prefixWord ++ tailWord_4755281) baseStart_4755281 baseEnd_4755281 := by
    simpa [prefixWord, tailWord_4755281, baseEnd_4755281] using wordTrace_append hprefix tailTrace_4755281
  have hstable : (prefixWord ++ tailWord_4755281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4755281).length < 2 ^ (prefixWord ++ tailWord_4755281).sum := by decide
  have hdescent : baseEnd_4755281 < baseStart_4755281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4755281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4755314 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 6, 3, 2]
def baseStart_4755314 : Nat := 118140960795 + 4755314 * 2 ^ 59
def prefixEnd_4755314 : Nat := 4983230072969 + 3 ^ 40 * 4755314 * 2
def baseEnd_4755314 : Nat := 2441761745054513045805715

theorem tailTrace_4755314 : CollatzResearch.WordTrace tailWord_4755314 prefixEnd_4755314 2441761745054513045805715 := by
  unfold tailWord_4755314
  simp only [CollatzResearch.WordTrace]
  refine ⟨43360137573579248954576249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115627033529544663878869997 43360137573579248954576249)
  ·
    refine ⟨32520103180184436715932187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43360137573579248954576249 32520103180184436715932187)
    ·
      refine ⟨48780154770276655073898281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32520103180184436715932187 48780154770276655073898281)
      ·
        refine ⟨36585116077707491305423711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48780154770276655073898281 36585116077707491305423711)
        ·
          refine ⟨54877674116561236958135567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36585116077707491305423711 54877674116561236958135567)
          ·
            refine ⟨82316511174841855437203351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54877674116561236958135567 82316511174841855437203351)
            ·
              refine ⟨123474766762262783155805027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82316511174841855437203351 123474766762262783155805027)
              ·
                refine ⟨185212150143394174733707541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123474766762262783155805027 185212150143394174733707541)
                ·
                  refine ⟨8681819537971601940642541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 185212150143394174733707541 8681819537971601940642541)
                  ·
                    refine ⟨3255682326739350727740953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8681819537971601940642541 3255682326739350727740953)
                    ·
                      refine ⟨2441761745054513045805715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3255682326739350727740953 2441761745054513045805715)
                      ·
                        rfl

theorem cell23_4755314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 6, 3, 2].length) (baseStart_4755314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4755314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4755314 prefixEnd_4755314 := by exact prefixLift 4755314
  have htrace : WordTrace (prefixWord ++ tailWord_4755314) baseStart_4755314 baseEnd_4755314 := by
    simpa [prefixWord, tailWord_4755314, baseEnd_4755314] using wordTrace_append hprefix tailTrace_4755314
  have hstable : (prefixWord ++ tailWord_4755314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4755314).length < 2 ^ (prefixWord ++ tailWord_4755314).sum := by decide
  have hdescent : baseEnd_4755314 < baseStart_4755314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4755314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4755331 : List Nat := [1, 1, 1, 3, 4, 3, 2, 1, 2, 3, 2]
def baseStart_4755331 : Nat := 118140960795 + 4755331 * 2 ^ 59
def prefixEnd_4755331 : Nat := 4983230072969 + 3 ^ 40 * 4755331 * 2
def baseEnd_4755331 : Nat := 2441770474225639479293137

theorem tailTrace_4755331 : CollatzResearch.WordTrace tailWord_4755331 prefixEnd_4755331 2441770474225639479293137 := by
  unfold tailWord_4755331
  simp only [CollatzResearch.WordTrace]
  refine ⟨173441170335255407721673847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115627446890170271814449231 173441170335255407721673847)
  ·
    refine ⟨260161755502883111582510771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173441170335255407721673847 260161755502883111582510771)
    ·
      refine ⟨390242633254324667373766157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260161755502883111582510771 390242633254324667373766157)
      ·
        refine ⟨146340987470371750265162309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 390242633254324667373766157 146340987470371750265162309)
        ·
          refine ⟨27438935150694703174717933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 146340987470371750265162309 27438935150694703174717933)
          ·
            refine ⟨10289600681510513690519225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27438935150694703174717933 10289600681510513690519225)
            ·
              refine ⟨7717200511132885267889419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10289600681510513690519225 7717200511132885267889419)
              ·
                refine ⟨11575800766699327901834129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7717200511132885267889419 11575800766699327901834129)
                ·
                  refine ⟨8681850575024495926375597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11575800766699327901834129 8681850575024495926375597)
                  ·
                    refine ⟨3255693965634185972390849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8681850575024495926375597 3255693965634185972390849)
                    ·
                      refine ⟨2441770474225639479293137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3255693965634185972390849 2441770474225639479293137)
                      ·
                        rfl

theorem cell23_4755331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 2, 3, 2].length) (baseStart_4755331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4755331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4755331 prefixEnd_4755331 := by exact prefixLift 4755331
  have htrace : WordTrace (prefixWord ++ tailWord_4755331) baseStart_4755331 baseEnd_4755331 := by
    simpa [prefixWord, tailWord_4755331, baseEnd_4755331] using wordTrace_append hprefix tailTrace_4755331
  have hstable : (prefixWord ++ tailWord_4755331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4755331).length < 2 ^ (prefixWord ++ tailWord_4755331).sum := by decide
  have hdescent : baseEnd_4755331 < baseStart_4755331 := by decide
  rcases family_descends (prefixWord ++ tailWord_4755331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4755337 : List Nat := [1, 2, 1, 1, 5, 1, 3, 2, 1, 6]
def baseStart_4755337 : Nat := 118140960795 + 4755337 * 2 ^ 59
def prefixEnd_4755337 : Nat := 4983230072969 + 3 ^ 40 * 4755337 * 2
def baseEnd_4755337 : Nat := 813924518369855485272703

theorem tailTrace_4755337 : CollatzResearch.WordTrace tailWord_4755337 prefixEnd_4755337 813924518369855485272703 := by
  unfold tailWord_4755337
  simp only [CollatzResearch.WordTrace]
  refine ⟨173441389173233670746392265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115627592782155780497594843 173441389173233670746392265)
  ·
    refine ⟨130081041879925253059794199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173441389173233670746392265 130081041879925253059794199)
    ·
      refine ⟨195121562819887879589691299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130081041879925253059794199 195121562819887879589691299)
      ·
        refine ⟨292682344229831819384536949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195121562819887879589691299 292682344229831819384536949)
        ·
          refine ⟨27438969771546733067300339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 292682344229831819384536949 27438969771546733067300339)
          ·
            refine ⟨41158454657320099600950509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27438969771546733067300339 41158454657320099600950509)
            ·
              refine ⟨15434420496495037350356441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41158454657320099600950509 15434420496495037350356441)
              ·
                refine ⟨11575815372371278012767331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15434420496495037350356441 11575815372371278012767331)
                ·
                  refine ⟨17363723058556917019150997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11575815372371278012767331 17363723058556917019150997)
                  ·
                    refine ⟨813924518369855485272703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17363723058556917019150997 813924518369855485272703)
                    ·
                      rfl

theorem cell23_4755337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 6].length) (baseStart_4755337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4755337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4755337 prefixEnd_4755337 := by exact prefixLift 4755337
  have htrace : WordTrace (prefixWord ++ tailWord_4755337) baseStart_4755337 baseEnd_4755337 := by
    simpa [prefixWord, tailWord_4755337, baseEnd_4755337] using wordTrace_append hprefix tailTrace_4755337
  have hstable : (prefixWord ++ tailWord_4755337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4755337).length < 2 ^ (prefixWord ++ tailWord_4755337).sum := by decide
  have hdescent : baseEnd_4755337 < baseStart_4755337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4755337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4755364 : List Nat := [2, 3, 1, 2, 1, 3, 1, 2, 3, 2, 3]
def baseStart_4755364 : Nat := 118140960795 + 4755364 * 2 ^ 59
def prefixEnd_4755364 : Nat := 4983230072969 + 3 ^ 40 * 4755364 * 2
def baseEnd_4755364 : Nat := 2441787419087237850180485

theorem tailTrace_4755364 : CollatzResearch.WordTrace tailWord_4755364 prefixEnd_4755364 2441787419087237850180485 := by
  unfold tailWord_4755364
  simp only [CollatzResearch.WordTrace]
  refine ⟨86721186972067927178812573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115628249296090569571750097 86721186972067927178812573)
  ·
    refine ⟨32520445114525472692054715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86721186972067927178812573 32520445114525472692054715)
    ·
      refine ⟨48780667671788209038082073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32520445114525472692054715 48780667671788209038082073)
      ·
        refine ⟨36585500753841156778561555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48780667671788209038082073 36585500753841156778561555)
        ·
          refine ⟨54878251130761735167842333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36585500753841156778561555 54878251130761735167842333)
          ·
            refine ⟨20579344174035650687940875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54878251130761735167842333 20579344174035650687940875)
            ·
              refine ⟨30869016261053476031911313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20579344174035650687940875 30869016261053476031911313)
              ·
                refine ⟨23151762195790107023933485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30869016261053476031911313 23151762195790107023933485)
                ·
                  refine ⟨8681910823421290133975057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23151762195790107023933485 8681910823421290133975057)
                  ·
                    refine ⟨6511433117565967600481293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8681910823421290133975057 6511433117565967600481293)
                    ·
                      refine ⟨2441787419087237850180485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6511433117565967600481293 2441787419087237850180485)
                      ·
                        rfl

theorem cell23_4755364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_4755364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4755364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4755364 prefixEnd_4755364 := by exact prefixLift 4755364
  have htrace : WordTrace (prefixWord ++ tailWord_4755364) baseStart_4755364 baseEnd_4755364 := by
    simpa [prefixWord, tailWord_4755364, baseEnd_4755364] using wordTrace_append hprefix tailTrace_4755364
  have hstable : (prefixWord ++ tailWord_4755364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4755364).length < 2 ^ (prefixWord ++ tailWord_4755364).sum := by decide
  have hdescent : baseEnd_4755364 < baseStart_4755364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4755364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4755428 : List Nat := [2, 3, 1, 1, 1, 1, 7, 1, 2, 1, 3]
def baseStart_4755428 : Nat := 118140960795 + 4755428 * 2 ^ 59
def prefixEnd_4755428 : Nat := 4983230072969 + 3 ^ 40 * 4755428 * 2
def baseEnd_4755428 : Nat := 2441820281849125599780191

theorem tailTrace_4755428 : CollatzResearch.WordTrace tailWord_4755428 prefixEnd_4755428 2441820281849125599780191 := by
  unfold tailWord_4755428
  simp only [CollatzResearch.WordTrace]
  refine ⟨86722354107951996643977469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115629805477269328858636625 86722354107951996643977469)
  ·
    refine ⟨32520882790481998741491551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86722354107951996643977469 32520882790481998741491551)
    ·
      refine ⟨48781324185722998112237327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32520882790481998741491551 48781324185722998112237327)
      ·
        refine ⟨73171986278584497168355991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48781324185722998112237327 73171986278584497168355991)
        ·
          refine ⟨109757979417876745752533987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73171986278584497168355991 109757979417876745752533987)
          ·
            refine ⟨164636969126815118628800981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109757979417876745752533987 164636969126815118628800981)
            ·
              refine ⟨3858678963909729342862523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 164636969126815118628800981 3858678963909729342862523)
              ·
                refine ⟨5788018445864594014293785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3858678963909729342862523 5788018445864594014293785)
                ·
                  refine ⟨4341013834398445510720339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5788018445864594014293785 4341013834398445510720339)
                  ·
                    refine ⟨6511520751597668266080509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4341013834398445510720339 6511520751597668266080509)
                    ·
                      refine ⟨2441820281849125599780191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6511520751597668266080509 2441820281849125599780191)
                      ·
                        rfl

theorem cell23_4755428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 1, 2, 1, 3].length) (baseStart_4755428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4755428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4755428 prefixEnd_4755428 := by exact prefixLift 4755428
  have htrace : WordTrace (prefixWord ++ tailWord_4755428) baseStart_4755428 baseEnd_4755428 := by
    simpa [prefixWord, tailWord_4755428, baseEnd_4755428] using wordTrace_append hprefix tailTrace_4755428
  have hstable : (prefixWord ++ tailWord_4755428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4755428).length < 2 ^ (prefixWord ++ tailWord_4755428).sum := by decide
  have hdescent : baseEnd_4755428 < baseStart_4755428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4755428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4755438 : List Nat := [4, 1, 2, 1, 3, 1, 1, 4, 1, 3, 2]
def baseStart_4755438 : Nat := 118140960795 + 4755438 * 2 ^ 59
def prefixEnd_4755438 : Nat := 4983230072969 + 3 ^ 40 * 4755438 * 2
def baseEnd_4755438 : Nat := 2441825416655670560655145

theorem tailTrace_4755438 : CollatzResearch.WordTrace tailWord_4755438 prefixEnd_4755438 2441825416655670560655145 := by
  unfold tailWord_4755438
  simp only [CollatzResearch.WordTrace]
  refine ⟨21680634118233470624477371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115630048630578509997212645 21680634118233470624477371)
  ·
    refine ⟨32520951177350205936716057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21680634118233470624477371 32520951177350205936716057)
    ·
      refine ⟨24390713383012654452537043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32520951177350205936716057 24390713383012654452537043)
      ·
        refine ⟨36586070074518981678805565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24390713383012654452537043 36586070074518981678805565)
        ·
          refine ⟨13719776277944618129552087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36586070074518981678805565 13719776277944618129552087)
          ·
            refine ⟨20579664416916927194328131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13719776277944618129552087 20579664416916927194328131)
            ·
              refine ⟨30869496625375390791492197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20579664416916927194328131 30869496625375390791492197)
              ·
                refine ⟨5788030617257885773404787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30869496625375390791492197 5788030617257885773404787)
                ·
                  refine ⟨8682045925886828660107181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5788030617257885773404787 8682045925886828660107181)
                  ·
                    refine ⟨3255767222207560747540193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8682045925886828660107181 3255767222207560747540193)
                    ·
                      refine ⟨2441825416655670560655145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3255767222207560747540193 2441825416655670560655145)
                      ·
                        rfl

theorem cell23_4755438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4, 1, 3, 2].length) (baseStart_4755438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4755438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4755438 prefixEnd_4755438 := by exact prefixLift 4755438
  have htrace : WordTrace (prefixWord ++ tailWord_4755438) baseStart_4755438 baseEnd_4755438 := by
    simpa [prefixWord, tailWord_4755438, baseEnd_4755438] using wordTrace_append hprefix tailTrace_4755438
  have hstable : (prefixWord ++ tailWord_4755438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4755438).length < 2 ^ (prefixWord ++ tailWord_4755438).sum := by decide
  have hdescent : baseEnd_4755438 < baseStart_4755438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4755438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4755451 : List Nat := [1, 1, 1, 1, 1, 3, 5, 2, 4, 2, 2]
def baseStart_4755451 : Nat := 118140960795 + 4755451 * 2 ^ 59
def prefixEnd_4755451 : Nat := 4983230072969 + 3 ^ 40 * 4755451 * 2
def baseEnd_4755451 : Nat := 2441832091904179009792585

theorem tailTrace_4755451 : CollatzResearch.WordTrace tailWord_4755451 prefixEnd_4755451 2441832091904179009792585 := by
  unfold tailWord_4755451
  simp only [CollatzResearch.WordTrace]
  refine ⟨173445547094820668216042207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115630364729880445477361471 173445547094820668216042207)
  ·
    refine ⟨260168320642231002324063311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173445547094820668216042207 260168320642231002324063311)
    ·
      refine ⟨390252480963346503486094967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260168320642231002324063311 390252480963346503486094967)
      ·
        refine ⟨585378721445019755229142451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390252480963346503486094967 585378721445019755229142451)
        ·
          refine ⟨878068082167529632843713677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 585378721445019755229142451 878068082167529632843713677)
          ·
            refine ⟨329275530812823612316392629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 878068082167529632843713677 329275530812823612316392629)
            ·
              refine ⟨30869581013702213654661809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 329275530812823612316392629 30869581013702213654661809)
              ·
                refine ⟨23152185760276660240996357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30869581013702213654661809 23152185760276660240996357)
                ·
                  refine ⟨4341034830051873795186817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23152185760276660240996357 4341034830051873795186817)
                  ·
                    refine ⟨3255776122538905346390113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4341034830051873795186817 3255776122538905346390113)
                    ·
                      refine ⟨2441832091904179009792585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3255776122538905346390113 2441832091904179009792585)
                      ·
                        rfl

theorem cell23_4755451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 4, 2, 2].length) (baseStart_4755451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4755451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4755451 prefixEnd_4755451 := by exact prefixLift 4755451
  have htrace : WordTrace (prefixWord ++ tailWord_4755451) baseStart_4755451 baseEnd_4755451 := by
    simpa [prefixWord, tailWord_4755451, baseEnd_4755451] using wordTrace_append hprefix tailTrace_4755451
  have hstable : (prefixWord ++ tailWord_4755451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4755451).length < 2 ^ (prefixWord ++ tailWord_4755451).sum := by decide
  have hdescent : baseEnd_4755451 < baseStart_4755451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4755451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4755467 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 7]
def baseStart_4755467 : Nat := 118140960795 + 4755467 * 2 ^ 59
def prefixEnd_4755467 : Nat := 4983230072969 + 3 ^ 40 * 4755467 * 2
def baseEnd_4755467 : Nat := 2441840307594650947192511

theorem tailTrace_4755467 : CollatzResearch.WordTrace tailWord_4755467 prefixEnd_4755467 2441840307594650947192511 := by
  unfold tailWord_4755467
  simp only [CollatzResearch.WordTrace]
  refine ⟨173446130662762702948624655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115630753775175135299083103 173446130662762702948624655)
  ·
    refine ⟨260169195994144054422936983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173446130662762702948624655 260169195994144054422936983)
    ·
      refine ⟨390253793991216081634405475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260169195994144054422936983 390253793991216081634405475)
      ·
        refine ⟨585380690986824122451608213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390253793991216081634405475 585380690986824122451608213)
        ·
          refine ⟨27439719890007380739919135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 585380690986824122451608213 27439719890007380739919135)
          ·
            refine ⟨41159579835011071109878703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27439719890007380739919135 41159579835011071109878703)
            ·
              refine ⟨61739369752516606664818055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41159579835011071109878703 61739369752516606664818055)
              ·
                refine ⟨92609054628774909997227083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61739369752516606664818055 92609054628774909997227083)
                ·
                  refine ⟨138913581943162364995840625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92609054628774909997227083 138913581943162364995840625)
                  ·
                    refine ⟨104185186457371773746880469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 138913581943162364995840625 104185186457371773746880469)
                    ·
                      refine ⟨2441840307594650947192511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 104185186457371773746880469 2441840307594650947192511)
                      ·
                        rfl

theorem cell23_4755467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 7].length) (baseStart_4755467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4755467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4755467 prefixEnd_4755467 := by exact prefixLift 4755467
  have htrace : WordTrace (prefixWord ++ tailWord_4755467) baseStart_4755467 baseEnd_4755467 := by
    simpa [prefixWord, tailWord_4755467, baseEnd_4755467] using wordTrace_append hprefix tailTrace_4755467
  have hstable : (prefixWord ++ tailWord_4755467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4755467).length < 2 ^ (prefixWord ++ tailWord_4755467).sum := by decide
  have hdescent : baseEnd_4755467 < baseStart_4755467 := by decide
  rcases family_descends (prefixWord ++ tailWord_4755467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4755468 : List Nat := [2, 2, 1, 2, 3, 1, 2, 4, 2, 2, 2]
def baseStart_4755468 : Nat := 118140960795 + 4755468 * 2 ^ 59
def prefixEnd_4755468 : Nat := 4983230072969 + 3 ^ 40 * 4755468 * 2
def baseEnd_4755468 : Nat := 2441840821075305443280007

theorem tailTrace_4755468 : CollatzResearch.WordTrace tailWord_4755468 prefixEnd_4755468 2441840821075305443280007 := by
  unfold tailWord_4755468
  simp only [CollatzResearch.WordTrace]
  refine ⟨86723083567879540059705529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115630778090506053412940705 86723083567879540059705529)
  ·
    refine ⟨65042312675909655044779147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86723083567879540059705529 65042312675909655044779147)
    ·
      refine ⟨97563469013864482567168721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65042312675909655044779147 97563469013864482567168721)
      ·
        refine ⟨73172601760398361925376541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97563469013864482567168721 73172601760398361925376541)
        ·
          refine ⟨27439725660149385722016203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73172601760398361925376541 27439725660149385722016203)
          ·
            refine ⟨41159588490224078583024305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27439725660149385722016203 41159588490224078583024305)
            ·
              refine ⟨30869691367668058937268229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41159588490224078583024305 30869691367668058937268229)
              ·
                refine ⟨5788067131437761050737793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30869691367668058937268229 5788067131437761050737793)
                ·
                  refine ⟨4341050348578320788053345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5788067131437761050737793 4341050348578320788053345)
                  ·
                    refine ⟨3255787761433740591040009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4341050348578320788053345 3255787761433740591040009)
                    ·
                      refine ⟨2441840821075305443280007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3255787761433740591040009 2441840821075305443280007)
                      ·
                        rfl

theorem cell23_4755468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4, 2, 2, 2].length) (baseStart_4755468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4755468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4755468 prefixEnd_4755468 := by exact prefixLift 4755468
  have htrace : WordTrace (prefixWord ++ tailWord_4755468) baseStart_4755468 baseEnd_4755468 := by
    simpa [prefixWord, tailWord_4755468, baseEnd_4755468] using wordTrace_append hprefix tailTrace_4755468
  have hstable : (prefixWord ++ tailWord_4755468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4755468).length < 2 ^ (prefixWord ++ tailWord_4755468).sum := by decide
  have hdescent : baseEnd_4755468 < baseStart_4755468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4755468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
