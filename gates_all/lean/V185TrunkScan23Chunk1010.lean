import V185TrunkScan23Chunk1009

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5979966 : List Nat := [4, 2, 1, 2, 2, 2, 1, 3, 6]
def baseStart_5979966 : Nat := 118140960795 + 5979966 * 2 ^ 59
def prefixEnd_5979966 : Nat := 4983230072969 + 3 ^ 40 * 5979966 * 2
def baseEnd_5979966 : Nat := 341177428393828398802627

theorem tailTrace_5979966 : CollatzResearch.WordTrace tailWord_5979966 prefixEnd_5979966 341177428393828398802627 := by
  unfold tailWord_5979966
  simp only [CollatzResearch.WordTrace]
  refine ⟨27263409781701494216038969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145404852169074635818874501 27263409781701494216038969)
  ·
    refine ⟨20447557336276120662029227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27263409781701494216038969 20447557336276120662029227)
    ·
      refine ⟨30671336004414180993043841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20447557336276120662029227 30671336004414180993043841)
      ·
        refine ⟨23003502003310635744782881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30671336004414180993043841 23003502003310635744782881)
        ·
          refine ⟨17252626502482976808587161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23003502003310635744782881 17252626502482976808587161)
          ·
            refine ⟨12939469876862232606440371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17252626502482976808587161 12939469876862232606440371)
            ·
              refine ⟨19409204815293348909660557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12939469876862232606440371 19409204815293348909660557)
              ·
                refine ⟨7278451805735005841122709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19409204815293348909660557 7278451805735005841122709)
                ·
                  refine ⟨341177428393828398802627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7278451805735005841122709 341177428393828398802627)
                  ·
                    rfl

theorem cell23_5979966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_5979966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979966 prefixEnd_5979966 := by exact prefixLift 5979966
  have htrace : WordTrace (prefixWord ++ tailWord_5979966) baseStart_5979966 baseEnd_5979966 := by
    simpa [prefixWord, tailWord_5979966, baseEnd_5979966] using wordTrace_append hprefix tailTrace_5979966
  have hstable : (prefixWord ++ tailWord_5979966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979966).length < 2 ^ (prefixWord ++ tailWord_5979966).sum := by decide
  have hdescent : baseEnd_5979966 < baseStart_5979966 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979993 : List Nat := [1, 2, 1, 2, 2, 3, 2, 5, 1, 1, 3]
def baseStart_5979993 : Nat := 118140960795 + 5979993 * 2 ^ 59
def prefixEnd_5979993 : Nat := 4983230072969 + 3 ^ 40 * 5979993 * 2
def baseEnd_5979993 : Nat := 3070610719522126983586019

theorem tailTrace_5979993 : CollatzResearch.WordTrace tailWord_5979993 prefixEnd_5979993 3070610719522126983586019 := by
  unfold tailWord_5979993
  simp only [CollatzResearch.WordTrace]
  refine ⟨218108263024514137339544633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145405508683009424893029755 218108263024514137339544633)
  ·
    refine ⟨163581197268385603004658475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218108263024514137339544633 163581197268385603004658475)
    ·
      refine ⟨245371795902578404506987713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163581197268385603004658475 245371795902578404506987713)
      ·
        refine ⟨184028846926933803380240785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245371795902578404506987713 184028846926933803380240785)
        ·
          refine ⟨138021635195200352535180589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184028846926933803380240785 138021635195200352535180589)
          ·
            refine ⟨51758113198200132200692721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138021635195200352535180589 51758113198200132200692721)
            ·
              refine ⟨38818584898650099150519541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51758113198200132200692721 38818584898650099150519541)
              ·
                refine ⟨3639242334248446795361207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38818584898650099150519541 3639242334248446795361207)
                ·
                  refine ⟨5458863501372670193041811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3639242334248446795361207 5458863501372670193041811)
                  ·
                    refine ⟨8188295252059005289562717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5458863501372670193041811 8188295252059005289562717)
                    ·
                      refine ⟨3070610719522126983586019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8188295252059005289562717 3070610719522126983586019)
                      ·
                        rfl

theorem cell23_5979993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 5, 1, 1, 3].length) (baseStart_5979993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979993 prefixEnd_5979993 := by exact prefixLift 5979993
  have htrace : WordTrace (prefixWord ++ tailWord_5979993) baseStart_5979993 baseEnd_5979993 := by
    simpa [prefixWord, tailWord_5979993, baseEnd_5979993] using wordTrace_append hprefix tailTrace_5979993
  have hstable : (prefixWord ++ tailWord_5979993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979993).length < 2 ^ (prefixWord ++ tailWord_5979993).sum := by decide
  have hdescent : baseEnd_5979993 < baseStart_5979993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980009 : List Nat := [1, 2, 1, 1, 1, 3, 1, 5, 4, 4]
def baseStart_5980009 : Nat := 118140960795 + 5980009 * 2 ^ 59
def prefixEnd_5980009 : Nat := 4983230072969 + 3 ^ 40 * 5980009 * 2
def baseEnd_5980009 : Nat := 1023539645070866306995315

theorem tailTrace_5980009 : CollatzResearch.WordTrace tailWord_5980009 prefixEnd_5980009 1023539645070866306995315 := by
  unfold tailWord_5980009
  simp only [CollatzResearch.WordTrace]
  refine ⟨218108846592456172072127081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145405897728304114714751387 218108846592456172072127081)
  ·
    refine ⟨163581634944342129054095311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218108846592456172072127081 163581634944342129054095311)
    ·
      refine ⟨245372452416513193581142967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163581634944342129054095311 245372452416513193581142967)
      ·
        refine ⟨368058678624769790371714451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245372452416513193581142967 368058678624769790371714451)
        ·
          refine ⟨552088017937154685557571677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368058678624769790371714451 552088017937154685557571677)
          ·
            refine ⟨207033006726433007084089379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 552088017937154685557571677 207033006726433007084089379)
            ·
              refine ⟨310549510089649510626134069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207033006726433007084089379 310549510089649510626134069)
              ·
                refine ⟨29114016570904641621200069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 310549510089649510626134069 29114016570904641621200069)
                ·
                  refine ⟨5458878107044620303975013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29114016570904641621200069 5458878107044620303975013)
                  ·
                    refine ⟨1023539645070866306995315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5458878107044620303975013 1023539645070866306995315)
                    ·
                      rfl

theorem cell23_5980009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 4, 4].length) (baseStart_5980009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980009 prefixEnd_5980009 := by exact prefixLift 5980009
  have htrace : WordTrace (prefixWord ++ tailWord_5980009) baseStart_5980009 baseEnd_5980009 := by
    simpa [prefixWord, tailWord_5980009, baseEnd_5980009] using wordTrace_append hprefix tailTrace_5980009
  have hstable : (prefixWord ++ tailWord_5980009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980009).length < 2 ^ (prefixWord ++ tailWord_5980009).sum := by decide
  have hdescent : baseEnd_5980009 < baseStart_5980009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980026 : List Nat := [3, 1, 1, 1, 1, 1, 6, 3, 2, 4]
def baseStart_5980026 : Nat := 118140960795 + 5980026 * 2 ^ 59
def prefixEnd_5980026 : Nat := 4983230072969 + 3 ^ 40 * 5980026 * 2
def baseEnd_5980026 : Nat := 1023542554794575118157789

theorem tailTrace_5980026 : CollatzResearch.WordTrace tailWord_5980026 prefixEnd_5980026 1023542554794575118157789 := by
  unfold tailWord_5980026
  simp only [CollatzResearch.WordTrace]
  refine ⟨54527366658348645993873983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145406311088929722650330621 54527366658348645993873983)
  ·
    refine ⟨81791049987522968990810975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54527366658348645993873983 81791049987522968990810975)
    ·
      refine ⟨122686574981284453486216463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81791049987522968990810975 122686574981284453486216463)
      ·
        refine ⟨184029862471926680229324695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122686574981284453486216463 184029862471926680229324695)
        ·
          refine ⟨276044793707890020343987043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184029862471926680229324695 276044793707890020343987043)
          ·
            refine ⟨414067190561835030515980565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276044793707890020343987043 414067190561835030515980565)
            ·
              refine ⟨19409399557586017055436589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 414067190561835030515980565 19409399557586017055436589)
              ·
                refine ⟨7278524834094756395788721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19409399557586017055436589 7278524834094756395788721)
                ·
                  refine ⟨5458893625571067296841541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7278524834094756395788721 5458893625571067296841541)
                  ·
                    refine ⟨1023542554794575118157789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5458893625571067296841541 1023542554794575118157789)
                    ·
                      rfl

theorem cell23_5980026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3, 2, 4].length) (baseStart_5980026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980026 prefixEnd_5980026 := by exact prefixLift 5980026
  have htrace : WordTrace (prefixWord ++ tailWord_5980026) baseStart_5980026 baseEnd_5980026 := by
    simpa [prefixWord, tailWord_5980026, baseEnd_5980026] using wordTrace_append hprefix tailTrace_5980026
  have hstable : (prefixWord ++ tailWord_5980026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980026).length < 2 ^ (prefixWord ++ tailWord_5980026).sum := by decide
  have hdescent : baseEnd_5980026 < baseStart_5980026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980036 : List Nat := [2, 3, 2, 1, 1, 1, 4, 1, 3, 2, 3]
def baseStart_5980036 : Nat := 118140960795 + 5980036 * 2 ^ 59
def prefixEnd_5980036 : Nat := 4983230072969 + 3 ^ 40 * 5980036 * 2
def baseEnd_5980036 : Nat := 3070632799190270315348321

theorem tailTrace_5980036 : CollatzResearch.WordTrace tailWord_5980036 prefixEnd_5980036 3070632799190270315348321 := by
  unfold tailWord_5980036
  simp only [CollatzResearch.WordTrace]
  refine ⟨109054915681679177841679981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145406554242238903788906641 109054915681679177841679981)
  ·
    refine ⟨40895593380629691690629993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109054915681679177841679981 40895593380629691690629993)
    ·
      refine ⟨30671695035472268767972495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40895593380629691690629993 30671695035472268767972495)
      ·
        refine ⟨46007542553208403151958743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30671695035472268767972495 46007542553208403151958743)
        ·
          refine ⟨69011313829812604727938115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46007542553208403151958743 69011313829812604727938115)
          ·
            refine ⟨103516970744718907091907173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69011313829812604727938115 103516970744718907091907173)
            ·
              refine ⟨19409432014634795079732595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103516970744718907091907173 19409432014634795079732595)
              ·
                refine ⟨29114148021952192619598893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19409432014634795079732595 29114148021952192619598893)
                ·
                  refine ⟨10917805508232072232349585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29114148021952192619598893 10917805508232072232349585)
                  ·
                    refine ⟨8188354131174054174262189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10917805508232072232349585 8188354131174054174262189)
                    ·
                      refine ⟨3070632799190270315348321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8188354131174054174262189 3070632799190270315348321)
                      ·
                        rfl

theorem cell23_5980036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_5980036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980036 prefixEnd_5980036 := by exact prefixLift 5980036
  have htrace : WordTrace (prefixWord ++ tailWord_5980036) baseStart_5980036 baseEnd_5980036 := by
    simpa [prefixWord, tailWord_5980036, baseEnd_5980036] using wordTrace_append hprefix tailTrace_5980036
  have hstable : (prefixWord ++ tailWord_5980036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980036).length < 2 ^ (prefixWord ++ tailWord_5980036).sum := by decide
  have hdescent : baseEnd_5980036 < baseStart_5980036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980050 : List Nat := [3, 2, 3, 2, 1, 1, 4, 1, 1, 1, 4]
def baseStart_5980050 : Nat := 118140960795 + 5980050 * 2 ^ 59
def prefixEnd_5980050 : Nat := 4983230072969 + 3 ^ 40 * 5980050 * 2
def baseEnd_5980050 : Nat := 3070639987919433260573257

theorem tailTrace_5980050 : CollatzResearch.WordTrace tailWord_5980050 prefixEnd_5980050 3070639987919433260573257 := by
  unfold tailWord_5980050
  simp only [CollatzResearch.WordTrace]
  refine ⟨54527585496326909018592401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145406894656871757382913069 54527585496326909018592401)
  ·
    refine ⟨40895689122245181763944301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54527585496326909018592401 40895689122245181763944301)
    ·
      refine ⟨15335883420841943161479113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40895689122245181763944301 15335883420841943161479113)
      ·
        refine ⟨11501912565631457371109335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15335883420841943161479113 11501912565631457371109335)
        ·
          refine ⟨17252868848447186056664003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11501912565631457371109335 17252868848447186056664003)
          ·
            refine ⟨25879303272670779084996005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17252868848447186056664003 25879303272670779084996005)
            ·
              refine ⟨4852369363625771078436751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25879303272670779084996005 4852369363625771078436751)
              ·
                refine ⟨7278554045438656617655127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4852369363625771078436751 7278554045438656617655127)
                ·
                  refine ⟨10917831068157984926482691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7278554045438656617655127 10917831068157984926482691)
                  ·
                    refine ⟨16376746602236977389724037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10917831068157984926482691 16376746602236977389724037)
                    ·
                      refine ⟨3070639987919433260573257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16376746602236977389724037 3070639987919433260573257)
                      ·
                        rfl

theorem cell23_5980050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_5980050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980050 prefixEnd_5980050 := by exact prefixLift 5980050
  have htrace : WordTrace (prefixWord ++ tailWord_5980050) baseStart_5980050 baseEnd_5980050 := by
    simpa [prefixWord, tailWord_5980050, baseEnd_5980050] using wordTrace_append hprefix tailTrace_5980050
  have hstable : (prefixWord ++ tailWord_5980050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980050).length < 2 ^ (prefixWord ++ tailWord_5980050).sum := by decide
  have hdescent : baseEnd_5980050 < baseStart_5980050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980056 : List Nat := [2, 1, 2, 6, 1, 1, 10]
def baseStart_5980056 : Nat := 118140960795 + 5980056 * 2 ^ 59
def prefixEnd_5980056 : Nat := 4983230072969 + 3 ^ 40 * 5980056 * 2
def baseEnd_5980056 : Nat := 37909173688930373297509

theorem tailTrace_5980056 : CollatzResearch.WordTrace tailWord_5980056 prefixEnd_5980056 37909173688930373297509 := by
  unfold tailWord_5980056
  simp only [CollatzResearch.WordTrace]
  refine ⟨109055280411642949549544011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145407040548857266066058681 109055280411642949549544011)
  ·
    refine ⟨163582920617464424324316017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109055280411642949549544011 163582920617464424324316017)
    ·
      refine ⟨122687190463098318243237013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163582920617464424324316017 122687190463098318243237013)
      ·
        refine ⟨5750962052957733667651735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 122687190463098318243237013 5750962052957733667651735)
        ·
          refine ⟨8626443079436600501477603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5750962052957733667651735 8626443079436600501477603)
          ·
            refine ⟨12939664619154900752216405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8626443079436600501477603 12939664619154900752216405)
            ·
              refine ⟨37909173688930373297509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12939664619154900752216405 37909173688930373297509)
              ·
                rfl

theorem cell23_5980056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 10].length) (baseStart_5980056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980056 prefixEnd_5980056 := by exact prefixLift 5980056
  have htrace : WordTrace (prefixWord ++ tailWord_5980056) baseStart_5980056 baseEnd_5980056 := by
    simpa [prefixWord, tailWord_5980056, baseEnd_5980056] using wordTrace_append hprefix tailTrace_5980056
  have hstable : (prefixWord ++ tailWord_5980056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980056).length < 2 ^ (prefixWord ++ tailWord_5980056).sum := by decide
  have hdescent : baseEnd_5980056 < baseStart_5980056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980060 : List Nat := [2, 2, 3, 3, 1, 3, 1, 2, 2, 4]
def baseStart_5980060 : Nat := 118140960795 + 5980060 * 2 ^ 59
def prefixEnd_5980060 : Nat := 4983230072969 + 3 ^ 40 * 5980060 * 2
def baseEnd_5980060 : Nat := 1023548374241992740482737

theorem tailTrace_5980060 : CollatzResearch.WordTrace tailWord_5980060 prefixEnd_5980060 1023548374241992740482737 := by
  unfold tailWord_5980060
  simp only [CollatzResearch.WordTrace]
  refine ⟨109055353357635703891116817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145407137810180938521489089 109055353357635703891116817)
  ·
    refine ⟨81791515018226777918337613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109055353357635703891116817 81791515018226777918337613)
    ·
      refine ⟨30671818131835041719376605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81791515018226777918337613 30671818131835041719376605)
      ·
        refine ⟨11501931799438140644766227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30671818131835041719376605 11501931799438140644766227)
        ·
          refine ⟨17252897699157210967149341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11501931799438140644766227 17252897699157210967149341)
          ·
            refine ⟨6469836637183954112681003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17252897699157210967149341 6469836637183954112681003)
            ·
              refine ⟨9704754955775931169021505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6469836637183954112681003 9704754955775931169021505)
              ·
                refine ⟨7278566216831948376766129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9704754955775931169021505 7278566216831948376766129)
                ·
                  refine ⟨5458924662623961282574597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7278566216831948376766129 5458924662623961282574597)
                  ·
                    refine ⟨1023548374241992740482737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5458924662623961282574597 1023548374241992740482737)
                    ·
                      rfl

theorem cell23_5980060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_5980060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980060 prefixEnd_5980060 := by exact prefixLift 5980060
  have htrace : WordTrace (prefixWord ++ tailWord_5980060) baseStart_5980060 baseEnd_5980060 := by
    simpa [prefixWord, tailWord_5980060, baseEnd_5980060] using wordTrace_append hprefix tailTrace_5980060
  have hstable : (prefixWord ++ tailWord_5980060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980060).length < 2 ^ (prefixWord ++ tailWord_5980060).sum := by decide
  have hdescent : baseEnd_5980060 < baseStart_5980060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980159 : List Nat := [1, 1, 2, 2, 1, 2, 1, 5, 1, 7]
def baseStart_5980159 : Nat := 118140960795 + 5980159 * 2 ^ 59
def prefixEnd_5980159 : Nat := 4983230072969 + 3 ^ 40 * 5980159 * 2
def baseEnd_5980159 : Nat := 1023565319103591111370085

theorem tailTrace_5980159 : CollatzResearch.WordTrace tailWord_5980159 prefixEnd_5980159 1023565319103591111370085 := by
  unfold tailWord_5980159
  simp only [CollatzResearch.WordTrace]
  refine ⟨218114317541912747690087531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145409545027941831793391687 218114317541912747690087531)
  ·
    refine ⟨327171476312869121535131297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218114317541912747690087531 327171476312869121535131297)
    ·
      refine ⟨245378607234651841151348473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327171476312869121535131297 245378607234651841151348473)
      ·
        refine ⟨184033955425988880863511355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245378607234651841151348473 184033955425988880863511355)
        ·
          refine ⟨276050933138983321295267033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184033955425988880863511355 276050933138983321295267033)
          ·
            refine ⟨207038199854237490971450275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276050933138983321295267033 207038199854237490971450275)
            ·
              refine ⟨310557299781356236457175413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207038199854237490971450275 310557299781356236457175413)
              ·
                refine ⟨29114746854502147167860195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 310557299781356236457175413 29114746854502147167860195)
                ·
                  refine ⟨43672120281753220751790293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29114746854502147167860195 43672120281753220751790293)
                  ·
                    refine ⟨1023565319103591111370085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43672120281753220751790293 1023565319103591111370085)
                    ·
                      rfl

theorem cell23_5980159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 7].length) (baseStart_5980159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980159 prefixEnd_5980159 := by exact prefixLift 5980159
  have htrace : WordTrace (prefixWord ++ tailWord_5980159) baseStart_5980159 baseEnd_5980159 := by
    simpa [prefixWord, tailWord_5980159, baseEnd_5980159] using wordTrace_append hprefix tailTrace_5980159
  have hstable : (prefixWord ++ tailWord_5980159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980159).length < 2 ^ (prefixWord ++ tailWord_5980159).sum := by decide
  have hdescent : baseEnd_5980159 < baseStart_5980159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980186 : List Nat := [3, 1, 1, 3, 1, 3, 2, 1, 1, 2, 5]
def baseStart_5980186 : Nat := 118140960795 + 5980186 * 2 ^ 59
def prefixEnd_5980186 : Nat := 4983230072969 + 3 ^ 40 * 5980186 * 2
def baseEnd_5980186 : Nat := 3070709821288444728472631

theorem tailTrace_5980186 : CollatzResearch.WordTrace tailWord_5980186 prefixEnd_5980186 3070709821288444728472631 := by
  unfold tailWord_5980186
  simp only [CollatzResearch.WordTrace]
  refine ⟨54528825578203732825330103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145410201541876620867546941 54528825578203732825330103)
  ·
    refine ⟨81793238367305599237995155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54528825578203732825330103 81793238367305599237995155)
    ·
      refine ⟨122689857550958398856992733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81793238367305599237995155 122689857550958398856992733)
      ·
        refine ⟨46008696581609399571372275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122689857550958398856992733 46008696581609399571372275)
        ·
          refine ⟨69013044872414099357058413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46008696581609399571372275 69013044872414099357058413)
          ·
            refine ⟨25879891827155287258896905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69013044872414099357058413 25879891827155287258896905)
            ·
              refine ⟨19409918870366465444172679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25879891827155287258896905 19409918870366465444172679)
              ·
                refine ⟨29114878305549698166259019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19409918870366465444172679 29114878305549698166259019)
                ·
                  refine ⟨43672317458324547249388529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29114878305549698166259019 43672317458324547249388529)
                  ·
                    refine ⟨32754238093743410437041397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43672317458324547249388529 32754238093743410437041397)
                    ·
                      refine ⟨3070709821288444728472631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32754238093743410437041397 3070709821288444728472631)
                      ·
                        rfl

theorem cell23_5980186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_5980186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980186 prefixEnd_5980186 := by exact prefixLift 5980186
  have htrace : WordTrace (prefixWord ++ tailWord_5980186) baseStart_5980186 baseEnd_5980186 := by
    simpa [prefixWord, tailWord_5980186, baseEnd_5980186] using wordTrace_append hprefix tailTrace_5980186
  have hstable : (prefixWord ++ tailWord_5980186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980186).length < 2 ^ (prefixWord ++ tailWord_5980186).sum := by decide
  have hdescent : baseEnd_5980186 < baseStart_5980186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980213 : List Nat := [1, 3, 3, 1, 1, 1, 5, 1, 2, 1, 4]
def baseStart_5980213 : Nat := 118140960795 + 5980213 * 2 ^ 59
def prefixEnd_5980213 : Nat := 4983230072969 + 3 ^ 40 * 5980213 * 2
def baseEnd_5980213 : Nat := 3070723685266116122835007

theorem tailTrace_5980213 : CollatzResearch.WordTrace tailWord_5980213 prefixEnd_5980213 3070723685266116122835007 := by
  unfold tailWord_5980213
  simp only [CollatzResearch.WordTrace]
  refine ⟨218116287083717114912553293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145410858055811409941702195 218116287083717114912553293)
  ·
    refine ⟨81793607656393918092207485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218116287083717114912553293 81793607656393918092207485)
    ·
      refine ⟨30672602871147719284577807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81793607656393918092207485 30672602871147719284577807)
      ·
        refine ⟨46008904306721578926866711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30672602871147719284577807 46008904306721578926866711)
        ·
          refine ⟨69013356460082368390300067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46008904306721578926866711 69013356460082368390300067)
          ·
            refine ⟨103520034690123552585450101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69013356460082368390300067 103520034690123552585450101)
            ·
              refine ⟨9705003252199083054885947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103520034690123552585450101 9705003252199083054885947)
              ·
                refine ⟨14557504878298624582328921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9705003252199083054885947 14557504878298624582328921)
                ·
                  refine ⟨10918128658723968436746691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14557504878298624582328921 10918128658723968436746691)
                  ·
                    refine ⟨16377192988085952655120037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10918128658723968436746691 16377192988085952655120037)
                    ·
                      refine ⟨3070723685266116122835007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16377192988085952655120037 3070723685266116122835007)
                      ·
                        rfl

theorem cell23_5980213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_5980213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980213 prefixEnd_5980213 := by exact prefixLift 5980213
  have htrace : WordTrace (prefixWord ++ tailWord_5980213) baseStart_5980213 baseEnd_5980213 := by
    simpa [prefixWord, tailWord_5980213, baseEnd_5980213] using wordTrace_append hprefix tailTrace_5980213
  have hstable : (prefixWord ++ tailWord_5980213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980213).length < 2 ^ (prefixWord ++ tailWord_5980213).sum := by decide
  have hdescent : baseEnd_5980213 < baseStart_5980213 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980219 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 10]
def baseStart_5980219 : Nat := 118140960795 + 5980219 * 2 ^ 59
def prefixEnd_5980219 : Nat := 4983230072969 + 3 ^ 40 * 5980219 * 2
def baseEnd_5980219 : Nat := 341191862905560344373331

theorem tailTrace_5980219 : CollatzResearch.WordTrace tailWord_5980219 prefixEnd_5980219 341191862905560344373331 := by
  unfold tailWord_5980219
  simp only [CollatzResearch.WordTrace]
  refine ⟨218116505921695377937271711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145411003947796918624847807 218116505921695377937271711)
  ·
    refine ⟨327174758882543066905907567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218116505921695377937271711 327174758882543066905907567)
    ·
      refine ⟨490762138323814600358861351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327174758882543066905907567 490762138323814600358861351)
      ·
        refine ⟨736143207485721900538292027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490762138323814600358861351 736143207485721900538292027)
        ·
          refine ⟨1104214811228582850807438041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 736143207485721900538292027 1104214811228582850807438041)
          ·
            refine ⟨828161108421437138105578531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1104214811228582850807438041 828161108421437138105578531)
            ·
              refine ⟨1242241662632155707158367797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 828161108421437138105578531 1242241662632155707158367797)
              ·
                refine ⟨116460155871764597546096981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1242241662632155707158367797 116460155871764597546096981)
                ·
                  refine ⟨341191862905560344373331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 116460155871764597546096981 341191862905560344373331)
                  ·
                    rfl

theorem cell23_5980219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 10].length) (baseStart_5980219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980219 prefixEnd_5980219 := by exact prefixLift 5980219
  have htrace : WordTrace (prefixWord ++ tailWord_5980219) baseStart_5980219 baseEnd_5980219 := by
    simpa [prefixWord, tailWord_5980219, baseEnd_5980219] using wordTrace_append hprefix tailTrace_5980219
  have hstable : (prefixWord ++ tailWord_5980219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980219).length < 2 ^ (prefixWord ++ tailWord_5980219).sum := by decide
  have hdescent : baseEnd_5980219 < baseStart_5980219 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980230 : List Nat := [6, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4]
def baseStart_5980230 : Nat := 118140960795 + 5980230 * 2 ^ 59
def prefixEnd_5980230 : Nat := 4983230072969 + 3 ^ 40 * 5980230 * 2
def baseEnd_5980230 : Nat := 3070732414437242556322429

theorem tailTrace_5980230 : CollatzResearch.WordTrace tailWord_5980230 prefixEnd_5980230 3070732414437242556322429 := by
  unfold tailWord_5980230
  simp only [CollatzResearch.WordTrace]
  refine ⟨6816153347645485212997567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 145411271416437017877281429 6816153347645485212997567)
  ·
    refine ⟨10224230021468227819496351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6816153347645485212997567 10224230021468227819496351)
    ·
      refine ⟨15336345032202341729244527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10224230021468227819496351 15336345032202341729244527)
      ·
        refine ⟨23004517548303512593866791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15336345032202341729244527 23004517548303512593866791)
        ·
          refine ⟨34506776322455268890800187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23004517548303512593866791 34506776322455268890800187)
          ·
            refine ⟨51760164483682903336200281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34506776322455268890800187 51760164483682903336200281)
            ·
              refine ⟨38820123362762177502150211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51760164483682903336200281 38820123362762177502150211)
              ·
                refine ⟨58230185044143266253225317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38820123362762177502150211 58230185044143266253225317)
                ·
                  refine ⟨10918159695776862422479747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58230185044143266253225317 10918159695776862422479747)
                  ·
                    refine ⟨16377239543665293633719621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10918159695776862422479747 16377239543665293633719621)
                    ·
                      refine ⟨3070732414437242556322429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16377239543665293633719621 3070732414437242556322429)
                      ·
                        rfl

theorem cell23_5980230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_5980230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980230 prefixEnd_5980230 := by exact prefixLift 5980230
  have htrace : WordTrace (prefixWord ++ tailWord_5980230) baseStart_5980230 baseEnd_5980230 := by
    simpa [prefixWord, tailWord_5980230, baseEnd_5980230] using wordTrace_append hprefix tailTrace_5980230
  have hstable : (prefixWord ++ tailWord_5980230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980230).length < 2 ^ (prefixWord ++ tailWord_5980230).sum := by decide
  have hdescent : baseEnd_5980230 < baseStart_5980230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980273 : List Nat := [1, 2, 2, 2, 1, 1, 3, 3, 1, 5, 2]
def baseStart_5980273 : Nat := 118140960795 + 5980273 * 2 ^ 59
def prefixEnd_5980273 : Nat := 4983230072969 + 3 ^ 40 * 5980273 * 2
def baseEnd_5980273 : Nat := 3070754494105385888084731

theorem tailTrace_5980273 : CollatzResearch.WordTrace tailWord_5980273 prefixEnd_5980273 3070754494105385888084731 := by
  unfold tailWord_5980273
  simp only [CollatzResearch.WordTrace]
  refine ⟨218118475463499745159737473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145412316975666496773158315 218118475463499745159737473)
  ·
    refine ⟨163588856597624808869803105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218118475463499745159737473 163588856597624808869803105)
    ·
      refine ⟨122691642448218606652352329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163588856597624808869803105 122691642448218606652352329)
      ·
        refine ⟨92018731836163954989264247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122691642448218606652352329 92018731836163954989264247)
        ·
          refine ⟨138028097754245932483896371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92018731836163954989264247 138028097754245932483896371)
          ·
            refine ⟨207042146631368898725844557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138028097754245932483896371 207042146631368898725844557)
            ·
              refine ⟨77640804986763337022191709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 207042146631368898725844557 77640804986763337022191709)
              ·
                refine ⟨29115301870036251383321891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77640804986763337022191709 29115301870036251383321891)
                ·
                  refine ⟨43672952805054377074982837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29115301870036251383321891 43672952805054377074982837)
                  ·
                    refine ⟨4094339325473847850779641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43672952805054377074982837 4094339325473847850779641)
                    ·
                      refine ⟨3070754494105385888084731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4094339325473847850779641 3070754494105385888084731)
                      ·
                        rfl

theorem cell23_5980273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 5, 2].length) (baseStart_5980273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980273 prefixEnd_5980273 := by exact prefixLift 5980273
  have htrace : WordTrace (prefixWord ++ tailWord_5980273) baseStart_5980273 baseEnd_5980273 := by
    simpa [prefixWord, tailWord_5980273, baseEnd_5980273] using wordTrace_append hprefix tailTrace_5980273
  have hstable : (prefixWord ++ tailWord_5980273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980273).length < 2 ^ (prefixWord ++ tailWord_5980273).sum := by decide
  have hdescent : baseEnd_5980273 < baseStart_5980273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980320 : List Nat := [2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 4]
def baseStart_5980320 : Nat := 118140960795 + 5980320 * 2 ^ 59
def prefixEnd_5980320 : Nat := 4983230072969 + 3 ^ 40 * 5980320 * 2
def baseEnd_5980320 : Nat := 3070778627696147204197015

theorem tailTrace_5980320 : CollatzResearch.WordTrace tailWord_5980320 prefixEnd_5980320 3070778627696147204197015 := by
  unfold tailWord_5980320
  simp only [CollatzResearch.WordTrace]
  refine ⟨109060094847164736093349207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145413459796219648124465609 109060094847164736093349207)
  ·
    refine ⟨163590142270747104140023811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109060094847164736093349207 163590142270747104140023811)
    ·
      refine ⟨245385213406120656210035717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163590142270747104140023811 245385213406120656210035717)
      ·
        refine ⟨46009727513647623039381697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 245385213406120656210035717 46009727513647623039381697)
        ·
          refine ⟨34507295635235717279536273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46009727513647623039381697 34507295635235717279536273)
          ·
            refine ⟨25880471726426787959652205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34507295635235717279536273 25880471726426787959652205)
            ·
              refine ⟨9705176897410045484869577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25880471726426787959652205 9705176897410045484869577)
              ·
                refine ⟨7278882673057534113652183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9705176897410045484869577 7278882673057534113652183)
                ·
                  refine ⟨10918324009586301170478275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7278882673057534113652183 10918324009586301170478275)
                  ·
                    refine ⟨16377486014379451755717413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10918324009586301170478275 16377486014379451755717413)
                    ·
                      refine ⟨3070778627696147204197015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16377486014379451755717413 3070778627696147204197015)
                      ·
                        rfl

theorem cell23_5980320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_5980320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980320 prefixEnd_5980320 := by exact prefixLift 5980320
  have htrace : WordTrace (prefixWord ++ tailWord_5980320) baseStart_5980320 baseEnd_5980320 := by
    simpa [prefixWord, tailWord_5980320, baseEnd_5980320] using wordTrace_append hprefix tailTrace_5980320
  have hstable : (prefixWord ++ tailWord_5980320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980320).length < 2 ^ (prefixWord ++ tailWord_5980320).sum := by decide
  have hdescent : baseEnd_5980320 < baseStart_5980320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980348 : List Nat := [2, 2, 2, 3, 4, 1, 2, 2, 1, 1, 3]
def baseStart_5980348 : Nat := 118140960795 + 5980348 * 2 ^ 59
def prefixEnd_5980348 : Nat := 4983230072969 + 3 ^ 40 * 5980348 * 2
def baseEnd_5980348 : Nat := 3070793005154473094646887

theorem tailTrace_5980348 : CollatzResearch.WordTrace tailWord_5980348 prefixEnd_5980348 3070793005154473094646887 := by
  unfold tailWord_5980348
  simp only [CollatzResearch.WordTrace]
  refine ⟨109060605469114016484358849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145414140625485355312478465 109060605469114016484358849)
  ·
    refine ⟨81795454101835512363269137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109060605469114016484358849 81795454101835512363269137)
    ·
      refine ⟨61346590576376634272451853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81795454101835512363269137 61346590576376634272451853)
      ·
        refine ⟨23004971466141237852169445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61346590576376634272451853 23004971466141237852169445)
        ·
          refine ⟨4313432149901482097281771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23004971466141237852169445 4313432149901482097281771)
          ·
            refine ⟨6470148224852223145922657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4313432149901482097281771 6470148224852223145922657)
            ·
              refine ⟨4852611168639167359441993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6470148224852223145922657 4852611168639167359441993)
              ·
                refine ⟨3639458376479375519581495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4852611168639167359441993 3639458376479375519581495)
                ·
                  refine ⟨5459187564719063279372243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3639458376479375519581495 5459187564719063279372243)
                  ·
                    refine ⟨8188781347078594919058365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5459187564719063279372243 8188781347078594919058365)
                    ·
                      refine ⟨3070793005154473094646887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8188781347078594919058365 3070793005154473094646887)
                      ·
                        rfl

theorem cell23_5980348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_5980348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980348 prefixEnd_5980348 := by exact prefixLift 5980348
  have htrace : WordTrace (prefixWord ++ tailWord_5980348) baseStart_5980348 baseEnd_5980348 := by
    simpa [prefixWord, tailWord_5980348, baseEnd_5980348] using wordTrace_append hprefix tailTrace_5980348
  have hstable : (prefixWord ++ tailWord_5980348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980348).length < 2 ^ (prefixWord ++ tailWord_5980348).sum := by decide
  have hdescent : baseEnd_5980348 < baseStart_5980348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980370 : List Nat := [3, 2, 2, 2, 1, 2, 1, 3, 1, 3, 3]
def baseStart_5980370 : Nat := 118140960795 + 5980370 * 2 ^ 59
def prefixEnd_5980370 : Nat := 4983230072969 + 3 ^ 40 * 5980370 * 2
def baseEnd_5980370 : Nat := 3070804301728872008571785

theorem tailTrace_5980370 : CollatzResearch.WordTrace tailWord_5980370 prefixEnd_5980370 3070804301728872008571785 := by
  unfold tailWord_5980370
  simp only [CollatzResearch.WordTrace]
  refine ⟨54530503336037082681504641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145414675562765553817345709 54530503336037082681504641)
  ·
    refine ⟨40897877502027812011128481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54530503336037082681504641 40897877502027812011128481)
    ·
      refine ⟨30673408126520859008346361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40897877502027812011128481 30673408126520859008346361)
      ·
        refine ⟨23005056094890644256259771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30673408126520859008346361 23005056094890644256259771)
        ·
          refine ⟨34507584142335966384389657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23005056094890644256259771 34507584142335966384389657)
          ·
            refine ⟨25880688106751974788292243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34507584142335966384389657 25880688106751974788292243)
            ·
              refine ⟨38821032160127962182438365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25880688106751974788292243 38821032160127962182438365)
              ·
                refine ⟨14557887060047985818414387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38821032160127962182438365 14557887060047985818414387)
                ·
                  refine ⟨21836830590071978727621581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14557887060047985818414387 21836830590071978727621581)
                  ·
                    refine ⟨8188811471276992022858093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21836830590071978727621581 8188811471276992022858093)
                    ·
                      refine ⟨3070804301728872008571785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8188811471276992022858093 3070804301728872008571785)
                      ·
                        rfl

theorem cell23_5980370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_5980370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980370 prefixEnd_5980370 := by exact prefixLift 5980370
  have htrace : WordTrace (prefixWord ++ tailWord_5980370) baseStart_5980370 baseEnd_5980370 := by
    simpa [prefixWord, tailWord_5980370, baseEnd_5980370] using wordTrace_append hprefix tailTrace_5980370
  have hstable : (prefixWord ++ tailWord_5980370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980370).length < 2 ^ (prefixWord ++ tailWord_5980370).sum := by decide
  have hdescent : baseEnd_5980370 < baseStart_5980370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980413 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 1, 6, 3]
def baseStart_5980413 : Nat := 118140960795 + 5980413 * 2 ^ 59
def prefixEnd_5980413 : Nat := 4983230072969 + 3 ^ 40 * 5980413 * 2
def baseEnd_5980413 : Nat := 3070826381397015340334087

theorem tailTrace_5980413 : CollatzResearch.WordTrace tailWord_5980413 prefixEnd_5980413 3070826381397015340334087 := by
  unfold tailWord_5980413
  simp only [CollatzResearch.WordTrace]
  refine ⟨218123581682992549069833893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145415721121995032713222595 218123581682992549069833893)
  ·
    refine ⟨40898171565561102950593855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 218123581682992549069833893 40898171565561102950593855)
    ·
      refine ⟨61347257348341654425890783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40898171565561102950593855 61347257348341654425890783)
      ·
        refine ⟨92020886022512481638836175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61347257348341654425890783 92020886022512481638836175)
        ·
          refine ⟨138031329033768722458254263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92020886022512481638836175 138031329033768722458254263)
          ·
            refine ⟨207046993550653083687381395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138031329033768722458254263 207046993550653083687381395)
            ·
              refine ⟨310570490325979625531072093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207046993550653083687381395 310570490325979625531072093)
              ·
                refine ⟨116463933872242359574152035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 310570490325979625531072093 116463933872242359574152035)
                ·
                  refine ⟨174695900808363539361228053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116463933872242359574152035 174695900808363539361228053)
                  ·
                    refine ⟨8188870350392040907557565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 174695900808363539361228053 8188870350392040907557565)
                    ·
                      refine ⟨3070826381397015340334087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8188870350392040907557565 3070826381397015340334087)
                      ·
                        rfl

theorem cell23_5980413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 6, 3].length) (baseStart_5980413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980413 prefixEnd_5980413 := by exact prefixLift 5980413
  have htrace : WordTrace (prefixWord ++ tailWord_5980413) baseStart_5980413 baseEnd_5980413 := by
    simpa [prefixWord, tailWord_5980413, baseEnd_5980413] using wordTrace_append hprefix tailTrace_5980413
  have hstable : (prefixWord ++ tailWord_5980413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980413).length < 2 ^ (prefixWord ++ tailWord_5980413).sum := by decide
  have hdescent : baseEnd_5980413 < baseStart_5980413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980433 : List Nat := [1, 2, 2, 1, 1, 5, 2, 2, 7]
def baseStart_5980433 : Nat := 118140960795 + 5980433 * 2 ^ 59
def prefixEnd_5980433 : Nat := 4983230072969 + 3 ^ 40 * 5980433 * 2
def baseEnd_5980433 : Nat := 341204072334456140231555

theorem tailTrace_5980433 : CollatzResearch.WordTrace tailWord_5980433 prefixEnd_5980433 341204072334456140231555 := by
  unfold tailWord_5980433
  simp only [CollatzResearch.WordTrace]
  refine ⟨218124311142920092485561953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145416207428613394990374635 218124311142920092485561953)
  ·
    refine ⟨163593233357190069364171465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218124311142920092485561953 163593233357190069364171465)
    ·
      refine ⟨122694925017892552023128599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163593233357190069364171465 122694925017892552023128599)
      ·
        refine ⟨184042387526838828034692899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122694925017892552023128599 184042387526838828034692899)
        ·
          refine ⟨276063581290258242052039349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184042387526838828034692899 276063581290258242052039349)
          ·
            refine ⟨25880960745961710192378689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 276063581290258242052039349 25880960745961710192378689)
            ·
              refine ⟨19410720559471282644284017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25880960745961710192378689 19410720559471282644284017)
              ·
                refine ⟨14558040419603461983213013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19410720559471282644284017 14558040419603461983213013)
                ·
                  refine ⟨341204072334456140231555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14558040419603461983213013 341204072334456140231555)
                  ·
                    rfl

theorem cell23_5980433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 7].length) (baseStart_5980433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980433 prefixEnd_5980433 := by exact prefixLift 5980433
  have htrace : WordTrace (prefixWord ++ tailWord_5980433) baseStart_5980433 baseEnd_5980433 := by
    simpa [prefixWord, tailWord_5980433, baseEnd_5980433] using wordTrace_append hprefix tailTrace_5980433
  have hstable : (prefixWord ++ tailWord_5980433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980433).length < 2 ^ (prefixWord ++ tailWord_5980433).sum := by decide
  have hdescent : baseEnd_5980433 < baseStart_5980433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980443 : List Nat := [1, 1, 1, 1, 1, 1, 6, 2, 1, 5, 3]
def baseStart_5980443 : Nat := 118140960795 + 5980443 * 2 ^ 59
def prefixEnd_5980443 : Nat := 4983230072969 + 3 ^ 40 * 5980443 * 2
def baseEnd_5980443 : Nat := 3070841785816650222958949

theorem tailTrace_5980443 : CollatzResearch.WordTrace tailWord_5980443 prefixEnd_5980443 3070841785816650222958949 := by
  unfold tailWord_5980443
  simp only [CollatzResearch.WordTrace]
  refine ⟨218124675872883864193425983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145416450581922576128950655 218124675872883864193425983)
  ·
    refine ⟨327187013809325796290138975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218124675872883864193425983 327187013809325796290138975)
    ·
      refine ⟨490780520713988694435208463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327187013809325796290138975 490780520713988694435208463)
      ·
        refine ⟨736170781070983041652812695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490780520713988694435208463 736170781070983041652812695)
        ·
          refine ⟨1104256171606474562479219043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 736170781070983041652812695 1104256171606474562479219043)
          ·
            refine ⟨1656384257409711843718828565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1104256171606474562479219043 1656384257409711843718828565)
            ·
              refine ⟨77643012066080242674320089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1656384257409711843718828565 77643012066080242674320089)
              ·
                refine ⟨58232259049560182005740067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77643012066080242674320089 58232259049560182005740067)
                ·
                  refine ⟨87348388574340273008610101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58232259049560182005740067 87348388574340273008610101)
                  ·
                    refine ⟨8188911428844400594557197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 87348388574340273008610101 8188911428844400594557197)
                    ·
                      refine ⟨3070841785816650222958949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8188911428844400594557197 3070841785816650222958949)
                      ·
                        rfl

theorem cell23_5980443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 5, 3].length) (baseStart_5980443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980443 prefixEnd_5980443 := by exact prefixLift 5980443
  have htrace : WordTrace (prefixWord ++ tailWord_5980443) baseStart_5980443 baseEnd_5980443 := by
    simpa [prefixWord, tailWord_5980443, baseEnd_5980443] using wordTrace_append hprefix tailTrace_5980443
  have hstable : (prefixWord ++ tailWord_5980443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980443).length < 2 ^ (prefixWord ++ tailWord_5980443).sum := by decide
  have hdescent : baseEnd_5980443 < baseStart_5980443 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980463 : List Nat := [1, 1, 2, 1, 2, 1, 5, 1, 4, 5]
def baseStart_5980463 : Nat := 118140960795 + 5980463 * 2 ^ 59
def prefixEnd_5980463 : Nat := 4983230072969 + 3 ^ 40 * 5980463 * 2
def baseEnd_5980463 : Nat := 1023617351809913381569619

theorem tailTrace_5980463 : CollatzResearch.WordTrace tailWord_5980463 prefixEnd_5980463 1023617351809913381569619 := by
  unfold tailWord_5980463
  simp only [CollatzResearch.WordTrace]
  refine ⟨218125405332811407609154043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145416936888540938406102695 218125405332811407609154043)
  ·
    refine ⟨327188107999217111413731065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218125405332811407609154043 327188107999217111413731065)
    ·
      refine ⟨245391080999412833560298299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327188107999217111413731065 245391080999412833560298299)
      ·
        refine ⟨368086621499119250340447449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245391080999412833560298299 368086621499119250340447449)
        ·
          refine ⟨276064966124339437755335587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368086621499119250340447449 276064966124339437755335587)
          ·
            refine ⟨414097449186509156633003381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276064966124339437755335587 414097449186509156633003381)
            ·
              refine ⟨38821635861235233434344067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 414097449186509156633003381 38821635861235233434344067)
              ·
                refine ⟨58232453791852850151516101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38821635861235233434344067 58232453791852850151516101)
                ·
                  refine ⟨10918585085972409403409269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58232453791852850151516101 10918585085972409403409269)
                  ·
                    refine ⟨1023617351809913381569619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10918585085972409403409269 1023617351809913381569619)
                    ·
                      rfl

theorem cell23_5980463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4, 5].length) (baseStart_5980463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980463 prefixEnd_5980463 := by exact prefixLift 5980463
  have htrace : WordTrace (prefixWord ++ tailWord_5980463) baseStart_5980463 baseEnd_5980463 := by
    simpa [prefixWord, tailWord_5980463, baseEnd_5980463] using wordTrace_append hprefix tailTrace_5980463
  have hstable : (prefixWord ++ tailWord_5980463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980463).length < 2 ^ (prefixWord ++ tailWord_5980463).sum := by decide
  have hdescent : baseEnd_5980463 < baseStart_5980463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980467 : List Nat := [1, 1, 1, 2, 5, 1, 5, 2, 5]
def baseStart_5980467 : Nat := 118140960795 + 5980467 * 2 ^ 59
def prefixEnd_5980467 : Nat := 4983230072969 + 3 ^ 40 * 5980467 * 2
def baseEnd_5980467 : Nat := 341206012150262014339871

theorem tailTrace_5980467 : CollatzResearch.WordTrace tailWord_5980467 prefixEnd_5980467 341206012150262014339871 := by
  unfold tailWord_5980467
  simp only [CollatzResearch.WordTrace]
  refine ⟨218125551224796916292299655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145417034149864610861533103 218125551224796916292299655)
  ·
    refine ⟨327188326837195374438449483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218125551224796916292299655 327188326837195374438449483)
    ·
      refine ⟨490782490255793061657674225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327188326837195374438449483 490782490255793061657674225)
      ·
        refine ⟨368086867691844796243255669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 490782490255793061657674225 368086867691844796243255669)
        ·
          refine ⟨34508143846110449647805219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 368086867691844796243255669 34508143846110449647805219)
          ·
            refine ⟨51762215769165674471707829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34508143846110449647805219 51762215769165674471707829)
            ·
              refine ⟨4852707728359281981722609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51762215769165674471707829 4852707728359281981722609)
              ·
                refine ⟨3639530796269461486291957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4852707728359281981722609 3639530796269461486291957)
                ·
                  refine ⟨341206012150262014339871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3639530796269461486291957 341206012150262014339871)
                  ·
                    rfl

theorem cell23_5980467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 2, 5].length) (baseStart_5980467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980467 prefixEnd_5980467 := by exact prefixLift 5980467
  have htrace : WordTrace (prefixWord ++ tailWord_5980467) baseStart_5980467 baseEnd_5980467 := by
    simpa [prefixWord, tailWord_5980467, baseEnd_5980467] using wordTrace_append hprefix tailTrace_5980467
  have hstable : (prefixWord ++ tailWord_5980467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980467).length < 2 ^ (prefixWord ++ tailWord_5980467).sum := by decide
  have hdescent : baseEnd_5980467 < baseStart_5980467 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980478 : List Nat := [4, 2, 1, 2, 1, 4, 2, 1, 2, 2, 2]
def baseStart_5980478 : Nat := 118140960795 + 5980478 * 2 ^ 59
def prefixEnd_5980478 : Nat := 4983230072969 + 3 ^ 40 * 5980478 * 2
def baseEnd_5980478 : Nat := 3070859757639557586021289

theorem tailTrace_5980478 : CollatzResearch.WordTrace tailWord_5980478 prefixEnd_5980478 3070859757639557586021289 := by
  unfold tailWord_5980478
  simp only [CollatzResearch.WordTrace]
  refine ⟨27265744053469633146368761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145417301618504710113966725 27265744053469633146368761)
  ·
    refine ⟨20449308040102224859776571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27265744053469633146368761 20449308040102224859776571)
    ·
      refine ⟨30673962060153337289664857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20449308040102224859776571 30673962060153337289664857)
      ·
        refine ⟨23005471545115002967248643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30673962060153337289664857 23005471545115002967248643)
        ·
          refine ⟨34508207317672504450872965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23005471545115002967248643 34508207317672504450872965)
          ·
            refine ⟨6470288872063594584538681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34508207317672504450872965 6470288872063594584538681)
            ·
              refine ⟨4852716654047695938404011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6470288872063594584538681 4852716654047695938404011)
              ·
                refine ⟨7279074981071543907606017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4852716654047695938404011 7279074981071543907606017)
                ·
                  refine ⟨5459306235803657930704513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7279074981071543907606017 5459306235803657930704513)
                  ·
                    refine ⟨4094479676852743448028385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5459306235803657930704513 4094479676852743448028385)
                    ·
                      refine ⟨3070859757639557586021289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4094479676852743448028385 3070859757639557586021289)
                      ·
                        rfl

theorem cell23_5980478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_5980478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980478 prefixEnd_5980478 := by exact prefixLift 5980478
  have htrace : WordTrace (prefixWord ++ tailWord_5980478) baseStart_5980478 baseEnd_5980478 := by
    simpa [prefixWord, tailWord_5980478, baseEnd_5980478] using wordTrace_append hprefix tailTrace_5980478
  have hstable : (prefixWord ++ tailWord_5980478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980478).length < 2 ^ (prefixWord ++ tailWord_5980478).sum := by decide
  have hdescent : baseEnd_5980478 < baseStart_5980478 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980483 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 3, 3, 4]
def baseStart_5980483 : Nat := 118140960795 + 5980483 * 2 ^ 59
def prefixEnd_5980483 : Nat := 4983230072969 + 3 ^ 40 * 5980483 * 2
def baseEnd_5980483 : Nat := 3070862325042830066458765

theorem tailTrace_5980483 : CollatzResearch.WordTrace tailWord_5980483 prefixEnd_5980483 3070862325042830066458765 := by
  unfold tailWord_5980483
  simp only [CollatzResearch.WordTrace]
  refine ⟨218126134792738951024882103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145417423195159300683254735 218126134792738951024882103)
  ·
    refine ⟨327189202189108426537323155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218126134792738951024882103 327189202189108426537323155)
    ·
      refine ⟨490783803283662639805984733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327189202189108426537323155 490783803283662639805984733)
      ·
        refine ⟨184043926231373489927244275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 490783803283662639805984733 184043926231373489927244275)
        ·
          refine ⟨276065889347060234890866413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184043926231373489927244275 276065889347060234890866413)
          ·
            refine ⟨103524708505147588084074905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 276065889347060234890866413 103524708505147588084074905)
            ·
              refine ⟨77643531378860691063056179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103524708505147588084074905 77643531378860691063056179)
              ·
                refine ⟨116465297068291036594584269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77643531378860691063056179 116465297068291036594584269)
                ·
                  refine ⟨43674486400609138722969101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116465297068291036594584269 43674486400609138722969101)
                  ·
                    refine ⟨16377932400228427021113413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43674486400609138722969101 16377932400228427021113413)
                    ·
                      refine ⟨3070862325042830066458765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16377932400228427021113413 3070862325042830066458765)
                      ·
                        rfl

theorem cell23_5980483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3, 4].length) (baseStart_5980483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980483 prefixEnd_5980483 := by exact prefixLift 5980483
  have htrace : WordTrace (prefixWord ++ tailWord_5980483) baseStart_5980483 baseEnd_5980483 := by
    simpa [prefixWord, tailWord_5980483, baseEnd_5980483] using wordTrace_append hprefix tailTrace_5980483
  have hstable : (prefixWord ++ tailWord_5980483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980483).length < 2 ^ (prefixWord ++ tailWord_5980483).sum := by decide
  have hdescent : baseEnd_5980483 < baseStart_5980483 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980543 : List Nat := [1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 6]
def baseStart_5980543 : Nat := 118140960795 + 5980543 * 2 ^ 59
def prefixEnd_5980543 : Nat := 4983230072969 + 3 ^ 40 * 5980543 * 2
def baseEnd_5980543 : Nat := 3070893133882099831708489

theorem tailTrace_5980543 : CollatzResearch.WordTrace tailWord_5980543 prefixEnd_5980543 3070893133882099831708489 := by
  unfold tailWord_5980543
  simp only [CollatzResearch.WordTrace]
  refine ⟨218128323172521581272066283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145418882115014387514710855 218128323172521581272066283)
  ·
    refine ⟨327192484758782371908099425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218128323172521581272066283 327192484758782371908099425)
    ·
      refine ⟨245394363569086778931074569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327192484758782371908099425 245394363569086778931074569)
      ·
        refine ⟨184045772676815084198305927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245394363569086778931074569 184045772676815084198305927)
        ·
          refine ⟨276068659015222626297458891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184045772676815084198305927 276068659015222626297458891)
          ·
            refine ⟨414102988522833939446188337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276068659015222626297458891 414102988522833939446188337)
            ·
              refine ⟨310577241392125454584641253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 414102988522833939446188337 310577241392125454584641253)
              ·
                refine ⟨58233232761023522734620235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 310577241392125454584641253 58233232761023522734620235)
                ·
                  refine ⟨87349849141535284101930353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58233232761023522734620235 87349849141535284101930353)
                  ·
                    refine ⟨65512386856151463076447765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 87349849141535284101930353 65512386856151463076447765)
                    ·
                      refine ⟨3070893133882099831708489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65512386856151463076447765 3070893133882099831708489)
                      ·
                        rfl

theorem cell23_5980543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_5980543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980543 prefixEnd_5980543 := by exact prefixLift 5980543
  have htrace : WordTrace (prefixWord ++ tailWord_5980543) baseStart_5980543 baseEnd_5980543 := by
    simpa [prefixWord, tailWord_5980543, baseEnd_5980543] using wordTrace_append hprefix tailTrace_5980543
  have hstable : (prefixWord ++ tailWord_5980543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980543).length < 2 ^ (prefixWord ++ tailWord_5980543).sum := by decide
  have hdescent : baseEnd_5980543 < baseStart_5980543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980554 : List Nat := [3, 1, 2, 5, 1, 1, 1, 1, 1, 4, 3]
def baseStart_5980554 : Nat := 118140960795 + 5980554 * 2 ^ 59
def prefixEnd_5980554 : Nat := 4983230072969 + 3 ^ 40 * 5980554 * 2
def baseEnd_5980554 : Nat := 3070898782169299288670939

theorem tailTrace_5980554 : CollatzResearch.WordTrace tailWord_5980554 prefixEnd_5980554 3070898782169299288670939 := by
  unfold tailWord_5980554
  simp only [CollatzResearch.WordTrace]
  refine ⟨54532181093870432537679179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145419149583654486767144477 54532181093870432537679179)
  ·
    refine ⟨81798271640805648806518769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54532181093870432537679179 81798271640805648806518769)
    ·
      refine ⟨61348703730604236604889077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81798271640805648806518769 61348703730604236604889077)
      ·
        refine ⟨5751440974744147181708351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61348703730604236604889077 5751440974744147181708351)
        ·
          refine ⟨8627161462116220772562527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5751440974744147181708351 8627161462116220772562527)
          ·
            refine ⟨12940742193174331158843791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8627161462116220772562527 12940742193174331158843791)
            ·
              refine ⟨19411113289761496738265687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12940742193174331158843791 19411113289761496738265687)
              ·
                refine ⟨29116669934642245107398531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19411113289761496738265687 29116669934642245107398531)
                ·
                  refine ⟨43675004901963367661097797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29116669934642245107398531 43675004901963367661097797)
                  ·
                    refine ⟨8189063419118131436455837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43675004901963367661097797 8189063419118131436455837)
                    ·
                      refine ⟨3070898782169299288670939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8189063419118131436455837 3070898782169299288670939)
                      ·
                        rfl

theorem cell23_5980554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_5980554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980554 prefixEnd_5980554 := by exact prefixLift 5980554
  have htrace : WordTrace (prefixWord ++ tailWord_5980554) baseStart_5980554 baseEnd_5980554 := by
    simpa [prefixWord, tailWord_5980554, baseEnd_5980554] using wordTrace_append hprefix tailTrace_5980554
  have hstable : (prefixWord ++ tailWord_5980554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980554).length < 2 ^ (prefixWord ++ tailWord_5980554).sum := by decide
  have hdescent : baseEnd_5980554 < baseStart_5980554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980574 : List Nat := [4, 3, 1, 2, 1, 1, 3, 2, 6]
def baseStart_5980574 : Nat := 118140960795 + 5980574 * 2 ^ 59
def prefixEnd_5980574 : Nat := 4983230072969 + 3 ^ 40 * 5980574 * 2
def baseEnd_5980574 : Nat := 341212116864709912268983

theorem tailTrace_5980574 : CollatzResearch.WordTrace tailWord_5980574 prefixEnd_5980574 341212116864709912268983 := by
  unfold tailWord_5980574
  simp only [CollatzResearch.WordTrace]
  refine ⟨27266181729426159195805597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145419635890272849044296517 27266181729426159195805597)
  ·
    refine ⟨10224818148534809698427099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27266181729426159195805597 10224818148534809698427099)
    ·
      refine ⟨15337227222802214547640649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10224818148534809698427099 15337227222802214547640649)
      ·
        refine ⟨11502920417101660910730487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15337227222802214547640649 11502920417101660910730487)
        ·
          refine ⟨17254380625652491366095731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11502920417101660910730487 17254380625652491366095731)
          ·
            refine ⟨25881570938478737049143597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17254380625652491366095731 25881570938478737049143597)
            ·
              refine ⟨9705589101929526393428849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25881570938478737049143597 9705589101929526393428849)
              ·
                refine ⟨7279191826447144795071637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9705589101929526393428849 7279191826447144795071637)
                ·
                  refine ⟨341212116864709912268983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7279191826447144795071637 341212116864709912268983)
                  ·
                    rfl

theorem cell23_5980574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_5980574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980574 prefixEnd_5980574 := by exact prefixLift 5980574
  have htrace : WordTrace (prefixWord ++ tailWord_5980574) baseStart_5980574 baseEnd_5980574 := by
    simpa [prefixWord, tailWord_5980574, baseEnd_5980574] using wordTrace_append hprefix tailTrace_5980574
  have hstable : (prefixWord ++ tailWord_5980574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980574).length < 2 ^ (prefixWord ++ tailWord_5980574).sum := by decide
  have hdescent : baseEnd_5980574 < baseStart_5980574 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980604 : List Nat := [2, 2, 2, 4, 1, 2, 2, 2, 1, 5]
def baseStart_5980604 : Nat := 118140960795 + 5980604 * 2 ^ 59
def prefixEnd_5980604 : Nat := 4983230072969 + 3 ^ 40 * 5980604 * 2
def baseEnd_5980604 : Nat := 1023641485400674697681903

theorem tailTrace_5980604 : CollatzResearch.WordTrace tailWord_5980604 prefixEnd_5980604 1023641485400674697681903 := by
  unfold tailWord_5980604
  simp only [CollatzResearch.WordTrace]
  refine ⟨109065274012650294345018433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145420365350200392460024577 109065274012650294345018433)
  ·
    refine ⟨81798955509487720758763825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109065274012650294345018433 81798955509487720758763825)
    ·
      refine ⟨61349216632115790569072869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81798955509487720758763825 61349216632115790569072869)
      ·
        refine ⟨11502978118521710731701163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61349216632115790569072869 11502978118521710731701163)
        ·
          refine ⟨17254467177782566097551745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11502978118521710731701163 17254467177782566097551745)
          ·
            refine ⟨12940850383336924573163809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17254467177782566097551745 12940850383336924573163809)
            ·
              refine ⟨9705637787502693429872857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12940850383336924573163809 9705637787502693429872857)
              ·
                refine ⟨7279228340627020072404643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9705637787502693429872857 7279228340627020072404643)
                ·
                  refine ⟨10918842510940530108606965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7279228340627020072404643 10918842510940530108606965)
                  ·
                    refine ⟨1023641485400674697681903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10918842510940530108606965 1023641485400674697681903)
                    ·
                      rfl

theorem cell23_5980604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2, 1, 5].length) (baseStart_5980604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980604 prefixEnd_5980604 := by exact prefixLift 5980604
  have htrace : WordTrace (prefixWord ++ tailWord_5980604) baseStart_5980604 baseEnd_5980604 := by
    simpa [prefixWord, tailWord_5980604, baseEnd_5980604] using wordTrace_append hprefix tailTrace_5980604
  have hstable : (prefixWord ++ tailWord_5980604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980604).length < 2 ^ (prefixWord ++ tailWord_5980604).sum := by decide
  have hdescent : baseEnd_5980604 < baseStart_5980604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980657 : List Nat := [1, 2, 2, 2, 3, 1, 2, 3, 1, 3, 3]
def baseStart_5980657 : Nat := 118140960795 + 5980657 * 2 ^ 59
def prefixEnd_5980657 : Nat := 4983230072969 + 3 ^ 40 * 5980657 * 2
def baseEnd_5980657 : Nat := 3070951670676712385682965

theorem tailTrace_5980657 : CollatzResearch.WordTrace tailWord_5980657 prefixEnd_5980657 3070951670676712385682965 := by
  unfold tailWord_5980657
  simp only [CollatzResearch.WordTrace]
  refine ⟨218132481094108578741716225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145421654062739052494477483 218132481094108578741716225)
  ·
    refine ⟨163599360820581434056287169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218132481094108578741716225 163599360820581434056287169)
    ·
      refine ⟨122699520615436075542215377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163599360820581434056287169 122699520615436075542215377)
      ·
        refine ⟨92024640461577056656661533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122699520615436075542215377 92024640461577056656661533)
        ·
          refine ⟨34509240173091396246248075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92024640461577056656661533 34509240173091396246248075)
          ·
            refine ⟨51763860259637094369372113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34509240173091396246248075 51763860259637094369372113)
            ·
              refine ⟨38822895194727820777029085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51763860259637094369372113 38822895194727820777029085)
              ·
                refine ⟨14558585698022932791385907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38822895194727820777029085 14558585698022932791385907)
                ·
                  refine ⟨21837878547034399187078861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14558585698022932791385907 21837878547034399187078861)
                  ·
                    refine ⟨8189204455137899695154573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21837878547034399187078861 8189204455137899695154573)
                    ·
                      refine ⟨3070951670676712385682965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8189204455137899695154573 3070951670676712385682965)
                      ·
                        rfl

theorem cell23_5980657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 3, 3].length) (baseStart_5980657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980657 prefixEnd_5980657 := by exact prefixLift 5980657
  have htrace : WordTrace (prefixWord ++ tailWord_5980657) baseStart_5980657 baseEnd_5980657 := by
    simpa [prefixWord, tailWord_5980657, baseEnd_5980657] using wordTrace_append hprefix tailTrace_5980657
  have hstable : (prefixWord ++ tailWord_5980657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980657).length < 2 ^ (prefixWord ++ tailWord_5980657).sum := by decide
  have hdescent : baseEnd_5980657 < baseStart_5980657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980658 : List Nat := [3, 2, 1, 4, 3, 1, 1, 2, 1, 1, 4]
def baseStart_5980658 : Nat := 118140960795 + 5980658 * 2 ^ 59
def prefixEnd_5980658 : Nat := 4983230072969 + 3 ^ 40 * 5980658 * 2
def baseEnd_5980658 : Nat := 3070952184157366881770461

theorem tailTrace_5980658 : CollatzResearch.WordTrace tailWord_5980658 prefixEnd_5980658 3070952184157366881770461 := by
  unfold tailWord_5980658
  simp only [CollatzResearch.WordTrace]
  refine ⟨54533129391776238978125657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145421678378069970608335085 54533129391776238978125657)
  ·
    refine ⟨40899847043832179233594243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54533129391776238978125657 40899847043832179233594243)
    ·
      refine ⟨61349770565748268850391365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40899847043832179233594243 61349770565748268850391365)
      ·
        refine ⟨11503081981077800409448381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61349770565748268850391365 11503081981077800409448381)
        ·
          refine ⟨4313655742904175153543143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11503081981077800409448381 4313655742904175153543143)
          ·
            refine ⟨6470483614356262730314715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4313655742904175153543143 6470483614356262730314715)
            ·
              refine ⟨9705725421534394095472073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6470483614356262730314715 9705725421534394095472073)
              ·
                refine ⟨7279294066150795571604055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9705725421534394095472073 7279294066150795571604055)
                ·
                  refine ⟨10918941099226193357406083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7279294066150795571604055 10918941099226193357406083)
                  ·
                    refine ⟨16378411648839290036109125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10918941099226193357406083 16378411648839290036109125)
                    ·
                      refine ⟨3070952184157366881770461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16378411648839290036109125 3070952184157366881770461)
                      ·
                        rfl

theorem cell23_5980658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_5980658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980658 prefixEnd_5980658 := by exact prefixLift 5980658
  have htrace : WordTrace (prefixWord ++ tailWord_5980658) baseStart_5980658 baseEnd_5980658 := by
    simpa [prefixWord, tailWord_5980658, baseEnd_5980658] using wordTrace_append hprefix tailTrace_5980658
  have hstable : (prefixWord ++ tailWord_5980658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980658).length < 2 ^ (prefixWord ++ tailWord_5980658).sum := by decide
  have hdescent : baseEnd_5980658 < baseStart_5980658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980661 : List Nat := [1, 3, 5, 1, 2, 1, 1, 1, 3, 2, 3]
def baseStart_5980661 : Nat := 118140960795 + 5980661 * 2 ^ 59
def prefixEnd_5980661 : Nat := 4983230072969 + 3 ^ 40 * 5980661 * 2
def baseEnd_5980661 : Nat := 3070953724599330370032947

theorem tailTrace_5980661 : CollatzResearch.WordTrace tailWord_5980661 prefixEnd_5980661 3070953724599330370032947 := by
  unfold tailWord_5980661
  simp only [CollatzResearch.WordTrace]
  refine ⟨218132626986094087424861837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145421751324062724949907891 218132626986094087424861837)
  ·
    refine ⟨81799735119785282784323189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218132626986094087424861837 81799735119785282784323189)
    ·
      refine ⟨7668725167479870261030299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81799735119785282784323189 7668725167479870261030299)
      ·
        refine ⟨11503087751219805391545449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7668725167479870261030299 11503087751219805391545449)
        ·
          refine ⟨8627315813414854043659087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11503087751219805391545449 8627315813414854043659087)
          ·
            refine ⟨12940973720122281065488631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8627315813414854043659087 12940973720122281065488631)
            ·
              refine ⟨19411460580183421598232947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12940973720122281065488631 19411460580183421598232947)
              ·
                refine ⟨29117190870275132397349421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19411460580183421598232947 29117190870275132397349421)
                ·
                  refine ⟨10918946576353174649006033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29117190870275132397349421 10918946576353174649006033)
                  ·
                    refine ⟨8189209932264880986754525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10918946576353174649006033 8189209932264880986754525)
                    ·
                      refine ⟨3070953724599330370032947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8189209932264880986754525 3070953724599330370032947)
                      ·
                        rfl

theorem cell23_5980661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_5980661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980661 prefixEnd_5980661 := by exact prefixLift 5980661
  have htrace : WordTrace (prefixWord ++ tailWord_5980661) baseStart_5980661 baseEnd_5980661 := by
    simpa [prefixWord, tailWord_5980661, baseEnd_5980661] using wordTrace_append hprefix tailTrace_5980661
  have hstable : (prefixWord ++ tailWord_5980661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980661).length < 2 ^ (prefixWord ++ tailWord_5980661).sum := by decide
  have hdescent : baseEnd_5980661 < baseStart_5980661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980678 : List Nat := [6, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5]
def baseStart_5980678 : Nat := 118140960795 + 5980678 * 2 ^ 59
def prefixEnd_5980678 : Nat := 4983230072969 + 3 ^ 40 * 5980678 * 2
def baseEnd_5980678 : Nat := 3070962453770456803520369

theorem tailTrace_5980678 : CollatzResearch.WordTrace tailWord_5980678 prefixEnd_5980678 3070962453770456803520369 := by
  unfold tailWord_5980678
  simp only [CollatzResearch.WordTrace]
  refine ⟨6816663969594765604007209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 145422164684688332885487125 6816663969594765604007209)
  ·
    refine ⟨5112497977196074203005407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6816663969594765604007209 5112497977196074203005407)
    ·
      refine ⟨7668746965794111304508111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5112497977196074203005407 7668746965794111304508111)
      ·
        refine ⟨11503120448691166956762167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7668746965794111304508111 11503120448691166956762167)
        ·
          refine ⟨17254680673036750435143251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11503120448691166956762167 17254680673036750435143251)
          ·
            refine ⟨25882021009555125652714877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17254680673036750435143251 25882021009555125652714877)
            ·
              refine ⟨9705757878583172119768079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25882021009555125652714877 9705757878583172119768079)
              ·
                refine ⟨14558636817874758179652119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9705757878583172119768079 14558636817874758179652119)
                ·
                  refine ⟨21837955226812137269478179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14558636817874758179652119 21837955226812137269478179)
                  ·
                    refine ⟨32756932840218205904217269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21837955226812137269478179 32756932840218205904217269)
                    ·
                      refine ⟨3070962453770456803520369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32756932840218205904217269 3070962453770456803520369)
                      ·
                        rfl

theorem cell23_5980678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_5980678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980678 prefixEnd_5980678 := by exact prefixLift 5980678
  have htrace : WordTrace (prefixWord ++ tailWord_5980678) baseStart_5980678 baseEnd_5980678 := by
    simpa [prefixWord, tailWord_5980678, baseEnd_5980678] using wordTrace_append hprefix tailTrace_5980678
  have hstable : (prefixWord ++ tailWord_5980678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980678).length < 2 ^ (prefixWord ++ tailWord_5980678).sum := by decide
  have hdescent : baseEnd_5980678 < baseStart_5980678 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980692 : List Nat := [2, 4, 3, 1, 1, 1, 4, 2, 1, 2, 2]
def baseStart_5980692 : Nat := 118140960795 + 5980692 * 2 ^ 59
def prefixEnd_5980692 : Nat := 4983230072969 + 3 ^ 40 * 5980692 * 2
def baseEnd_5980692 : Nat := 3070969642499619748745305

theorem tailTrace_5980692 : CollatzResearch.WordTrace tailWord_5980692 prefixEnd_5980692 3070969642499619748745305 := by
  unfold tailWord_5980692
  simp only [CollatzResearch.WordTrace]
  refine ⟨109066878824490889859620165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145422505099321186479493553 109066878824490889859620165)
  ·
    refine ⟨20450039779592041848678781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109066878824490889859620165 20450039779592041848678781)
    ·
      refine ⟨7668764917347015693254543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20450039779592041848678781 7668764917347015693254543)
      ·
        refine ⟨11503147376020523539881815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7668764917347015693254543 11503147376020523539881815)
        ·
          refine ⟨17254721064030785309822723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11503147376020523539881815 17254721064030785309822723)
          ·
            refine ⟨25882081596046177964734085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17254721064030785309822723 25882081596046177964734085)
            ·
              refine ⟨4852890299258658368387641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25882081596046177964734085 4852890299258658368387641)
              ·
                refine ⟨3639667724443993776290731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4852890299258658368387641 3639667724443993776290731)
                ·
                  refine ⟨5459501586665990664436097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3639667724443993776290731 5459501586665990664436097)
                  ·
                    refine ⟨4094626189999492998327073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5459501586665990664436097 4094626189999492998327073)
                    ·
                      refine ⟨3070969642499619748745305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4094626189999492998327073 3070969642499619748745305)
                      ·
                        rfl

theorem cell23_5980692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_5980692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980692 prefixEnd_5980692 := by exact prefixLift 5980692
  have htrace : WordTrace (prefixWord ++ tailWord_5980692) baseStart_5980692 baseEnd_5980692 := by
    simpa [prefixWord, tailWord_5980692, baseEnd_5980692] using wordTrace_append hprefix tailTrace_5980692
  have hstable : (prefixWord ++ tailWord_5980692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980692).length < 2 ^ (prefixWord ++ tailWord_5980692).sum := by decide
  have hdescent : baseEnd_5980692 < baseStart_5980692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980707 : List Nat := [1, 1, 1, 4, 4, 2, 1, 1, 2, 6]
def baseStart_5980707 : Nat := 118140960795 + 5980707 * 2 ^ 59
def prefixEnd_5980707 : Nat := 4983230072969 + 3 ^ 40 * 5980707 * 2
def baseEnd_5980707 : Nat := 1023659114903145730019245

theorem tailTrace_5980707 : CollatzResearch.WordTrace tailWord_5980707 prefixEnd_5980707 1023659114903145730019245 := by
  unfold tailWord_5980707
  simp only [CollatzResearch.WordTrace]
  refine ⟨218134304743927437281036375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145422869829284958187357583 218134304743927437281036375)
  ·
    refine ⟨327201457115891155921554563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218134304743927437281036375 327201457115891155921554563)
    ·
      refine ⟨490802185673836733882331845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327201457115891155921554563 490802185673836733882331845)
      ·
        refine ⟨92025409813844387602937221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 490802185673836733882331845 92025409813844387602937221)
        ·
          refine ⟨17254764340095822675550729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92025409813844387602937221 17254764340095822675550729)
          ·
            refine ⟨12941073255071867006663047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17254764340095822675550729 12941073255071867006663047)
            ·
              refine ⟨19411609882607800509994571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12941073255071867006663047 19411609882607800509994571)
              ·
                refine ⟨29117414823911700764991857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19411609882607800509994571 29117414823911700764991857)
                ·
                  refine ⟨21838061117933775573743893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29117414823911700764991857 21838061117933775573743893)
                  ·
                    refine ⟨1023659114903145730019245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21838061117933775573743893 1023659114903145730019245)
                    ·
                      rfl

theorem cell23_5980707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 6].length) (baseStart_5980707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980707 prefixEnd_5980707 := by exact prefixLift 5980707
  have htrace : WordTrace (prefixWord ++ tailWord_5980707) baseStart_5980707 baseEnd_5980707 := by
    simpa [prefixWord, tailWord_5980707, baseEnd_5980707] using wordTrace_append hprefix tailTrace_5980707
  have hstable : (prefixWord ++ tailWord_5980707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980707).length < 2 ^ (prefixWord ++ tailWord_5980707).sum := by decide
  have hdescent : baseEnd_5980707 < baseStart_5980707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980720 : List Nat := [2, 1, 1, 1, 2, 3, 3, 1, 9]
def baseStart_5980720 : Nat := 118140960795 + 5980720 * 2 ^ 59
def prefixEnd_5980720 : Nat := 4983230072969 + 3 ^ 40 * 5980720 * 2
def baseEnd_5980720 : Nat := 341220446661993959910575

theorem tailTrace_5980720 : CollatzResearch.WordTrace tailWord_5980720 prefixEnd_5980720 341220446661993959910575 := by
  unfold tailWord_5980720
  simp only [CollatzResearch.WordTrace]
  refine ⟨109067389446440170250629807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145423185928586893667506409 109067389446440170250629807)
  ·
    refine ⟨163601084169660255375944711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109067389446440170250629807 163601084169660255375944711)
    ·
      refine ⟨245401626254490383063917067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163601084169660255375944711 245401626254490383063917067)
      ·
        refine ⟨368102439381735574595875601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245401626254490383063917067 368102439381735574595875601)
        ·
          refine ⟨276076829536301680946906701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368102439381735574595875601 276076829536301680946906701)
          ·
            refine ⟨103528811076113130355090013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 276076829536301680946906701 103528811076113130355090013)
            ·
              refine ⟨38823304153542423883158755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103528811076113130355090013 38823304153542423883158755)
              ·
                refine ⟨58234956230313635824738133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38823304153542423883158755 58234956230313635824738133)
                ·
                  refine ⟨341220446661993959910575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 58234956230313635824738133 341220446661993959910575)
                  ·
                    rfl

theorem cell23_5980720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 9].length) (baseStart_5980720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980720 prefixEnd_5980720 := by exact prefixLift 5980720
  have htrace : WordTrace (prefixWord ++ tailWord_5980720) baseStart_5980720 baseEnd_5980720 := by
    simpa [prefixWord, tailWord_5980720, baseEnd_5980720] using wordTrace_append hprefix tailTrace_5980720
  have hstable : (prefixWord ++ tailWord_5980720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980720).length < 2 ^ (prefixWord ++ tailWord_5980720).sum := by decide
  have hdescent : baseEnd_5980720 < baseStart_5980720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980747 : List Nat := [1, 1, 1, 1, 3, 1, 5, 2, 2, 3, 3]
def baseStart_5980747 : Nat := 118140960795 + 5980747 * 2 ^ 59
def prefixEnd_5980747 : Nat := 4983230072969 + 3 ^ 40 * 5980747 * 2
def baseEnd_5980747 : Nat := 3070997883935617033557551

theorem tailTrace_5980747 : CollatzResearch.WordTrace tailWord_5980747 prefixEnd_5980747 3070997883935617033557551 := by
  unfold tailWord_5980747
  simp only [CollatzResearch.WordTrace]
  refine ⟨218135763663782524112492495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145423842442521682741661663 218135763663782524112492495)
  ·
    refine ⟨327203645495673786168738743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218135763663782524112492495 327203645495673786168738743)
    ·
      refine ⟨490805468243510679253108115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327203645495673786168738743 490805468243510679253108115)
      ·
        refine ⟨736208202365266018879662173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490805468243510679253108115 736208202365266018879662173)
        ·
          refine ⟨276078075886974757079873315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 736208202365266018879662173 276078075886974757079873315)
          ·
            refine ⟨414117113830462135619809973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276078075886974757079873315 414117113830462135619809973)
            ·
              refine ⟨38823479421605825214357185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 414117113830462135619809973 38823479421605825214357185)
              ·
                refine ⟨29117609566204368910767889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38823479421605825214357185 29117609566204368910767889)
                ·
                  refine ⟨21838207174653276683075917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29117609566204368910767889 21838207174653276683075917)
                  ·
                    refine ⟨8189327690494978756153469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21838207174653276683075917 8189327690494978756153469)
                    ·
                      refine ⟨3070997883935617033557551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8189327690494978756153469 3070997883935617033557551)
                      ·
                        rfl

theorem cell23_5980747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 3, 3].length) (baseStart_5980747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980747 prefixEnd_5980747 := by exact prefixLift 5980747
  have htrace : WordTrace (prefixWord ++ tailWord_5980747) baseStart_5980747 baseEnd_5980747 := by
    simpa [prefixWord, tailWord_5980747, baseEnd_5980747] using wordTrace_append hprefix tailTrace_5980747
  have hstable : (prefixWord ++ tailWord_5980747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980747).length < 2 ^ (prefixWord ++ tailWord_5980747).sum := by decide
  have hdescent : baseEnd_5980747 < baseStart_5980747 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980754 : List Nat := [3, 2, 2, 1, 2, 1, 1, 6, 5]
def baseStart_5980754 : Nat := 118140960795 + 5980754 * 2 ^ 59
def prefixEnd_5980754 : Nat := 4983230072969 + 3 ^ 40 * 5980754 * 2
def baseEnd_5980754 : Nat := 341222386477799834018891

theorem tailTrace_5980754 : CollatzResearch.WordTrace tailWord_5980754 prefixEnd_5980754 341222386477799834018891 := by
  unfold tailWord_5980754
  simp only [CollatzResearch.WordTrace]
  refine ⟨54534004743689291076999329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145424012649838109538664877 54534004743689291076999329)
  ·
    refine ⟨40900503557766968307749497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54534004743689291076999329 40900503557766968307749497)
    ·
      refine ⟨30675377668325226230812123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40900503557766968307749497 30675377668325226230812123)
      ·
        refine ⟨46013066502487839346218185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30675377668325226230812123 46013066502487839346218185)
        ·
          refine ⟨34509799876865879509663639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46013066502487839346218185 34509799876865879509663639)
          ·
            refine ⟨51764699815298819264495459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34509799876865879509663639 51764699815298819264495459)
            ·
              refine ⟨77647049722948228896743189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51764699815298819264495459 77647049722948228896743189)
              ·
                refine ⟨3639705455763198229534837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77647049722948228896743189 3639705455763198229534837)
                ·
                  refine ⟨341222386477799834018891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3639705455763198229534837 341222386477799834018891)
                  ·
                    rfl

theorem cell23_5980754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 6, 5].length) (baseStart_5980754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980754 prefixEnd_5980754 := by exact prefixLift 5980754
  have htrace : WordTrace (prefixWord ++ tailWord_5980754) baseStart_5980754 baseEnd_5980754 := by
    simpa [prefixWord, tailWord_5980754, baseEnd_5980754] using wordTrace_append hprefix tailTrace_5980754
  have hstable : (prefixWord ++ tailWord_5980754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980754).length < 2 ^ (prefixWord ++ tailWord_5980754).sum := by decide
  have hdescent : baseEnd_5980754 < baseStart_5980754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980804 : List Nat := [2, 3, 2, 1, 3, 1, 1, 1, 4, 1, 4]
def baseStart_5980804 : Nat := 118140960795 + 5980804 * 2 ^ 59
def prefixEnd_5980804 : Nat := 4983230072969 + 3 ^ 40 * 5980804 * 2
def baseEnd_5980804 : Nat := 3071027152332923310544789

theorem tailTrace_5980804 : CollatzResearch.WordTrace tailWord_5980804 prefixEnd_5980804 3071027152332923310544789 := by
  unfold tailWord_5980804
  simp only [CollatzResearch.WordTrace]
  refine ⟨109068921312288011423658733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145425228416384015231544977 109068921312288011423658733)
  ·
    refine ⟨40900845492108004283872025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109068921312288011423658733 40900845492108004283872025)
    ·
      refine ⟨30675634119081003212904019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40900845492108004283872025 30675634119081003212904019)
      ·
        refine ⟨46013451178621504819356029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30675634119081003212904019 46013451178621504819356029)
        ·
          refine ⟨17255044191983064307258511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46013451178621504819356029 17255044191983064307258511)
          ·
            refine ⟨25882566287974596460887767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17255044191983064307258511 25882566287974596460887767)
            ·
              refine ⟨38823849431961894691331651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25882566287974596460887767 38823849431961894691331651)
              ·
                refine ⟨58235774147942842036997477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38823849431961894691331651 58235774147942842036997477)
                ·
                  refine ⟨10919207652739282881937027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58235774147942842036997477 10919207652739282881937027)
                  ·
                    refine ⟨16378811479108924322905541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10919207652739282881937027 16378811479108924322905541)
                    ·
                      refine ⟨3071027152332923310544789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16378811479108924322905541 3071027152332923310544789)
                      ·
                        rfl

theorem cell23_5980804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_5980804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980804 prefixEnd_5980804 := by exact prefixLift 5980804
  have htrace : WordTrace (prefixWord ++ tailWord_5980804) baseStart_5980804 baseEnd_5980804 := by
    simpa [prefixWord, tailWord_5980804, baseEnd_5980804] using wordTrace_append hprefix tailTrace_5980804
  have hstable : (prefixWord ++ tailWord_5980804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980804).length < 2 ^ (prefixWord ++ tailWord_5980804).sum := by decide
  have hdescent : baseEnd_5980804 < baseStart_5980804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980824 : List Nat := [2, 1, 2, 4, 1, 1, 1, 2, 4, 2, 3]
def baseStart_5980824 : Nat := 118140960795 + 5980824 * 2 ^ 59
def prefixEnd_5980824 : Nat := 4983230072969 + 3 ^ 40 * 5980824 * 2
def baseEnd_5980824 : Nat := 3071037421946013232294697

theorem tailTrace_5980824 : CollatzResearch.WordTrace tailWord_5980824 prefixEnd_5980824 3071037421946013232294697 := by
  unfold tailWord_5980824
  simp only [CollatzResearch.WordTrace]
  refine ⟨109069286042251783131522763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145425714723002377508697017 109069286042251783131522763)
  ·
    refine ⟨163603929063377674697284145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109069286042251783131522763 163603929063377674697284145)
    ·
      refine ⟨122702946797533256022963109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163603929063377674697284145 122702946797533256022963109)
      ·
        refine ⟨23006802524537485504305583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122702946797533256022963109 23006802524537485504305583)
        ·
          refine ⟨34510203786806228256458375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23006802524537485504305583 34510203786806228256458375)
          ·
            refine ⟨51765305680209342384687563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34510203786806228256458375 51765305680209342384687563)
            ·
              refine ⟨77647958520314013577031345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51765305680209342384687563 77647958520314013577031345)
              ·
                refine ⟨58235968890235510182773509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77647958520314013577031345 58235968890235510182773509)
                ·
                  refine ⟨10919244166919158159270033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58235968890235510182773509 10919244166919158159270033)
                  ·
                    refine ⟨8189433125189368619452525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10919244166919158159270033 8189433125189368619452525)
                    ·
                      refine ⟨3071037421946013232294697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8189433125189368619452525 3071037421946013232294697)
                      ·
                        rfl

theorem cell23_5980824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_5980824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980824 prefixEnd_5980824 := by exact prefixLift 5980824
  have htrace : WordTrace (prefixWord ++ tailWord_5980824) baseStart_5980824 baseEnd_5980824 := by
    simpa [prefixWord, tailWord_5980824, baseEnd_5980824] using wordTrace_append hprefix tailTrace_5980824
  have hstable : (prefixWord ++ tailWord_5980824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980824).length < 2 ^ (prefixWord ++ tailWord_5980824).sum := by decide
  have hdescent : baseEnd_5980824 < baseStart_5980824 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980874 : List Nat := [3, 1, 2, 1, 4, 1, 1, 2, 3, 5]
def baseStart_5980874 : Nat := 118140960795 + 5980874 * 2 ^ 59
def prefixEnd_5980874 : Nat := 4983230072969 + 3 ^ 40 * 5980874 * 2
def baseEnd_5980874 : Nat := 1023687698659579345556489

theorem tailTrace_5980874 : CollatzResearch.WordTrace tailWord_5980874 prefixEnd_5980874 1023687698659579345556489 := by
  unfold tailWord_5980874
  simp only [CollatzResearch.WordTrace]
  refine ⟨54535098933580606200591419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145426930489548283201577117 54535098933580606200591419)
  ·
    refine ⟨81802648400370909300887129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54535098933580606200591419 81802648400370909300887129)
    ·
      refine ⟨61351986300278181975665347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81802648400370909300887129 61351986300278181975665347)
      ·
        refine ⟨92027979450417272963498021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61351986300278181975665347 92027979450417272963498021)
        ·
          refine ⟨17255246146953238680655879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92027979450417272963498021 17255246146953238680655879)
          ·
            refine ⟨25882869220429858020983819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17255246146953238680655879 25882869220429858020983819)
            ·
              refine ⟨38824303830644787031475729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25882869220429858020983819 38824303830644787031475729)
              ·
                refine ⟨29118227872983590273606797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38824303830644787031475729 29118227872983590273606797)
                ·
                  refine ⟨10919335452368846352602549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29118227872983590273606797 10919335452368846352602549)
                  ·
                    refine ⟨1023687698659579345556489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10919335452368846352602549 1023687698659579345556489)
                    ·
                      rfl

theorem cell23_5980874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_5980874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980874 prefixEnd_5980874 := by exact prefixLift 5980874
  have htrace : WordTrace (prefixWord ++ tailWord_5980874) baseStart_5980874 baseEnd_5980874 := by
    simpa [prefixWord, tailWord_5980874, baseEnd_5980874] using wordTrace_append hprefix tailTrace_5980874
  have hstable : (prefixWord ++ tailWord_5980874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980874).length < 2 ^ (prefixWord ++ tailWord_5980874).sum := by decide
  have hdescent : baseEnd_5980874 < baseStart_5980874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980907 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 6]
def baseStart_5980907 : Nat := 118140960795 + 5980907 * 2 ^ 59
def prefixEnd_5980907 : Nat := 4983230072969 + 3 ^ 40 * 5980907 * 2
def baseEnd_5980907 : Nat := 3071080040840336407556815

theorem tailTrace_5980907 : CollatzResearch.WordTrace tailWord_5980907 prefixEnd_5980907 3071080040840336407556815 := by
  unfold tailWord_5980907
  simp only [CollatzResearch.WordTrace]
  refine ⟨218141599343202871438316975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145427732895468580958877983 218141599343202871438316975)
  ·
    refine ⟨327212399014804307157475463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218141599343202871438316975 327212399014804307157475463)
    ·
      refine ⟨490818598522206460736213195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327212399014804307157475463 490818598522206460736213195)
      ·
        refine ⟨736227897783309691104319793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490818598522206460736213195 736227897783309691104319793)
        ·
          refine ⟨552170923337482268328239845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 736227897783309691104319793 552170923337482268328239845)
          ·
            refine ⟨103532048125777925311544971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 552170923337482268328239845 103532048125777925311544971)
            ·
              refine ⟨155298072188666887967317457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103532048125777925311544971 155298072188666887967317457)
              ·
                refine ⟨116473554141500165975488093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155298072188666887967317457 116473554141500165975488093)
                ·
                  refine ⟨43677582803062562240808035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116473554141500165975488093 43677582803062562240808035)
                  ·
                    refine ⟨65516374204593843361212053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43677582803062562240808035 65516374204593843361212053)
                    ·
                      refine ⟨3071080040840336407556815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65516374204593843361212053 3071080040840336407556815)
                      ·
                        rfl

theorem cell23_5980907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 6].length) (baseStart_5980907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980907 prefixEnd_5980907 := by exact prefixLift 5980907
  have htrace : WordTrace (prefixWord ++ tailWord_5980907) baseStart_5980907 baseEnd_5980907 := by
    simpa [prefixWord, tailWord_5980907, baseEnd_5980907] using wordTrace_append hprefix tailTrace_5980907
  have hstable : (prefixWord ++ tailWord_5980907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980907).length < 2 ^ (prefixWord ++ tailWord_5980907).sum := by decide
  have hdescent : baseEnd_5980907 < baseStart_5980907 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980911 : List Nat := [1, 1, 2, 1, 5, 3, 1, 3, 1, 1, 4]
def baseStart_5980911 : Nat := 118140960795 + 5980911 * 2 ^ 59
def prefixEnd_5980911 : Nat := 4983230072969 + 3 ^ 40 * 5980911 * 2
def baseEnd_5980911 : Nat := 3071082094762954391906797

theorem tailTrace_5980911 : CollatzResearch.WordTrace tailWord_5980911 prefixEnd_5980911 3071082094762954391906797 := by
  unfold tailWord_5980911
  simp only [CollatzResearch.WordTrace]
  refine ⟨218141745235188380121462587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145427830156792253414308391 218141745235188380121462587)
  ·
    refine ⟨327212617852782570182193881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218141745235188380121462587 327212617852782570182193881)
    ·
      refine ⟨245409463389586927636645411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327212617852782570182193881 245409463389586927636645411)
      ·
        refine ⟨368114195084380391454968117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245409463389586927636645411 368114195084380391454968117)
        ·
          refine ⟨34510705789160661698903261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 368114195084380391454968117 34510705789160661698903261)
          ·
            refine ⟨12941514670935248137088723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34510705789160661698903261 12941514670935248137088723)
            ·
              refine ⟨19412272006402872205633085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12941514670935248137088723 19412272006402872205633085)
              ·
                refine ⟨7279602002401077077112407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19412272006402872205633085 7279602002401077077112407)
                ·
                  refine ⟨10919403003601615615668611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7279602002401077077112407 10919403003601615615668611)
                  ·
                    refine ⟨16379104505402423423502917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10919403003601615615668611 16379104505402423423502917)
                    ·
                      refine ⟨3071082094762954391906797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16379104505402423423502917 3071082094762954391906797)
                      ·
                        rfl

theorem cell23_5980911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3, 1, 1, 4].length) (baseStart_5980911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980911 prefixEnd_5980911 := by exact prefixLift 5980911
  have htrace : WordTrace (prefixWord ++ tailWord_5980911) baseStart_5980911 baseEnd_5980911 := by
    simpa [prefixWord, tailWord_5980911, baseEnd_5980911] using wordTrace_append hprefix tailTrace_5980911
  have hstable : (prefixWord ++ tailWord_5980911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980911).length < 2 ^ (prefixWord ++ tailWord_5980911).sum := by decide
  have hdescent : baseEnd_5980911 < baseStart_5980911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980927 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 7]
def baseStart_5980927 : Nat := 118140960795 + 5980927 * 2 ^ 59
def prefixEnd_5980927 : Nat := 4983230072969 + 3 ^ 40 * 5980927 * 2
def baseEnd_5980927 : Nat := 3071090310453426329306723

theorem tailTrace_5980927 : CollatzResearch.WordTrace tailWord_5980927 prefixEnd_5980927 3071090310453426329306723 := by
  unfold tailWord_5980927
  simp only [CollatzResearch.WordTrace]
  refine ⟨218142328803130414854045035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145428219202086943236030023 218142328803130414854045035)
  ·
    refine ⟨327213493204695622281067553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218142328803130414854045035 327213493204695622281067553)
    ·
      refine ⟨245410119903521716710800665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327213493204695622281067553 245410119903521716710800665)
      ·
        refine ⟨184057589927641287533100499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245410119903521716710800665 184057589927641287533100499)
        ·
          refine ⟨276086384891461931299650749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184057589927641287533100499 276086384891461931299650749)
          ·
            refine ⟨103532394334298224237369031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 276086384891461931299650749 103532394334298224237369031)
            ·
              refine ⟨155298591501447336356053547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103532394334298224237369031 155298591501447336356053547)
              ·
                refine ⟨232947887252171004534080321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155298591501447336356053547 232947887252171004534080321)
                ·
                  refine ⟨174710915439128253400560241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 232947887252171004534080321 174710915439128253400560241)
                  ·
                    refine ⟨131033186579346190050420181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 174710915439128253400560241 131033186579346190050420181)
                    ·
                      refine ⟨3071090310453426329306723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 131033186579346190050420181 3071090310453426329306723)
                      ·
                        rfl

theorem cell23_5980927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_5980927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980927 prefixEnd_5980927 := by exact prefixLift 5980927
  have htrace : WordTrace (prefixWord ++ tailWord_5980927) baseStart_5980927 baseEnd_5980927 := by
    simpa [prefixWord, tailWord_5980927, baseEnd_5980927] using wordTrace_append hprefix tailTrace_5980927
  have hstable : (prefixWord ++ tailWord_5980927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980927).length < 2 ^ (prefixWord ++ tailWord_5980927).sum := by decide
  have hdescent : baseEnd_5980927 < baseStart_5980927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980938 : List Nat := [3, 1, 2, 2, 1, 2, 5, 1, 2, 4]
def baseStart_5980938 : Nat := 118140960795 + 5980938 * 2 ^ 59
def prefixEnd_5980938 : Nat := 4983230072969 + 3 ^ 40 * 5980938 * 2
def baseEnd_5980938 : Nat := 1023698652913541928756391

theorem tailTrace_5980938 : CollatzResearch.WordTrace tailWord_5980938 prefixEnd_5980938 1023698652913541928756391 := by
  unfold tailWord_5980938
  simp only [CollatzResearch.WordTrace]
  refine ⟨54535682501522640933173867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145428486670727042488463645 54535682501522640933173867)
  ·
    refine ⟨81803523752283961399760801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54535682501522640933173867 81803523752283961399760801)
    ·
      refine ⟨61352642814212971049820601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81803523752283961399760801 61352642814212971049820601)
      ·
        refine ⟨46014482110659728287365451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61352642814212971049820601 46014482110659728287365451)
        ·
          refine ⟨69021723165989592431048177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46014482110659728287365451 69021723165989592431048177)
          ·
            refine ⟨51766292374492194323286133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69021723165989592431048177 51766292374492194323286133)
            ·
              refine ⟨4853089910108643217808075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51766292374492194323286133 4853089910108643217808075)
              ·
                refine ⟨7279634865162964826712113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4853089910108643217808075 7279634865162964826712113)
                ·
                  refine ⟨5459726148872223620034085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7279634865162964826712113 5459726148872223620034085)
                  ·
                    refine ⟨1023698652913541928756391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5459726148872223620034085 1023698652913541928756391)
                    ·
                      rfl

theorem cell23_5980938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 1, 2, 4].length) (baseStart_5980938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980938 prefixEnd_5980938 := by exact prefixLift 5980938
  have htrace : WordTrace (prefixWord ++ tailWord_5980938) baseStart_5980938 baseEnd_5980938 := by
    simpa [prefixWord, tailWord_5980938, baseEnd_5980938] using wordTrace_append hprefix tailTrace_5980938
  have hstable : (prefixWord ++ tailWord_5980938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980938).length < 2 ^ (prefixWord ++ tailWord_5980938).sum := by decide
  have hdescent : baseEnd_5980938 < baseStart_5980938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980961 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 6, 1, 3]
def baseStart_5980961 : Nat := 118140960795 + 5980961 * 2 ^ 59
def prefixEnd_5980961 : Nat := 4983230072969 + 3 ^ 40 * 5980961 * 2
def baseEnd_5980961 : Nat := 3071107768795679196281567

theorem tailTrace_5980961 : CollatzResearch.WordTrace tailWord_5980961 prefixEnd_5980961 3071107768795679196281567 := by
  unfold tailWord_5980961
  simp only [CollatzResearch.WordTrace]
  refine ⟨218143568885007238660782737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145429045923338159107188491 218143568885007238660782737)
  ·
    refine ⟨163607676663755428995587053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218143568885007238660782737 163607676663755428995587053)
    ·
      refine ⟨61352878748908285873345145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163607676663755428995587053 61352878748908285873345145)
      ·
        refine ⟨46014659061681214405008859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61352878748908285873345145 46014659061681214405008859)
        ·
          refine ⟨69021988592521821607513289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46014659061681214405008859 69021988592521821607513289)
          ·
            refine ⟨51766491444391366205634967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69021988592521821607513289 51766491444391366205634967)
            ·
              refine ⟨77649737166587049308452451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51766491444391366205634967 77649737166587049308452451)
              ·
                refine ⟨116474605749880573962678677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77649737166587049308452451 116474605749880573962678677)
                ·
                  refine ⟨5459747144525651904500563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 116474605749880573962678677 5459747144525651904500563)
                  ·
                    refine ⟨8189620716788477856750845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5459747144525651904500563 8189620716788477856750845)
                    ·
                      refine ⟨3071107768795679196281567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8189620716788477856750845 3071107768795679196281567)
                      ·
                        rfl

theorem cell23_5980961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_5980961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980961 prefixEnd_5980961 := by exact prefixLift 5980961
  have htrace : WordTrace (prefixWord ++ tailWord_5980961) baseStart_5980961 baseEnd_5980961 := by
    simpa [prefixWord, tailWord_5980961, baseEnd_5980961] using wordTrace_append hprefix tailTrace_5980961
  have hstable : (prefixWord ++ tailWord_5980961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980961).length < 2 ^ (prefixWord ++ tailWord_5980961).sum := by decide
  have hdescent : baseEnd_5980961 < baseStart_5980961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980962 : List Nat := [3, 3, 1, 1, 2, 2, 3, 3, 1, 2, 2]
def baseStart_5980962 : Nat := 118140960795 + 5980962 * 2 ^ 59
def prefixEnd_5980962 : Nat := 4983230072969 + 3 ^ 40 * 5980962 * 2
def baseEnd_5980962 : Nat := 3071108282276333692369063

theorem tailTrace_5980962 : CollatzResearch.WordTrace tailWord_5980962 prefixEnd_5980962 3071108282276333692369063 := by
  unfold tailWord_5980962
  simp only [CollatzResearch.WordTrace]
  refine ⟨54535901339500903957892285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145429070238669077221046093 54535901339500903957892285)
  ·
    refine ⟨20450963002312838984209607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54535901339500903957892285 20450963002312838984209607)
    ·
      refine ⟨30676444503469258476314411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20450963002312838984209607 30676444503469258476314411)
      ·
        refine ⟨46014666755203887714471617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30676444503469258476314411 46014666755203887714471617)
        ·
          refine ⟨34511000066402915785853713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46014666755203887714471617 34511000066402915785853713)
          ·
            refine ⟨25883250049802186839390285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34511000066402915785853713 25883250049802186839390285)
            ·
              refine ⟨9706218768675820064771357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25883250049802186839390285 9706218768675820064771357)
              ·
                refine ⟨3639832038253432524289259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9706218768675820064771357 3639832038253432524289259)
                ·
                  refine ⟨5459748057380148786433889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3639832038253432524289259 5459748057380148786433889)
                  ·
                    refine ⟨4094811043035111589825417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5459748057380148786433889 4094811043035111589825417)
                    ·
                      refine ⟨3071108282276333692369063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4094811043035111589825417 3071108282276333692369063)
                      ·
                        rfl

theorem cell23_5980962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 3, 1, 2, 2].length) (baseStart_5980962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980962 prefixEnd_5980962 := by exact prefixLift 5980962
  have htrace : WordTrace (prefixWord ++ tailWord_5980962) baseStart_5980962 baseEnd_5980962 := by
    simpa [prefixWord, tailWord_5980962, baseEnd_5980962] using wordTrace_append hprefix tailTrace_5980962
  have hstable : (prefixWord ++ tailWord_5980962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980962).length < 2 ^ (prefixWord ++ tailWord_5980962).sum := by decide
  have hdescent : baseEnd_5980962 < baseStart_5980962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980978 : List Nat := [3, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3]
def baseStart_5980978 : Nat := 118140960795 + 5980978 * 2 ^ 59
def prefixEnd_5980978 : Nat := 4983230072969 + 3 ^ 40 * 5980978 * 2
def baseEnd_5980978 : Nat := 3071116497966805629768989

theorem tailTrace_5980978 : CollatzResearch.WordTrace tailWord_5980978 prefixEnd_5980978 3071116497966805629768989 := by
  unfold tailWord_5980978
  simp only [CollatzResearch.WordTrace]
  refine ⟨54536047231486412641037897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145429459283963767042767725 54536047231486412641037897)
  ·
    refine ⟨40902035423614809480778423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54536047231486412641037897 40902035423614809480778423)
    ·
      refine ⟨61353053135422214221167635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40902035423614809480778423 61353053135422214221167635)
      ·
        refine ⟨92029579703133321331751453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61353053135422214221167635 92029579703133321331751453)
        ·
          refine ⟨34511092388674995499406795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92029579703133321331751453 34511092388674995499406795)
          ·
            refine ⟨51766638583012493249110193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34511092388674995499406795 51766638583012493249110193)
            ·
              refine ⟨38824978937259369936832645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51766638583012493249110193 38824978937259369936832645)
              ·
                refine ⟨7279683550736131863156121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38824978937259369936832645 7279683550736131863156121)
                ·
                  refine ⟨5459762663052098897367091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7279683550736131863156121 5459762663052098897367091)
                  ·
                    refine ⟨8189643994578148346050637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5459762663052098897367091 8189643994578148346050637)
                    ·
                      refine ⟨3071116497966805629768989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8189643994578148346050637 3071116497966805629768989)
                      ·
                        rfl

theorem cell23_5980978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3].length) (baseStart_5980978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980978 prefixEnd_5980978 := by exact prefixLift 5980978
  have htrace : WordTrace (prefixWord ++ tailWord_5980978) baseStart_5980978 baseEnd_5980978 := by
    simpa [prefixWord, tailWord_5980978, baseEnd_5980978] using wordTrace_append hprefix tailTrace_5980978
  have hstable : (prefixWord ++ tailWord_5980978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980978).length < 2 ^ (prefixWord ++ tailWord_5980978).sum := by decide
  have hdescent : baseEnd_5980978 < baseStart_5980978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5980984 : List Nat := [2, 1, 2, 1, 3, 2, 2, 1, 2, 3, 4]
def baseStart_5980984 : Nat := 118140960795 + 5980984 * 2 ^ 59
def prefixEnd_5980984 : Nat := 4983230072969 + 3 ^ 40 * 5980984 * 2
def baseEnd_5980984 : Nat := 3071119578850732606293961

theorem tailTrace_5980984 : CollatzResearch.WordTrace tailWord_5980984 prefixEnd_5980984 3071119578850732606293961 := by
  unfold tailWord_5980984
  simp only [CollatzResearch.WordTrace]
  refine ⟨109072203881961956794435003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145429605175949275725913337 109072203881961956794435003)
  ·
    refine ⟨163608305822942935191652505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109072203881961956794435003 163608305822942935191652505)
    ·
      refine ⟨122706229367207201393739379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163608305822942935191652505 122706229367207201393739379)
      ·
        refine ⟨184059344050810802090609069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122706229367207201393739379 184059344050810802090609069)
        ·
          refine ⟨69022254019054050783978401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184059344050810802090609069 69022254019054050783978401)
          ·
            refine ⟨51766690514290538087983801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69022254019054050783978401 51766690514290538087983801)
            ·
              refine ⟨38825017885717903565987851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51766690514290538087983801 38825017885717903565987851)
              ·
                refine ⟨58237526828576855348981777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38825017885717903565987851 58237526828576855348981777)
                ·
                  refine ⟨43678145121432641511736333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58237526828576855348981777 43678145121432641511736333)
                  ·
                    refine ⟨16379304420537240566901125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43678145121432641511736333 16379304420537240566901125)
                    ·
                      refine ⟨3071119578850732606293961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16379304420537240566901125 3071119578850732606293961)
                      ·
                        rfl

theorem cell23_5980984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 2, 3, 4].length) (baseStart_5980984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5980984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5980984 prefixEnd_5980984 := by exact prefixLift 5980984
  have htrace : WordTrace (prefixWord ++ tailWord_5980984) baseStart_5980984 baseEnd_5980984 := by
    simpa [prefixWord, tailWord_5980984, baseEnd_5980984] using wordTrace_append hprefix tailTrace_5980984
  have hstable : (prefixWord ++ tailWord_5980984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5980984).length < 2 ^ (prefixWord ++ tailWord_5980984).sum := by decide
  have hdescent : baseEnd_5980984 < baseStart_5980984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5980984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981018 : List Nat := [3, 1, 1, 2, 1, 5, 1, 2, 1, 4, 2]
def baseStart_5981018 : Nat := 118140960795 + 5981018 * 2 ^ 59
def prefixEnd_5981018 : Nat := 4983230072969 + 3 ^ 40 * 5981018 * 2
def baseEnd_5981018 : Nat := 3071137037192985473268805

theorem tailTrace_5981018 : CollatzResearch.WordTrace tailWord_5981018 prefixEnd_5981018 3071137037192985473268805 := by
  unfold tailWord_5981018
  simp only [CollatzResearch.WordTrace]
  refine ⟨54536411961450184348901927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145430431897200491597071805 54536411961450184348901927)
  ·
    refine ⟨81804617942175276523352891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54536411961450184348901927 81804617942175276523352891)
    ·
      refine ⟨122706926913262914785029337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81804617942175276523352891 122706926913262914785029337)
      ·
        refine ⟨92030195184947186088772003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122706926913262914785029337 92030195184947186088772003)
        ·
          refine ⟨138045292777420779133158005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92030195184947186088772003 138045292777420779133158005)
          ·
            refine ⟨12941746197883198043733563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 138045292777420779133158005 12941746197883198043733563)
            ·
              refine ⟨19412619296824797065600345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12941746197883198043733563 19412619296824797065600345)
              ·
                refine ⟨14559464472618597799200259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19412619296824797065600345 14559464472618597799200259)
                ·
                  refine ⟨21839196708927896698800389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14559464472618597799200259 21839196708927896698800389)
                  ·
                    refine ⟨4094849382923980631025073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21839196708927896698800389 4094849382923980631025073)
                    ·
                      refine ⟨3071137037192985473268805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4094849382923980631025073 3071137037192985473268805)
                      ·
                        rfl

theorem cell23_5981018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 1, 4, 2].length) (baseStart_5981018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981018 prefixEnd_5981018 := by exact prefixLift 5981018
  have htrace : WordTrace (prefixWord ++ tailWord_5981018) baseStart_5981018 baseEnd_5981018 := by
    simpa [prefixWord, tailWord_5981018, baseEnd_5981018] using wordTrace_append hprefix tailTrace_5981018
  have hstable : (prefixWord ++ tailWord_5981018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981018).length < 2 ^ (prefixWord ++ tailWord_5981018).sum := by decide
  have hdescent : baseEnd_5981018 < baseStart_5981018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981091 : List Nat := [1, 1, 1, 4, 1, 2, 2, 4, 2, 1, 4]
def baseStart_5981091 : Nat := 118140960795 + 5981091 * 2 ^ 59
def prefixEnd_5981091 : Nat := 4983230072969 + 3 ^ 40 * 5981091 * 2
def baseEnd_5981091 : Nat := 3071174521280763687655969

theorem tailTrace_5981091 : CollatzResearch.WordTrace tailWord_5981091 prefixEnd_5981091 3071174521280763687655969 := by
  unfold tailWord_5981091
  simp only [CollatzResearch.WordTrace]
  refine ⟨218148310374536270863015127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145432206916357513908676751 218148310374536270863015127)
  ·
    refine ⟨327222465561804406294522691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218148310374536270863015127 327222465561804406294522691)
    ·
      refine ⟨490833698342706609441784037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327222465561804406294522691 490833698342706609441784037)
      ·
        refine ⟨92031318439257489270334507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 490833698342706609441784037 92031318439257489270334507)
        ·
          refine ⟨138046977658886233905501761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92031318439257489270334507 138046977658886233905501761)
          ·
            refine ⟨103535233244164675429126321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138046977658886233905501761 103535233244164675429126321)
            ·
              refine ⟨77651424933123506571844741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103535233244164675429126321 77651424933123506571844741)
              ·
                refine ⟨14559642174960657482220889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77651424933123506571844741 14559642174960657482220889)
                ·
                  refine ⟨10919731631220493111665667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14559642174960657482220889 10919731631220493111665667)
                  ·
                    refine ⟨16379597446830739667498501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10919731631220493111665667 16379597446830739667498501)
                    ·
                      refine ⟨3071174521280763687655969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16379597446830739667498501 3071174521280763687655969)
                      ·
                        rfl

theorem cell23_5981091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_5981091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981091 prefixEnd_5981091 := by exact prefixLift 5981091
  have htrace : WordTrace (prefixWord ++ tailWord_5981091) baseStart_5981091 baseEnd_5981091 := by
    simpa [prefixWord, tailWord_5981091, baseEnd_5981091] using wordTrace_append hprefix tailTrace_5981091
  have hstable : (prefixWord ++ tailWord_5981091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981091).length < 2 ^ (prefixWord ++ tailWord_5981091).sum := by decide
  have hdescent : baseEnd_5981091 < baseStart_5981091 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981111 : List Nat := [1, 1, 3, 1, 3, 1, 3, 2, 1, 4, 3]
def baseStart_5981111 : Nat := 118140960795 + 5981111 * 2 ^ 59
def prefixEnd_5981111 : Nat := 4983230072969 + 3 ^ 40 * 5981111 * 2
def baseEnd_5981111 : Nat := 3071184790893853609405877

theorem tailTrace_5981111 : CollatzResearch.WordTrace tailWord_5981111 prefixEnd_5981111 3071184790893853609405877 := by
  unfold tailWord_5981111
  simp only [CollatzResearch.WordTrace]
  refine ⟨218149039834463814278743187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145432693222975876185828791 218149039834463814278743187)
  ·
    refine ⟨327223559751695721418114781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218149039834463814278743187 327223559751695721418114781)
    ·
      refine ⟨122708834906885895531793043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 327223559751695721418114781 122708834906885895531793043)
      ·
        refine ⟨184063252360328843297689565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122708834906885895531793043 184063252360328843297689565)
        ·
          refine ⟨69023719635123316236633587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184063252360328843297689565 69023719635123316236633587)
          ·
            refine ⟨103535579452684974354950381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69023719635123316236633587 103535579452684974354950381)
            ·
              refine ⟨38825842294756865383106393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103535579452684974354950381 38825842294756865383106393)
              ·
                refine ⟨29119381721067649037329795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38825842294756865383106393 29119381721067649037329795)
                ·
                  refine ⟨43679072581601473555994693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29119381721067649037329795 43679072581601473555994693)
                  ·
                    refine ⟨8189826109050276291749005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43679072581601473555994693 8189826109050276291749005)
                    ·
                      refine ⟨3071184790893853609405877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8189826109050276291749005 3071184790893853609405877)
                      ·
                        rfl

theorem cell23_5981111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 4, 3].length) (baseStart_5981111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981111 prefixEnd_5981111 := by exact prefixLift 5981111
  have htrace : WordTrace (prefixWord ++ tailWord_5981111) baseStart_5981111 baseEnd_5981111 := by
    simpa [prefixWord, tailWord_5981111, baseEnd_5981111] using wordTrace_append hprefix tailTrace_5981111
  have hstable : (prefixWord ++ tailWord_5981111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981111).length < 2 ^ (prefixWord ++ tailWord_5981111).sum := by decide
  have hdescent : baseEnd_5981111 < baseStart_5981111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981118 : List Nat := [4, 2, 1, 1, 1, 2, 1, 4, 3, 4]
def baseStart_5981118 : Nat := 118140960795 + 5981118 * 2 ^ 59
def prefixEnd_5981118 : Nat := 4983230072969 + 3 ^ 40 * 5981118 * 2
def baseEnd_5981118 : Nat := 1023729461752811694006115

theorem tailTrace_5981118 : CollatzResearch.WordTrace tailWord_5981118 prefixEnd_5981118 1023729461752811694006115 := by
  unfold tailWord_5981118
  simp only [CollatzResearch.WordTrace]
  refine ⟨27268661893179806809281001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145432863430292302982832005 27268661893179806809281001)
  ·
    refine ⟨20451496419884855106960751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27268661893179806809281001 20451496419884855106960751)
    ·
      refine ⟨30677244629827282660441127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20451496419884855106960751 30677244629827282660441127)
      ·
        refine ⟨46015866944740923990661691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30677244629827282660441127 46015866944740923990661691)
        ·
          refine ⟨69023800417111385985992537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46015866944740923990661691 69023800417111385985992537)
          ·
            refine ⟨51767850312833539489494403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69023800417111385985992537 51767850312833539489494403)
            ·
              refine ⟨77651775469250309234241605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51767850312833539489494403 77651775469250309234241605)
              ·
                refine ⟨14559707900484432981420301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77651775469250309234241605 14559707900484432981420301)
                ·
                  refine ⟨5459890462681662368032613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14559707900484432981420301 5459890462681662368032613)
                  ·
                    refine ⟨1023729461752811694006115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5459890462681662368032613 1023729461752811694006115)
                    ·
                      rfl

theorem cell23_5981118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_5981118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981118 prefixEnd_5981118 := by exact prefixLift 5981118
  have htrace : WordTrace (prefixWord ++ tailWord_5981118) baseStart_5981118 baseEnd_5981118 := by
    simpa [prefixWord, tailWord_5981118, baseEnd_5981118] using wordTrace_append hprefix tailTrace_5981118
  have hstable : (prefixWord ++ tailWord_5981118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981118).length < 2 ^ (prefixWord ++ tailWord_5981118).sum := by decide
  have hdescent : baseEnd_5981118 < baseStart_5981118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981135 : List Nat := [1, 1, 2, 1, 1, 6, 3, 3, 1, 4]
def baseStart_5981135 : Nat := 118140960795 + 5981135 * 2 ^ 59
def prefixEnd_5981135 : Nat := 4983230072969 + 3 ^ 40 * 5981135 * 2
def baseEnd_5981135 : Nat := 1023732371476520505168589

theorem tailTrace_5981135 : CollatzResearch.WordTrace tailWord_5981135 prefixEnd_5981135 1023732371476520505168589 := by
  unfold tailWord_5981135
  simp only [CollatzResearch.WordTrace]
  refine ⟨218149915186376866377616859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145433276790917910918411239 218149915186376866377616859)
  ·
    refine ⟨327224872779565299566425289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218149915186376866377616859 327224872779565299566425289)
    ·
      refine ⟨245418654584673974674818967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327224872779565299566425289 245418654584673974674818967)
      ·
        refine ⟨368127981877010962012228451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245418654584673974674818967 368127981877010962012228451)
        ·
          refine ⟨552191972815516443018342677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368127981877010962012228451 552191972815516443018342677)
          ·
            refine ⟨25883998725727333266484813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 552191972815516443018342677 25883998725727333266484813)
            ·
              refine ⟨9706499522147749974931805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25883998725727333266484813 9706499522147749974931805)
              ·
                refine ⟨3639937320805406240599427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9706499522147749974931805 3639937320805406240599427)
                ·
                  refine ⟨5459905981208109360899141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3639937320805406240599427 5459905981208109360899141)
                  ·
                    refine ⟨1023732371476520505168589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5459905981208109360899141 1023732371476520505168589)
                    ·
                      rfl

theorem cell23_5981135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 3, 1, 4].length) (baseStart_5981135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981135 prefixEnd_5981135 := by exact prefixLift 5981135
  have htrace : WordTrace (prefixWord ++ tailWord_5981135) baseStart_5981135 baseEnd_5981135 := by
    simpa [prefixWord, tailWord_5981135, baseEnd_5981135] using wordTrace_append hprefix tailTrace_5981135
  have hstable : (prefixWord ++ tailWord_5981135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981135).length < 2 ^ (prefixWord ++ tailWord_5981135).sum := by decide
  have hdescent : baseEnd_5981135 < baseStart_5981135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981168 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 6, 3, 2]
def baseStart_5981168 : Nat := 118140960795 + 5981168 * 2 ^ 59
def prefixEnd_5981168 : Nat := 4983230072969 + 3 ^ 40 * 5981168 * 2
def baseEnd_5981168 : Nat := 3071214059291159886393115

theorem tailTrace_5981168 : CollatzResearch.WordTrace tailWord_5981168 prefixEnd_5981168 3071214059291159886393115 := by
  unfold tailWord_5981168
  simp only [CollatzResearch.WordTrace]
  refine ⟨109075559397628656506784079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145434079196838208675712105 109075559397628656506784079)
  ·
    refine ⟨163613339096442984760176119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109075559397628656506784079 163613339096442984760176119)
    ·
      refine ⟨245420008644664477140264179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163613339096442984760176119 245420008644664477140264179)
      ·
        refine ⟨368130012966996715710396269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245420008644664477140264179 368130012966996715710396269)
        ·
          refine ⟨138048754862623768391398601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 368130012966996715710396269 138048754862623768391398601)
          ·
            refine ⟨103536566146967826293548951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138048754862623768391398601 103536566146967826293548951)
            ·
              refine ⟨155304849220451739440323427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103536566146967826293548951 155304849220451739440323427)
              ·
                refine ⟨232957273830677609160485141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155304849220451739440323427 232957273830677609160485141)
                ·
                  refine ⟨10919872210813012929397741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 232957273830677609160485141 10919872210813012929397741)
                  ·
                    refine ⟨4094952079054879848524153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10919872210813012929397741 4094952079054879848524153)
                    ·
                      refine ⟨3071214059291159886393115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4094952079054879848524153 3071214059291159886393115)
                      ·
                        rfl

theorem cell23_5981168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 6, 3, 2].length) (baseStart_5981168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981168 prefixEnd_5981168 := by exact prefixLift 5981168
  have htrace : WordTrace (prefixWord ++ tailWord_5981168) baseStart_5981168 baseEnd_5981168 := by
    simpa [prefixWord, tailWord_5981168, baseEnd_5981168] using wordTrace_append hprefix tailTrace_5981168
  have hstable : (prefixWord ++ tailWord_5981168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981168).length < 2 ^ (prefixWord ++ tailWord_5981168).sum := by decide
  have hdescent : baseEnd_5981168 < baseStart_5981168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981185 : List Nat := [1, 2, 4, 1, 2, 2, 1, 3, 2, 3, 2]
def baseStart_5981185 : Nat := 118140960795 + 5981185 * 2 ^ 59
def prefixEnd_5981185 : Nat := 4983230072969 + 3 ^ 40 * 5981185 * 2
def baseEnd_5981185 : Nat := 3071222788462286319880537

theorem tailTrace_5981185 : CollatzResearch.WordTrace tailWord_5981185 prefixEnd_5981185 3071222788462286319880537 := by
  unfold tailWord_5981185
  simp only [CollatzResearch.WordTrace]
  refine ⟨218151738836195724916937009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145434492557463816611291339 218151738836195724916937009)
  ·
    refine ⟨163613804127146793687702757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218151738836195724916937009 163613804127146793687702757)
    ·
      refine ⟨30677588273840023816444267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163613804127146793687702757 30677588273840023816444267)
      ·
        refine ⟨46016382410760035724666401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30677588273840023816444267 46016382410760035724666401)
        ·
          refine ⟨34512286808070026793499801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46016382410760035724666401 34512286808070026793499801)
          ·
            refine ⟨25884215106052520095124851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34512286808070026793499801 25884215106052520095124851)
            ·
              refine ⟨38826322659078780142687277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25884215106052520095124851 38826322659078780142687277)
              ·
                refine ⟨14559870997154542553507729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38826322659078780142687277 14559870997154542553507729)
                ·
                  refine ⟨10919903247865906915130797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14559870997154542553507729 10919903247865906915130797)
                  ·
                    refine ⟨4094963717949715093174049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10919903247865906915130797 4094963717949715093174049)
                    ·
                      refine ⟨3071222788462286319880537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4094963717949715093174049 3071222788462286319880537)
                      ·
                        rfl

theorem cell23_5981185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2, 3, 2].length) (baseStart_5981185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981185 prefixEnd_5981185 := by exact prefixLift 5981185
  have htrace : WordTrace (prefixWord ++ tailWord_5981185) baseStart_5981185 baseEnd_5981185 := by
    simpa [prefixWord, tailWord_5981185, baseEnd_5981185] using wordTrace_append hprefix tailTrace_5981185
  have hstable : (prefixWord ++ tailWord_5981185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981185).length < 2 ^ (prefixWord ++ tailWord_5981185).sum := by decide
  have hdescent : baseEnd_5981185 < baseStart_5981185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981195 : List Nat := [1, 1, 1, 1, 6, 3, 3, 1, 1, 5]
def baseStart_5981195 : Nat := 118140960795 + 5981195 * 2 ^ 59
def prefixEnd_5981195 : Nat := 4983230072969 + 3 ^ 40 * 5981195 * 2
def baseEnd_5981195 : Nat := 1023742641089610426918497

theorem tailTrace_5981195 : CollatzResearch.WordTrace tailWord_5981195 prefixEnd_5981195 1023742641089610426918497 := by
  unfold tailWord_5981195
  simp only [CollatzResearch.WordTrace]
  refine ⟨218152103566159496624801039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145434735710772997749867359 218152103566159496624801039)
  ·
    refine ⟨327228155349239244937201559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218152103566159496624801039 327228155349239244937201559)
    ·
      refine ⟨490842233023858867405802339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327228155349239244937201559 490842233023858867405802339)
      ·
        refine ⟨736263349535788301108703509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490842233023858867405802339 736263349535788301108703509)
        ·
          refine ⟨34512344509490076614470477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 736263349535788301108703509 34512344509490076614470477)
          ·
            refine ⟨12942129191058778730426429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34512344509490076614470477 12942129191058778730426429)
            ·
              refine ⟨4853298446647042023909911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12942129191058778730426429 4853298446647042023909911)
              ·
                refine ⟨7279947669970563035864867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4853298446647042023909911 7279947669970563035864867)
                ·
                  refine ⟨10919921504955844553797301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7279947669970563035864867 10919921504955844553797301)
                  ·
                    refine ⟨1023742641089610426918497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10919921504955844553797301 1023742641089610426918497)
                    ·
                      rfl

theorem cell23_5981195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 1, 1, 5].length) (baseStart_5981195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981195 prefixEnd_5981195 := by exact prefixLift 5981195
  have htrace : WordTrace (prefixWord ++ tailWord_5981195) baseStart_5981195 baseEnd_5981195 := by
    simpa [prefixWord, tailWord_5981195, baseEnd_5981195] using wordTrace_append hprefix tailTrace_5981195
  have hstable : (prefixWord ++ tailWord_5981195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981195).length < 2 ^ (prefixWord ++ tailWord_5981195).sum := by decide
  have hdescent : baseEnd_5981195 < baseStart_5981195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981228 : List Nat := [2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 4]
def baseStart_5981228 : Nat := 118140960795 + 5981228 * 2 ^ 59
def prefixEnd_5981228 : Nat := 4983230072969 + 3 ^ 40 * 5981228 * 2
def baseEnd_5981228 : Nat := 3071244868130429651642839

theorem tailTrace_5981228 : CollatzResearch.WordTrace tailWord_5981228 prefixEnd_5981228 3071244868130429651642839 := by
  unfold tailWord_5981228
  simp only [CollatzResearch.WordTrace]
  refine ⟨109076653587519971630376169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145435538116693295507168225 109076653587519971630376169)
  ·
    refine ⟨81807490190639978722782127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109076653587519971630376169 81807490190639978722782127)
    ·
      refine ⟨122711235285959968084173191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81807490190639978722782127 122711235285959968084173191)
      ·
        refine ⟨184066852928939952126259787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122711235285959968084173191 184066852928939952126259787)
        ·
          refine ⟨276100279393409928189389681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184066852928939952126259787 276100279393409928189389681)
          ·
            refine ⟨207075209545057446142042261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276100279393409928189389681 207075209545057446142042261)
            ·
              refine ⟨9706650447424567787908231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 207075209545057446142042261 9706650447424567787908231)
              ·
                refine ⟨14559975671136851681862347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9706650447424567787908231 14559975671136851681862347)
                ·
                  refine ⟨21839963506705277522793521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14559975671136851681862347 21839963506705277522793521)
                  ·
                    refine ⟨16379972630028958142095141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21839963506705277522793521 16379972630028958142095141)
                    ·
                      refine ⟨3071244868130429651642839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16379972630028958142095141 3071244868130429651642839)
                      ·
                        rfl

theorem cell23_5981228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 4].length) (baseStart_5981228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981228 prefixEnd_5981228 := by exact prefixLift 5981228
  have htrace : WordTrace (prefixWord ++ tailWord_5981228) baseStart_5981228 baseEnd_5981228 := by
    simpa [prefixWord, tailWord_5981228, baseEnd_5981228] using wordTrace_append hprefix tailTrace_5981228
  have hstable : (prefixWord ++ tailWord_5981228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981228).length < 2 ^ (prefixWord ++ tailWord_5981228).sum := by decide
  have hdescent : baseEnd_5981228 < baseStart_5981228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981248 : List Nat := [2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 3]
def baseStart_5981248 : Nat := 118140960795 + 5981248 * 2 ^ 59
def prefixEnd_5981248 : Nat := 4983230072969 + 3 ^ 40 * 5981248 * 2
def baseEnd_5981248 : Nat := 3071255137743519573392747

theorem tailTrace_5981248 : CollatzResearch.WordTrace tailWord_5981248 prefixEnd_5981248 3071255137743519573392747 := by
  unfold tailWord_5981248
  simp only [CollatzResearch.WordTrace]
  refine ⟨109077018317483743338240199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145436024423311657784320265 109077018317483743338240199)
  ·
    refine ⟨163615527476225615007360299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109077018317483743338240199 163615527476225615007360299)
    ·
      refine ⟨245423291214338422511040449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163615527476225615007360299 245423291214338422511040449)
      ·
        refine ⟨184067468410753816883280337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245423291214338422511040449 184067468410753816883280337)
        ·
          refine ⟨138050601308065362662460253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184067468410753816883280337 138050601308065362662460253)
          ·
            refine ⟨51768975490524510998422595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138050601308065362662460253 51768975490524510998422595)
            ·
              refine ⟨77653463235786766497633893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51768975490524510998422595 77653463235786766497633893)
              ·
                refine ⟨14560024356710018718306355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77653463235786766497633893 14560024356710018718306355)
                ·
                  refine ⟨21840036535065028077459533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14560024356710018718306355 21840036535065028077459533)
                  ·
                    refine ⟨8190013700649385529047325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21840036535065028077459533 8190013700649385529047325)
                    ·
                      refine ⟨3071255137743519573392747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8190013700649385529047325 3071255137743519573392747)
                      ·
                        rfl

theorem cell23_5981248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 3].length) (baseStart_5981248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981248 prefixEnd_5981248 := by exact prefixLift 5981248
  have htrace : WordTrace (prefixWord ++ tailWord_5981248) baseStart_5981248 baseEnd_5981248 := by
    simpa [prefixWord, tailWord_5981248, baseEnd_5981248] using wordTrace_append hprefix tailTrace_5981248
  have hstable : (prefixWord ++ tailWord_5981248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981248).length < 2 ^ (prefixWord ++ tailWord_5981248).sum := by decide
  have hdescent : baseEnd_5981248 < baseStart_5981248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981249 : List Nat := [1, 2, 5, 1, 3, 2, 2, 1, 1, 1, 4]
def baseStart_5981249 : Nat := 118140960795 + 5981249 * 2 ^ 59
def prefixEnd_5981249 : Nat := 4983230072969 + 3 ^ 40 * 5981249 * 2
def baseEnd_5981249 : Nat := 3071255651224174069480243

theorem tailTrace_5981249 : CollatzResearch.WordTrace tailWord_5981249 prefixEnd_5981249 3071255651224174069480243 := by
  unfold tailWord_5981249
  simp only [CollatzResearch.WordTrace]
  refine ⟨218154073107963863847266801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145436048738642575898177867 218154073107963863847266801)
  ·
    refine ⟨163615554830972897885450101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218154073107963863847266801 163615554830972897885450101)
    ·
      refine ⟨15338958265403709176760947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 163615554830972897885450101 15338958265403709176760947)
      ·
        refine ⟨23008437398105563765141421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15338958265403709176760947 23008437398105563765141421)
        ·
          refine ⟨8628164024289586411928033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23008437398105563765141421 8628164024289586411928033)
          ·
            refine ⟨6471123018217189808946025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8628164024289586411928033 6471123018217189808946025)
            ·
              refine ⟨4853342263662892356709519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6471123018217189808946025 4853342263662892356709519)
              ·
                refine ⟨7280013395494338535064279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4853342263662892356709519 7280013395494338535064279)
                ·
                  refine ⟨10920020093241507802596419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7280013395494338535064279 10920020093241507802596419)
                  ·
                    refine ⟨16380030139862261703894629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10920020093241507802596419 16380030139862261703894629)
                    ·
                      refine ⟨3071255651224174069480243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16380030139862261703894629 3071255651224174069480243)
                      ·
                        rfl

theorem cell23_5981249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_5981249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981249 prefixEnd_5981249 := by exact prefixLift 5981249
  have htrace : WordTrace (prefixWord ++ tailWord_5981249) baseStart_5981249 baseEnd_5981249 := by
    simpa [prefixWord, tailWord_5981249, baseEnd_5981249] using wordTrace_append hprefix tailTrace_5981249
  have hstable : (prefixWord ++ tailWord_5981249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981249).length < 2 ^ (prefixWord ++ tailWord_5981249).sum := by decide
  have hdescent : baseEnd_5981249 < baseStart_5981249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981282 : List Nat := [3, 3, 2, 2, 1, 1, 3, 1, 1, 3, 3]
def baseStart_5981282 : Nat := 118140960795 + 5981282 * 2 ^ 59
def prefixEnd_5981282 : Nat := 4983230072969 + 3 ^ 40 * 5981282 * 2
def baseEnd_5981282 : Nat := 3071272596085772440367591

theorem tailTrace_5981282 : CollatzResearch.WordTrace tailWord_5981282 prefixEnd_5981282 3071272596085772440367591 := by
  unfold tailWord_5981282
  simp only [CollatzResearch.WordTrace]
  refine ⟨54538819179211077620804525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145436851144562873655478733 54538819179211077620804525)
  ·
    refine ⟨20452057192204154107801697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54538819179211077620804525 20452057192204154107801697)
    ·
      refine ⟨15339042894153115580851273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20452057192204154107801697 15339042894153115580851273)
      ·
        refine ⟨11504282170614836685638455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15339042894153115580851273 11504282170614836685638455)
        ·
          refine ⟨17256423255922255028457683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11504282170614836685638455 17256423255922255028457683)
          ·
            refine ⟨25884634883883382542686525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17256423255922255028457683 25884634883883382542686525)
            ·
              refine ⟨9706738081456268453507447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25884634883883382542686525 9706738081456268453507447)
              ·
                refine ⟨14560107122184402680261171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9706738081456268453507447 14560107122184402680261171)
                ·
                  refine ⟨21840160683276604020391757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14560107122184402680261171 21840160683276604020391757)
                  ·
                    refine ⟨8190060256228726507646909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21840160683276604020391757 8190060256228726507646909)
                    ·
                      refine ⟨3071272596085772440367591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8190060256228726507646909 3071272596085772440367591)
                      ·
                        rfl

theorem cell23_5981282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_5981282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981282 prefixEnd_5981282 := by exact prefixLift 5981282
  have htrace : WordTrace (prefixWord ++ tailWord_5981282) baseStart_5981282 baseEnd_5981282 := by
    simpa [prefixWord, tailWord_5981282, baseEnd_5981282] using wordTrace_append hprefix tailTrace_5981282
  have hstable : (prefixWord ++ tailWord_5981282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981282).length < 2 ^ (prefixWord ++ tailWord_5981282).sum := by decide
  have hdescent : baseEnd_5981282 < baseStart_5981282 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981291 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 5]
def baseStart_5981291 : Nat := 118140960795 + 5981291 * 2 ^ 59
def prefixEnd_5981291 : Nat := 4983230072969 + 3 ^ 40 * 5981291 * 2
def baseEnd_5981291 : Nat := 3071277217411662905155049

theorem tailTrace_5981291 : CollatzResearch.WordTrace tailWord_5981291 prefixEnd_5981291 3071277217411662905155049 := by
  unfold tailWord_5981291
  simp only [CollatzResearch.WordTrace]
  refine ⟨218155604973811705020295727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145437069982541136680197151 218155604973811705020295727)
  ·
    refine ⟨327233407460717557530443591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218155604973811705020295727 327233407460717557530443591)
    ·
      refine ⟨490850111191076336295665387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327233407460717557530443591 490850111191076336295665387)
      ·
        refine ⟨736275166786614504443498081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490850111191076336295665387 736275166786614504443498081)
        ·
          refine ⟨552206375089960878332623561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 736275166786614504443498081 552206375089960878332623561)
          ·
            refine ⟨414154781317470658749467671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 552206375089960878332623561 414154781317470658749467671)
            ·
              refine ⟨621232171976205988124201507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414154781317470658749467671 621232171976205988124201507)
              ·
                refine ⟨931848257964308982186302261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 621232171976205988124201507 931848257964308982186302261)
                ·
                  refine ⟨87360774184153967079965837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 931848257964308982186302261 87360774184153967079965837)
                  ·
                    refine ⟨32760290319057737654987189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 87360774184153967079965837 32760290319057737654987189)
                    ·
                      refine ⟨3071277217411662905155049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32760290319057737654987189 3071277217411662905155049)
                      ·
                        rfl

theorem cell23_5981291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 5].length) (baseStart_5981291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981291 prefixEnd_5981291 := by exact prefixLift 5981291
  have htrace : WordTrace (prefixWord ++ tailWord_5981291) baseStart_5981291 baseEnd_5981291 := by
    simpa [prefixWord, tailWord_5981291, baseEnd_5981291] using wordTrace_append hprefix tailTrace_5981291
  have hstable : (prefixWord ++ tailWord_5981291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981291).length < 2 ^ (prefixWord ++ tailWord_5981291).sum := by decide
  have hdescent : baseEnd_5981291 < baseStart_5981291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981292 : List Nat := [2, 2, 1, 1, 3, 2, 4, 2, 1, 3, 2]
def baseStart_5981292 : Nat := 118140960795 + 5981292 * 2 ^ 59
def prefixEnd_5981292 : Nat := 4983230072969 + 3 ^ 40 * 5981292 * 2
def baseEnd_5981292 : Nat := 3071277730892317401242545

theorem tailTrace_5981292 : CollatzResearch.WordTrace tailWord_5981292 prefixEnd_5981292 3071277730892317401242545 := by
  unfold tailWord_5981292
  simp only [CollatzResearch.WordTrace]
  refine ⟨109077820723404041095541065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145437094297872054794054753 109077820723404041095541065)
  ·
    refine ⟨81808365542553030821655799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109077820723404041095541065 81808365542553030821655799)
    ·
      refine ⟨122712548313829546232483699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81808365542553030821655799 122712548313829546232483699)
      ·
        refine ⟨184068822470744319348725549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122712548313829546232483699 184068822470744319348725549)
        ·
          refine ⟨69025808426529119755772081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184068822470744319348725549 69025808426529119755772081)
          ·
            refine ⟨51769356319896839816829061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69025808426529119755772081 51769356319896839816829061)
            ·
              refine ⟨9706754309980657465655449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51769356319896839816829061 9706754309980657465655449)
              ·
                refine ⟨7280065732485493099241587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9706754309980657465655449 7280065732485493099241587)
                ·
                  refine ⟨10920098598728239648862381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7280065732485493099241587 10920098598728239648862381)
                  ·
                    refine ⟨4095036974523089868323393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10920098598728239648862381 4095036974523089868323393)
                    ·
                      refine ⟨3071277730892317401242545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4095036974523089868323393 3071277730892317401242545)
                      ·
                        rfl

theorem cell23_5981292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 3, 2].length) (baseStart_5981292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981292 prefixEnd_5981292 := by exact prefixLift 5981292
  have htrace : WordTrace (prefixWord ++ tailWord_5981292) baseStart_5981292 baseEnd_5981292 := by
    simpa [prefixWord, tailWord_5981292, baseEnd_5981292] using wordTrace_append hprefix tailTrace_5981292
  have hstable : (prefixWord ++ tailWord_5981292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981292).length < 2 ^ (prefixWord ++ tailWord_5981292).sum := by decide
  have hdescent : baseEnd_5981292 < baseStart_5981292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981308 : List Nat := [2, 2, 2, 1, 1, 3, 3, 1, 2, 1, 5]
def baseStart_5981308 : Nat := 118140960795 + 5981308 * 2 ^ 59
def prefixEnd_5981308 : Nat := 4983230072969 + 3 ^ 40 * 5981308 * 2
def baseEnd_5981308 : Nat := 3071285946582789338642471

theorem tailTrace_5981308 : CollatzResearch.WordTrace tailWord_5981308 prefixEnd_5981308 3071285946582789338642471 := by
  unfold tailWord_5981308
  simp only [CollatzResearch.WordTrace]
  refine ⟨109078112507375058461832289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145437483343166744615776385 109078112507375058461832289)
  ·
    refine ⟨81808584380531293846374217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109078112507375058461832289 81808584380531293846374217)
    ·
      refine ⟨61356438285398470384780663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81808584380531293846374217 61356438285398470384780663)
      ·
        refine ⟨92034657428097705577170995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61356438285398470384780663 92034657428097705577170995)
        ·
          refine ⟨138051986142146558365756493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92034657428097705577170995 138051986142146558365756493)
          ·
            refine ⟨51769494803304959387158685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138051986142146558365756493 51769494803304959387158685)
            ·
              refine ⟨19413560551239359770184507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51769494803304959387158685 19413560551239359770184507)
              ·
                refine ⟨29120340826859039655276761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19413560551239359770184507 29120340826859039655276761)
                ·
                  refine ⟨21840255620144279741457571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29120340826859039655276761 21840255620144279741457571)
                  ·
                    refine ⟨32760383430216419612186357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21840255620144279741457571 32760383430216419612186357)
                    ·
                      refine ⟨3071285946582789338642471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32760383430216419612186357 3071285946582789338642471)
                      ·
                        rfl

theorem cell23_5981308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_5981308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981308 prefixEnd_5981308 := by exact prefixLift 5981308
  have htrace : WordTrace (prefixWord ++ tailWord_5981308) baseStart_5981308 baseEnd_5981308 := by
    simpa [prefixWord, tailWord_5981308, baseEnd_5981308] using wordTrace_append hprefix tailTrace_5981308
  have hstable : (prefixWord ++ tailWord_5981308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981308).length < 2 ^ (prefixWord ++ tailWord_5981308).sum := by decide
  have hdescent : baseEnd_5981308 < baseStart_5981308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981322 : List Nat := [3, 1, 2, 3, 1, 1, 1, 3, 4, 2, 2]
def baseStart_5981322 : Nat := 118140960795 + 5981322 * 2 ^ 59
def prefixEnd_5981322 : Nat := 4983230072969 + 3 ^ 40 * 5981322 * 2
def baseEnd_5981322 : Nat := 3071293135311952283867407

theorem tailTrace_5981322 : CollatzResearch.WordTrace tailWord_5981322 prefixEnd_5981322 3071293135311952283867407 := by
  unfold tailWord_5981322
  simp only [CollatzResearch.WordTrace]
  refine ⟨54539183909174849328668555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145437823757799598209782813 54539183909174849328668555)
  ·
    refine ⟨81808775863762273993002833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54539183909174849328668555 81808775863762273993002833)
    ·
      refine ⟨61356581897821705494752125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81808775863762273993002833 61356581897821705494752125)
      ·
        refine ⟨23008718211683139560532047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61356581897821705494752125 23008718211683139560532047)
        ·
          refine ⟨34513077317524709340798071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23008718211683139560532047 34513077317524709340798071)
          ·
            refine ⟨51769615976287064011197107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34513077317524709340798071 51769615976287064011197107)
            ·
              refine ⟨77654423964430596016795661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51769615976287064011197107 77654423964430596016795661)
              ·
                refine ⟨29120408986661473506298373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77654423964430596016795661 29120408986661473506298373)
                ·
                  refine ⟨5460076684999026282430945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29120408986661473506298373 5460076684999026282430945)
                  ·
                    refine ⟨4095057513749269711823209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5460076684999026282430945 4095057513749269711823209)
                    ·
                      refine ⟨3071293135311952283867407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4095057513749269711823209 3071293135311952283867407)
                      ·
                        rfl

theorem cell23_5981322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_5981322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981322 prefixEnd_5981322 := by exact prefixLift 5981322
  have htrace : WordTrace (prefixWord ++ tailWord_5981322) baseStart_5981322 baseEnd_5981322 := by
    simpa [prefixWord, tailWord_5981322, baseEnd_5981322] using wordTrace_append hprefix tailTrace_5981322
  have hstable : (prefixWord ++ tailWord_5981322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981322).length < 2 ^ (prefixWord ++ tailWord_5981322).sum := by decide
  have hdescent : baseEnd_5981322 < baseStart_5981322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981395 : List Nat := [1, 1, 1, 2, 1, 1, 1, 7, 2, 4, 2]
def baseStart_5981395 : Nat := 118140960795 + 5981395 * 2 ^ 59
def prefixEnd_5981395 : Nat := 4983230072969 + 3 ^ 40 * 5981395 * 2
def baseEnd_5981395 : Nat := 3071330619399730498254571

theorem tailTrace_5981395 : CollatzResearch.WordTrace tailWord_5981395 prefixEnd_5981395 3071330619399730498254571 := by
  unfold tailWord_5981395
  simp only [CollatzResearch.WordTrace]
  refine ⟨218159398165434930782081639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145439598776956620521387759 218159398165434930782081639)
  ·
    refine ⟨327239097248152396173122459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218159398165434930782081639 327239097248152396173122459)
    ·
      refine ⟨490858645872228594259683689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327239097248152396173122459 490858645872228594259683689)
      ·
        refine ⟨368143984404171445694762767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 490858645872228594259683689 368143984404171445694762767)
        ·
          refine ⟨552215976606257168542144151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368143984404171445694762767 552215976606257168542144151)
          ·
            refine ⟨828323964909385752813216227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552215976606257168542144151 828323964909385752813216227)
            ·
              refine ⟨1242485947364078629219824341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 828323964909385752813216227 1242485947364078629219824341)
              ·
                refine ⟨29120764391345592872339633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1242485947364078629219824341 29120764391345592872339633)
                ·
                  refine ⟨21840573293509194654254725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29120764391345592872339633 21840573293509194654254725)
                  ·
                    refine ⟨4095107492532973997672761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21840573293509194654254725 4095107492532973997672761)
                    ·
                      refine ⟨3071330619399730498254571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4095107492532973997672761 3071330619399730498254571)
                      ·
                        rfl

theorem cell23_5981395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 4, 2].length) (baseStart_5981395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981395 prefixEnd_5981395 := by exact prefixLift 5981395
  have htrace : WordTrace (prefixWord ++ tailWord_5981395) baseStart_5981395 baseEnd_5981395 := by
    simpa [prefixWord, tailWord_5981395, baseEnd_5981395] using wordTrace_append hprefix tailTrace_5981395
  have hstable : (prefixWord ++ tailWord_5981395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981395).length < 2 ^ (prefixWord ++ tailWord_5981395).sum := by decide
  have hdescent : baseEnd_5981395 < baseStart_5981395 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981452 : List Nat := [2, 2, 1, 2, 2, 4, 3, 1, 6]
def baseStart_5981452 : Nat := 118140960795 + 5981452 * 2 ^ 59
def prefixEnd_5981452 : Nat := 4983230072969 + 3 ^ 40 * 5981452 * 2
def baseEnd_5981452 : Nat := 341262209755226308360201

theorem tailTrace_5981452 : CollatzResearch.WordTrace tailWord_5981452 prefixEnd_5981452 341262209755226308360201 := by
  unfold tailWord_5981452
  simp only [CollatzResearch.WordTrace]
  refine ⟨109080738563114214758453305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145440984750818953011271073 109080738563114214758453305)
  ·
    refine ⟨81810553922335661068839979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109080738563114214758453305 81810553922335661068839979)
    ·
      refine ⟨122715830883503491603259969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81810553922335661068839979 122715830883503491603259969)
      ·
        refine ⟨92036873162627618702444977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122715830883503491603259969 92036873162627618702444977)
        ·
          refine ⟨69027654871970714026833733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92036873162627618702444977 69027654871970714026833733)
          ·
            refine ⟨12942685288494508880031325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69027654871970714026833733 12942685288494508880031325)
            ·
              refine ⟨4853506983185440830011747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12942685288494508880031325 4853506983185440830011747)
              ·
                refine ⟨7280260474778161245017621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4853506983185440830011747 7280260474778161245017621)
                ·
                  refine ⟨341262209755226308360201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7280260474778161245017621 341262209755226308360201)
                  ·
                    rfl

theorem cell23_5981452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 1, 6].length) (baseStart_5981452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981452 prefixEnd_5981452 := by exact prefixLift 5981452
  have htrace : WordTrace (prefixWord ++ tailWord_5981452) baseStart_5981452 baseEnd_5981452 := by
    simpa [prefixWord, tailWord_5981452, baseEnd_5981452] using wordTrace_append hprefix tailTrace_5981452
  have hstable : (prefixWord ++ tailWord_5981452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981452).length < 2 ^ (prefixWord ++ tailWord_5981452).sum := by decide
  have hdescent : baseEnd_5981452 < baseStart_5981452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981489 : List Nat := [1, 2, 2, 3, 3, 2, 1, 2, 2, 3, 2]
def baseStart_5981489 : Nat := 118140960795 + 5981489 * 2 ^ 59
def prefixEnd_5981489 : Nat := 4983230072969 + 3 ^ 40 * 5981489 * 2
def baseEnd_5981489 : Nat := 3071378886581253130479139

theorem tailTrace_5981489 : CollatzResearch.WordTrace tailWord_5981489 prefixEnd_5981489 3071378886581253130479139 := by
  unfold tailWord_5981489
  simp only [CollatzResearch.WordTrace]
  refine ⟨218162826627094384836003521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145441884418062923224002347 218162826627094384836003521)
  ·
    refine ⟨163622119970320788627002641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218162826627094384836003521 163622119970320788627002641)
    ·
      refine ⟨122716589977740591470251981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163622119970320788627002641 122716589977740591470251981)
      ·
        refine ⟨46018721241652721801344493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122716589977740591470251981 46018721241652721801344493)
        ·
          refine ⟨17257020465619770675504185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46018721241652721801344493 17257020465619770675504185)
          ·
            refine ⟨12942765349214828006628139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17257020465619770675504185 12942765349214828006628139)
            ·
              refine ⟨19414148023822242009942209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12942765349214828006628139 19414148023822242009942209)
              ·
                refine ⟨14560611017866681507456657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19414148023822242009942209 14560611017866681507456657)
                ·
                  refine ⟨10920458263400011130592493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14560611017866681507456657 10920458263400011130592493)
                  ·
                    refine ⟨4095171848775004173972185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10920458263400011130592493 4095171848775004173972185)
                    ·
                      refine ⟨3071378886581253130479139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4095171848775004173972185 3071378886581253130479139)
                      ·
                        rfl

theorem cell23_5981489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 3, 2].length) (baseStart_5981489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981489 prefixEnd_5981489 := by exact prefixLift 5981489
  have htrace : WordTrace (prefixWord ++ tailWord_5981489) baseStart_5981489 baseEnd_5981489 := by
    simpa [prefixWord, tailWord_5981489, baseEnd_5981489] using wordTrace_append hprefix tailTrace_5981489
  have hstable : (prefixWord ++ tailWord_5981489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981489).length < 2 ^ (prefixWord ++ tailWord_5981489).sum := by decide
  have hdescent : baseEnd_5981489 < baseStart_5981489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981502 : List Nat := [4, 2, 1, 2, 1, 1, 2, 2, 3, 1, 4]
def baseStart_5981502 : Nat := 118140960795 + 5981502 * 2 ^ 59
def prefixEnd_5981502 : Nat := 4983230072969 + 3 ^ 40 * 5981502 * 2
def baseEnd_5981502 : Nat := 3071385561829761579616579

theorem tailTrace_5981502 : CollatzResearch.WordTrace tailWord_5981502 prefixEnd_5981502 3071385561829761579616579 := by
  unfold tailWord_5981502
  simp only [CollatzResearch.WordTrace]
  refine ⟨27270412597005911007028345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145442200517364858704151173 27270412597005911007028345)
  ·
    refine ⟨20452809447754433255271259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27270412597005911007028345 20452809447754433255271259)
    ·
      refine ⟨30679214171631649882906889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20452809447754433255271259 30679214171631649882906889)
      ·
        refine ⟨23009410628723737412180167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30679214171631649882906889 23009410628723737412180167)
        ·
          refine ⟨34514115943085606118270251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23009410628723737412180167 34514115943085606118270251)
          ·
            refine ⟨51771173914628409177405377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34514115943085606118270251 51771173914628409177405377)
            ·
              refine ⟨38828380435971306883054033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51771173914628409177405377 38828380435971306883054033)
              ·
                refine ⟨29121285326978480162290525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38828380435971306883054033 29121285326978480162290525)
                ·
                  refine ⟨10920481997616930060858947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29121285326978480162290525 10920481997616930060858947)
                  ·
                    refine ⟨16380722996425395091288421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10920481997616930060858947 16380722996425395091288421)
                    ·
                      refine ⟨3071385561829761579616579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16380722996425395091288421 3071385561829761579616579)
                      ·
                        rfl

theorem cell23_5981502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_5981502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981502 prefixEnd_5981502 := by exact prefixLift 5981502
  have htrace : WordTrace (prefixWord ++ tailWord_5981502) baseStart_5981502 baseEnd_5981502 := by
    simpa [prefixWord, tailWord_5981502, baseEnd_5981502] using wordTrace_append hprefix tailTrace_5981502
  have hstable : (prefixWord ++ tailWord_5981502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981502).length < 2 ^ (prefixWord ++ tailWord_5981502).sum := by decide
  have hdescent : baseEnd_5981502 < baseStart_5981502 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981525 : List Nat := [1, 3, 2, 2, 3, 1, 2, 9]
def baseStart_5981525 : Nat := 118140960795 + 5981525 * 2 ^ 59
def prefixEnd_5981525 : Nat := 4983230072969 + 3 ^ 40 * 5981525 * 2
def baseEnd_5981525 : Nat := 113755458217956110726999

theorem tailTrace_5981525 : CollatzResearch.WordTrace tailWord_5981525 prefixEnd_5981525 113755458217956110726999 := by
  unfold tailWord_5981525
  simp only [CollatzResearch.WordTrace]
  refine ⟨218164139654963962984314029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145442759769975975322876019 218164139654963962984314029)
  ·
    refine ⟨81811552370611486119117761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218164139654963962984314029 81811552370611486119117761)
    ·
      refine ⟨61358664277958614589338321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81811552370611486119117761 61358664277958614589338321)
      ·
        refine ⟨46018998208468960942003741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61358664277958614589338321 46018998208468960942003741)
        ·
          refine ⟨17257124328175860353251403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46018998208468960942003741 17257124328175860353251403)
          ·
            refine ⟨25885686492263790529877105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17257124328175860353251403 25885686492263790529877105)
            ·
              refine ⟨19414264869197842897407829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25885686492263790529877105 19414264869197842897407829)
              ·
                refine ⟨113755458217956110726999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19414264869197842897407829 113755458217956110726999)
                ·
                  rfl

theorem cell23_5981525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 9].length) (baseStart_5981525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981525 prefixEnd_5981525 := by exact prefixLift 5981525
  have htrace : WordTrace (prefixWord ++ tailWord_5981525) baseStart_5981525 baseEnd_5981525 := by
    simpa [prefixWord, tailWord_5981525, baseEnd_5981525] using wordTrace_append hprefix tailTrace_5981525
  have hstable : (prefixWord ++ tailWord_5981525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981525).length < 2 ^ (prefixWord ++ tailWord_5981525).sum := by decide
  have hdescent : baseEnd_5981525 < baseStart_5981525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981546 : List Nat := [3, 1, 3, 3, 2, 1, 2, 2, 2, 4]
def baseStart_5981546 : Nat := 118140960795 + 5981546 * 2 ^ 59
def prefixEnd_5981546 : Nat := 4983230072969 + 3 ^ 40 * 5981546 * 2
def baseEnd_5981546 : Nat := 1023802718326186469155459

theorem tailTrace_5981546 : CollatzResearch.WordTrace tailWord_5981546 prefixEnd_5981546 1023802718326186469155459 := by
  unfold tailWord_5981546
  simp only [CollatzResearch.WordTrace]
  refine ⟨54541226396971970892707123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145443270391925255713885661 54541226396971970892707123)
  ·
    refine ⟨81811839595457956339060685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54541226396971970892707123 81811839595457956339060685)
    ·
      refine ⟨30679439848296733627147757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81811839595457956339060685 30679439848296733627147757)
      ·
        refine ⟨11504789943111275110180409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30679439848296733627147757 11504789943111275110180409)
        ·
          refine ⟨8628592457333456332635307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11504789943111275110180409 8628592457333456332635307)
          ·
            refine ⟨12942888686000184498952961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8628592457333456332635307 12942888686000184498952961)
            ·
              refine ⟨9707166514500138374214721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12942888686000184498952961 9707166514500138374214721)
              ·
                refine ⟨7280374885875103780661041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9707166514500138374214721 7280374885875103780661041)
                ·
                  refine ⟨5460281164406327835495781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7280374885875103780661041 5460281164406327835495781)
                  ·
                    refine ⟨1023802718326186469155459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5460281164406327835495781 1023802718326186469155459)
                    ·
                      rfl

theorem cell23_5981546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_5981546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981546 prefixEnd_5981546 := by exact prefixLift 5981546
  have htrace : WordTrace (prefixWord ++ tailWord_5981546) baseStart_5981546 baseEnd_5981546 := by
    simpa [prefixWord, tailWord_5981546, baseEnd_5981546] using wordTrace_append hprefix tailTrace_5981546
  have hstable : (prefixWord ++ tailWord_5981546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981546).length < 2 ^ (prefixWord ++ tailWord_5981546).sum := by decide
  have hdescent : baseEnd_5981546 < baseStart_5981546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981553 : List Nat := [1, 2, 2, 2, 1, 2, 6, 2, 1, 2, 2]
def baseStart_5981553 : Nat := 118140960795 + 5981553 * 2 ^ 59
def prefixEnd_5981553 : Nat := 4983230072969 + 3 ^ 40 * 5981553 * 2
def baseEnd_5981553 : Nat := 3071411749343140880078845

theorem tailTrace_5981553 : CollatzResearch.WordTrace tailWord_5981553 prefixEnd_5981553 3071411749343140880078845 := by
  unfold tailWord_5981553
  simp only [CollatzResearch.WordTrace]
  refine ⟨218165160898862523766333313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145443440599241682510888875 218165160898862523766333313)
  ·
    refine ⟨163623870674146892824749985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218165160898862523766333313 163623870674146892824749985)
    ·
      refine ⟨122717903005610169618562489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163623870674146892824749985 122717903005610169618562489)
      ·
        refine ⟨92038427254207627213921867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122717903005610169618562489 92038427254207627213921867)
        ·
          refine ⟨138057640881311440820882801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92038427254207627213921867 138057640881311440820882801)
          ·
            refine ⟨103543230660983580615662101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138057640881311440820882801 103543230660983580615662101)
            ·
              refine ⟨4853588937233605341359161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 103543230660983580615662101 4853588937233605341359161)
              ·
                refine ⟨3640191702925204006019371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4853588937233605341359161 3640191702925204006019371)
                ·
                  refine ⟨5460287554387806009029057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3640191702925204006019371 5460287554387806009029057)
                  ·
                    refine ⟨4095215665790854506771793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5460287554387806009029057 4095215665790854506771793)
                    ·
                      refine ⟨3071411749343140880078845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4095215665790854506771793 3071411749343140880078845)
                      ·
                        rfl

theorem cell23_5981553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 2, 1, 2, 2].length) (baseStart_5981553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981553 prefixEnd_5981553 := by exact prefixLift 5981553
  have htrace : WordTrace (prefixWord ++ tailWord_5981553) baseStart_5981553 baseEnd_5981553 := by
    simpa [prefixWord, tailWord_5981553, baseEnd_5981553] using wordTrace_append hprefix tailTrace_5981553
  have hstable : (prefixWord ++ tailWord_5981553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981553).length < 2 ^ (prefixWord ++ tailWord_5981553).sum := by decide
  have hdescent : baseEnd_5981553 < baseStart_5981553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981579 : List Nat := [1, 1, 1, 1, 4, 3, 2, 4, 1, 3, 2]
def baseStart_5981579 : Nat := 118140960795 + 5981579 * 2 ^ 59
def prefixEnd_5981579 : Nat := 4983230072969 + 3 ^ 40 * 5981579 * 2
def baseEnd_5981579 : Nat := 3071425099840157778353725

theorem tailTrace_5981579 : CollatzResearch.WordTrace tailWord_5981579 prefixEnd_5981579 3071425099840157778353725 := by
  unfold tailWord_5981579
  simp only [CollatzResearch.WordTrace]
  refine ⟨218166109196768330206779791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145444072797845553471186527 218166109196768330206779791)
  ·
    refine ⟨327249163795152495310169687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218166109196768330206779791 327249163795152495310169687)
    ·
      refine ⟨490873745692728742965254531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327249163795152495310169687 490873745692728742965254531)
      ·
        refine ⟨736310618539093114447881797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490873745692728742965254531 736310618539093114447881797)
        ·
          refine ⟨138058240976079958958977837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 736310618539093114447881797 138058240976079958958977837)
          ·
            refine ⟨51771840366029984609616689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138058240976079958958977837 51771840366029984609616689)
            ·
              refine ⟨38828880274522488457212517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51771840366029984609616689 38828880274522488457212517)
              ·
                refine ⟨7280415051472966585727347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38828880274522488457212517 7280415051472966585727347)
                ·
                  refine ⟨10920622577209449878591021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7280415051472966585727347 10920622577209449878591021)
                  ·
                    refine ⟨4095233466453543704471633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10920622577209449878591021 4095233466453543704471633)
                    ·
                      refine ⟨3071425099840157778353725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4095233466453543704471633 3071425099840157778353725)
                      ·
                        rfl

theorem cell23_5981579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 3, 2].length) (baseStart_5981579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981579 prefixEnd_5981579 := by exact prefixLift 5981579
  have htrace : WordTrace (prefixWord ++ tailWord_5981579) baseStart_5981579 baseEnd_5981579 := by
    simpa [prefixWord, tailWord_5981579, baseEnd_5981579] using wordTrace_append hprefix tailTrace_5981579
  have hstable : (prefixWord ++ tailWord_5981579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981579).length < 2 ^ (prefixWord ++ tailWord_5981579).sum := by decide
  have hdescent : baseEnd_5981579 < baseStart_5981579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981602 : List Nat := [3, 3, 1, 2, 1, 2, 1, 2, 2, 6]
def baseStart_5981602 : Nat := 118140960795 + 5981602 * 2 ^ 59
def prefixEnd_5981602 : Nat := 4983230072969 + 3 ^ 40 * 5981602 * 2
def baseEnd_5981602 : Nat := 1023812303298403729455373

theorem tailTrace_5981602 : CollatzResearch.WordTrace tailWord_5981602 prefixEnd_5981602 1023812303298403729455373 := by
  unfold tailWord_5981602
  simp only [CollatzResearch.WordTrace]
  refine ⟨54541737018921251283716765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145444632050456670089911373 54541737018921251283716765)
  ·
    refine ⟨20453151382095469231393787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54541737018921251283716765 20453151382095469231393787)
    ·
      refine ⟨30679727073143203847090681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20453151382095469231393787 30679727073143203847090681)
      ·
        refine ⟨23009795304857402885318011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30679727073143203847090681 23009795304857402885318011)
        ·
          refine ⟨34514692957286104327977017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23009795304857402885318011 34514692957286104327977017)
          ·
            refine ⟨25886019717964578245982763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34514692957286104327977017 25886019717964578245982763)
            ·
              refine ⟨38829029576946867368974145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25886019717964578245982763 38829029576946867368974145)
              ·
                refine ⟨29121772182710150526730609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38829029576946867368974145 29121772182710150526730609)
                ·
                  refine ⟨21841329137032612895047957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29121772182710150526730609 21841329137032612895047957)
                  ·
                    refine ⟨1023812303298403729455373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21841329137032612895047957 1023812303298403729455373)
                    ·
                      rfl

theorem cell23_5981602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_5981602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981602 prefixEnd_5981602 := by exact prefixLift 5981602
  have htrace : WordTrace (prefixWord ++ tailWord_5981602) baseStart_5981602 baseEnd_5981602 := by
    simpa [prefixWord, tailWord_5981602, baseEnd_5981602] using wordTrace_append hprefix tailTrace_5981602
  have hstable : (prefixWord ++ tailWord_5981602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981602).length < 2 ^ (prefixWord ++ tailWord_5981602).sum := by decide
  have hdescent : baseEnd_5981602 < baseStart_5981602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981655 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 7]
def baseStart_5981655 : Nat := 118140960795 + 5981655 * 2 ^ 59
def prefixEnd_5981655 : Nat := 4983230072969 + 3 ^ 40 * 5981655 * 2
def baseEnd_5981655 : Nat := 3071464124369899481003375

theorem tailTrace_5981655 : CollatzResearch.WordTrace tailWord_5981655 prefixEnd_5981655 3071464124369899481003375 := by
  unfold tailWord_5981655
  simp only [CollatzResearch.WordTrace]
  refine ⟨218168881144492995186546419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145445920762995330124364279 218168881144492995186546419)
  ·
    refine ⟨327253321716739492779819629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218168881144492995186546419 327253321716739492779819629)
    ·
      refine ⟨122719995643777309792432361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 327253321716739492779819629 122719995643777309792432361)
      ·
        refine ⟨92039996732832982344324271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122719995643777309792432361 92039996732832982344324271)
        ·
          refine ⟨138059995099249473516486407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92039996732832982344324271 138059995099249473516486407)
          ·
            refine ⟨207089992648874210274729611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138059995099249473516486407 207089992648874210274729611)
            ·
              refine ⟨310634988973311315412094417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207089992648874210274729611 310634988973311315412094417)
              ·
                refine ⟨232976241729983486559070813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 310634988973311315412094417 232976241729983486559070813)
                ·
                  refine ⟨87366090648743807459651555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 232976241729983486559070813 87366090648743807459651555)
                  ·
                    refine ⟨131049135973115711189477333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 87366090648743807459651555 131049135973115711189477333)
                    ·
                      refine ⟨3071464124369899481003375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 131049135973115711189477333 3071464124369899481003375)
                      ·
                        rfl

theorem cell23_5981655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_5981655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981655 prefixEnd_5981655 := by exact prefixLift 5981655
  have htrace : WordTrace (prefixWord ++ tailWord_5981655) baseStart_5981655 baseEnd_5981655 := by
    simpa [prefixWord, tailWord_5981655, baseEnd_5981655] using wordTrace_append hprefix tailTrace_5981655
  have hstable : (prefixWord ++ tailWord_5981655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981655).length < 2 ^ (prefixWord ++ tailWord_5981655).sum := by decide
  have hdescent : baseEnd_5981655 < baseStart_5981655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981672 : List Nat := [2, 1, 4, 1, 1, 2, 3, 1, 1, 2, 5]
def baseStart_5981672 : Nat := 118140960795 + 5981672 * 2 ^ 59
def prefixEnd_5981672 : Nat := 4983230072969 + 3 ^ 40 * 5981672 * 2
def baseEnd_5981672 : Nat := 3071472853541025914490797

theorem tailTrace_5981672 : CollatzResearch.WordTrace tailWord_5981672 prefixEnd_5981672 3071472853541025914490797 := by
  unfold tailWord_5981672
  simp only [CollatzResearch.WordTrace]
  refine ⟨109084750592715703544957635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145446334123620938059943513 109084750592715703544957635)
  ·
    refine ⟨163627125889073555317436453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109084750592715703544957635 163627125889073555317436453)
    ·
      refine ⟨30680086104201291622019335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163627125889073555317436453 30680086104201291622019335)
      ·
        refine ⟨46020129156301937433029003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30680086104201291622019335 46020129156301937433029003)
        ·
          refine ⟨69030193734452906149543505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46020129156301937433029003 69030193734452906149543505)
          ·
            refine ⟨51772645300839679612157629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69030193734452906149543505 51772645300839679612157629)
            ·
              refine ⟨19414741987814879854559111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51772645300839679612157629 19414741987814879854559111)
              ·
                refine ⟨29122112981722319781838667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19414741987814879854559111 29122112981722319781838667)
                ·
                  refine ⟨43683169472583479672758001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29122112981722319781838667 43683169472583479672758001)
                  ·
                    refine ⟨32762377104437609754568501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43683169472583479672758001 32762377104437609754568501)
                    ·
                      refine ⟨3071472853541025914490797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32762377104437609754568501 3071472853541025914490797)
                      ·
                        rfl

theorem cell23_5981672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_5981672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981672 prefixEnd_5981672 := by exact prefixLift 5981672
  have htrace : WordTrace (prefixWord ++ tailWord_5981672) baseStart_5981672 baseEnd_5981672 := by
    simpa [prefixWord, tailWord_5981672, baseEnd_5981672] using wordTrace_append hprefix tailTrace_5981672
  have hstable : (prefixWord ++ tailWord_5981672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981672).length < 2 ^ (prefixWord ++ tailWord_5981672).sum := by decide
  have hdescent : baseEnd_5981672 < baseStart_5981672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981675 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 2, 8]
def baseStart_5981675 : Nat := 118140960795 + 5981675 * 2 ^ 59
def prefixEnd_5981675 : Nat := 4983230072969 + 3 ^ 40 * 5981675 * 2
def baseEnd_5981675 : Nat := 1023824797994329800917761

theorem tailTrace_5981675 : CollatzResearch.WordTrace tailWord_5981675 prefixEnd_5981675 1023824797994329800917761 := by
  unfold tailWord_5981675
  simp only [CollatzResearch.WordTrace]
  refine ⟨218169610604420538602274479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145446407069613692401516319 218169610604420538602274479)
  ·
    refine ⟨327254415906630807903411719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218169610604420538602274479 327254415906630807903411719)
    ·
      refine ⟨490881623859946211855117579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327254415906630807903411719 490881623859946211855117579)
      ·
        refine ⟨736322435789919317782676369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490881623859946211855117579 736322435789919317782676369)
        ·
          refine ⟨552241826842439488337007277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 736322435789919317782676369 552241826842439488337007277)
          ·
            refine ⟨207090685065914808126377729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 552241826842439488337007277 207090685065914808126377729)
            ·
              refine ⟨155318013799436106094783297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207090685065914808126377729 155318013799436106094783297)
              ·
                refine ⟨116488510349577079571087473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155318013799436106094783297 116488510349577079571087473)
                ·
                  refine ⟨87366382762182809678315605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116488510349577079571087473 87366382762182809678315605)
                  ·
                    refine ⟨1023824797994329800917761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 87366382762182809678315605 1023824797994329800917761)
                    ·
                      rfl

theorem cell23_5981675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 8].length) (baseStart_5981675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981675 prefixEnd_5981675 := by exact prefixLift 5981675
  have htrace : WordTrace (prefixWord ++ tailWord_5981675) baseStart_5981675 baseEnd_5981675 := by
    simpa [prefixWord, tailWord_5981675, baseEnd_5981675] using wordTrace_append hprefix tailTrace_5981675
  have hstable : (prefixWord ++ tailWord_5981675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981675).length < 2 ^ (prefixWord ++ tailWord_5981675).sum := by decide
  have hdescent : baseEnd_5981675 < baseStart_5981675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981677 : List Nat := [1, 5, 1, 3, 2, 2, 2, 1, 2, 2, 2]
def baseStart_5981677 : Nat := 118140960795 + 5981677 * 2 ^ 59
def prefixEnd_5981677 : Nat := 4983230072969 + 3 ^ 40 * 5981677 * 2
def baseEnd_5981677 : Nat := 3071475420944298394928275

theorem tailTrace_5981677 : CollatzResearch.WordTrace tailWord_5981677 prefixEnd_5981677 3071475420944298394928275 := by
  unfold tailWord_5981677
  simp only [CollatzResearch.WordTrace]
  refine ⟨218169683550413292943847285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145446455700275528629231523 218169683550413292943847285)
  ·
    refine ⟨20453407832851246213485683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 218169683550413292943847285 20453407832851246213485683)
    ·
      refine ⟨30680111749276869320228525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20453407832851246213485683 30680111749276869320228525)
      ·
        refine ⟨11505041905978825995085697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30680111749276869320228525 11505041905978825995085697)
        ·
          refine ⟨8628781429484119496314273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11505041905978825995085697 8628781429484119496314273)
          ·
            refine ⟨6471586072113089622235705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8628781429484119496314273 6471586072113089622235705)
            ·
              refine ⟨4853689554084817216676779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6471586072113089622235705 4853689554084817216676779)
              ·
                refine ⟨7280534331127225825015169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4853689554084817216676779 7280534331127225825015169)
                ·
                  refine ⟨5460400748345419368761377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7280534331127225825015169 5460400748345419368761377)
                  ·
                    refine ⟨4095300561259064526571033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5460400748345419368761377 4095300561259064526571033)
                    ·
                      refine ⟨3071475420944298394928275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4095300561259064526571033 3071475420944298394928275)
                      ·
                        rfl

theorem cell23_5981677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_5981677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981677 prefixEnd_5981677 := by exact prefixLift 5981677
  have htrace : WordTrace (prefixWord ++ tailWord_5981677) baseStart_5981677 baseEnd_5981677 := by
    simpa [prefixWord, tailWord_5981677, baseEnd_5981677] using wordTrace_append hprefix tailTrace_5981677
  have hstable : (prefixWord ++ tailWord_5981677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981677).length < 2 ^ (prefixWord ++ tailWord_5981677).sum := by decide
  have hdescent : baseEnd_5981677 < baseStart_5981677 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981750 : List Nat := [5, 1, 2, 1, 4, 1, 1, 1, 2, 1, 4]
def baseStart_5981750 : Nat := 118140960795 + 5981750 * 2 ^ 59
def prefixEnd_5981750 : Nat := 4983230072969 + 3 ^ 40 * 5981750 * 2
def baseEnd_5981750 : Nat := 3071512905032076609315439

theorem tailTrace_5981750 : CollatzResearch.WordTrace tailWord_5981750 prefixEnd_5981750 3071512905032076609315439 := by
  unfold tailWord_5981750
  simp only [CollatzResearch.WordTrace]
  refine ⟨13635771629946801650703419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145448230719432550940836469 13635771629946801650703419)
  ·
    refine ⟨20453657444920202476055129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13635771629946801650703419 20453657444920202476055129)
    ·
      refine ⟨15340243083690151857041347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20453657444920202476055129 15340243083690151857041347)
      ·
        refine ⟨23010364625535227785562021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15340243083690151857041347 23010364625535227785562021)
        ·
          refine ⟨4314443367287855209792879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23010364625535227785562021 4314443367287855209792879)
          ·
            refine ⟨6471665050931782814689319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4314443367287855209792879 6471665050931782814689319)
            ·
              refine ⟨9707497576397674222033979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6471665050931782814689319 9707497576397674222033979)
              ·
                refine ⟨14561246364596511333050969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9707497576397674222033979 14561246364596511333050969)
                ·
                  refine ⟨10920934773447383499788227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14561246364596511333050969 10920934773447383499788227)
                  ·
                    refine ⟨16381402160171075249682341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10920934773447383499788227 16381402160171075249682341)
                    ·
                      refine ⟨3071512905032076609315439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16381402160171075249682341 3071512905032076609315439)
                      ·
                        rfl

theorem cell23_5981750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_5981750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981750 prefixEnd_5981750 := by exact prefixLift 5981750
  have htrace : WordTrace (prefixWord ++ tailWord_5981750) baseStart_5981750 baseEnd_5981750 := by
    simpa [prefixWord, tailWord_5981750, baseEnd_5981750] using wordTrace_append hprefix tailTrace_5981750
  have hstable : (prefixWord ++ tailWord_5981750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981750).length < 2 ^ (prefixWord ++ tailWord_5981750).sum := by decide
  have hdescent : baseEnd_5981750 < baseStart_5981750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981773 : List Nat := [1, 6, 1, 1, 3, 2, 1, 2, 6]
def baseStart_5981773 : Nat := 118140960795 + 5981773 * 2 ^ 59
def prefixEnd_5981773 : Nat := 4983230072969 + 3 ^ 40 * 5981773 * 2
def baseEnd_5981773 : Nat := 341280523898570002147537

theorem tailTrace_5981773 : CollatzResearch.WordTrace tailWord_5981773 prefixEnd_5981773 341280523898570002147537 := by
  unfold tailWord_5981773
  simp only [CollatzResearch.WordTrace]
  refine ⟨218173184958065501339341973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145448789972043667559561315 218173184958065501339341973)
  ·
    refine ⟨10226868044909320375281655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 218173184958065501339341973 10226868044909320375281655)
    ·
      refine ⟨15340302067363980562922483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10226868044909320375281655 15340302067363980562922483)
      ·
        refine ⟨23010453101045970844383725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15340302067363980562922483 23010453101045970844383725)
        ·
          refine ⟨8628919912892239066643897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23010453101045970844383725 8628919912892239066643897)
          ·
            refine ⟨6471689934669179299982923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8628919912892239066643897 6471689934669179299982923)
            ·
              refine ⟨9707534902003768949974385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6471689934669179299982923 9707534902003768949974385)
              ·
                refine ⟨7280651176502826712480789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9707534902003768949974385 7280651176502826712480789)
                ·
                  refine ⟨341280523898570002147537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7280651176502826712480789 341280523898570002147537)
                  ·
                    rfl

theorem cell23_5981773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_5981773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981773 prefixEnd_5981773 := by exact prefixLift 5981773
  have htrace : WordTrace (prefixWord ++ tailWord_5981773) baseStart_5981773 baseEnd_5981773 := by
    simpa [prefixWord, tailWord_5981773, baseEnd_5981773] using wordTrace_append hprefix tailTrace_5981773
  have hstable : (prefixWord ++ tailWord_5981773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981773).length < 2 ^ (prefixWord ++ tailWord_5981773).sum := by decide
  have hdescent : baseEnd_5981773 < baseStart_5981773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981783 : List Nat := [1, 1, 3, 2, 2, 3, 2, 4, 1, 1, 3]
def baseStart_5981783 : Nat := 118140960795 + 5981783 * 2 ^ 59
def prefixEnd_5981783 : Nat := 4983230072969 + 3 ^ 40 * 5981783 * 2
def baseEnd_5981783 : Nat := 3071529849893674980202787

theorem tailTrace_5981783 : CollatzResearch.WordTrace tailWord_5981783 prefixEnd_5981783 3071529849893674980202787 := by
  unfold tailWord_5981783
  simp only [CollatzResearch.WordTrace]
  refine ⟨218173549688029273047206003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145449033125352848698137335 218173549688029273047206003)
  ·
    refine ⟨327260324532043909570809005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218173549688029273047206003 327260324532043909570809005)
    ·
      refine ⟨122722621699516466089053377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 327260324532043909570809005 122722621699516466089053377)
      ·
        refine ⟨92041966274637349566790033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122722621699516466089053377 92041966274637349566790033)
        ·
          refine ⟨69031474705978012175092525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92041966274637349566790033 69031474705978012175092525)
          ·
            refine ⟨25886803014741754565659697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69031474705978012175092525 25886803014741754565659697)
            ·
              refine ⟨19415102261056315924244773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25886803014741754565659697 19415102261056315924244773)
              ·
                refine ⟨3640331673948059235795895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19415102261056315924244773 3640331673948059235795895)
                ·
                  refine ⟨5460497510922088853693843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3640331673948059235795895 5460497510922088853693843)
                  ·
                    refine ⟨8190746266383133280540765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5460497510922088853693843 8190746266383133280540765)
                    ·
                      refine ⟨3071529849893674980202787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8190746266383133280540765 3071529849893674980202787)
                      ·
                        rfl

theorem cell23_5981783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 4, 1, 1, 3].length) (baseStart_5981783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981783 prefixEnd_5981783 := by exact prefixLift 5981783
  have htrace : WordTrace (prefixWord ++ tailWord_5981783) baseStart_5981783 baseEnd_5981783 := by
    simpa [prefixWord, tailWord_5981783, baseEnd_5981783] using wordTrace_append hprefix tailTrace_5981783
  have hstable : (prefixWord ++ tailWord_5981783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981783).length < 2 ^ (prefixWord ++ tailWord_5981783).sum := by decide
  have hdescent : baseEnd_5981783 < baseStart_5981783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981799 : List Nat := [1, 1, 5, 1, 1, 1, 5, 1, 1, 6]
def baseStart_5981799 : Nat := 118140960795 + 5981799 * 2 ^ 59
def prefixEnd_5981799 : Nat := 4983230072969 + 3 ^ 40 * 5981799 * 2
def baseEnd_5981799 : Nat := 1023846021861382305867571

theorem tailTrace_5981799 : CollatzResearch.WordTrace tailWord_5981799 prefixEnd_5981799 1023846021861382305867571 := by
  unfold tailWord_5981799
  simp only [CollatzResearch.WordTrace]
  refine ⟨218174133255971307779788451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145449422170647538519858967 218174133255971307779788451)
  ·
    refine ⟨327261199883956961669682677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218174133255971307779788451 327261199883956961669682677)
    ·
      refine ⟨30680737489120965156532751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 327261199883956961669682677 30680737489120965156532751)
      ·
        refine ⟨46021106233681447734799127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30680737489120965156532751 46021106233681447734799127)
        ·
          refine ⟨69031659350522171602198691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46021106233681447734799127 69031659350522171602198691)
          ·
            refine ⟨103547489025783257403298037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69031659350522171602198691 103547489025783257403298037)
            ·
              refine ⟨9707577096167180381559191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103547489025783257403298037 9707577096167180381559191)
              ·
                refine ⟨14561365644250770572338787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9707577096167180381559191 14561365644250770572338787)
                ·
                  refine ⟨21842048466376155858508181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14561365644250770572338787 21842048466376155858508181)
                  ·
                    refine ⟨1023846021861382305867571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21842048466376155858508181 1023846021861382305867571)
                    ·
                      rfl

theorem cell23_5981799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_5981799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981799 prefixEnd_5981799 := by exact prefixLift 5981799
  have htrace : WordTrace (prefixWord ++ tailWord_5981799) baseStart_5981799 baseEnd_5981799 := by
    simpa [prefixWord, tailWord_5981799, baseEnd_5981799] using wordTrace_append hprefix tailTrace_5981799
  have hstable : (prefixWord ++ tailWord_5981799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981799).length < 2 ^ (prefixWord ++ tailWord_5981799).sum := by decide
  have hdescent : baseEnd_5981799 < baseStart_5981799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981809 : List Nat := [1, 2, 2, 2, 1, 1, 1, 5, 3, 2, 3]
def baseStart_5981809 : Nat := 118140960795 + 5981809 * 2 ^ 59
def prefixEnd_5981809 : Nat := 4983230072969 + 3 ^ 40 * 5981809 * 2
def baseEnd_5981809 : Nat := 3071543200390691878477667

theorem tailTrace_5981809 : CollatzResearch.WordTrace tailWord_5981809 prefixEnd_5981809 3071543200390691878477667 := by
  unfold tailWord_5981809
  simp only [CollatzResearch.WordTrace]
  refine ⟨218174497985935079487652481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145449665323956719658434987 218174497985935079487652481)
  ·
    refine ⟨163630873489451309615739361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218174497985935079487652481 163630873489451309615739361)
    ·
      refine ⟨122723155117088482211804521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163630873489451309615739361 122723155117088482211804521)
      ·
        refine ⟨92042366337816361658853391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122723155117088482211804521 92042366337816361658853391)
        ·
          refine ⟨138063549506724542488280087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92042366337816361658853391 138063549506724542488280087)
          ·
            refine ⟨207095324260086813732420131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138063549506724542488280087 207095324260086813732420131)
            ·
              refine ⟨310642986390130220598630197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207095324260086813732420131 310642986390130220598630197)
              ·
                refine ⟨29122779974074708181121581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 310642986390130220598630197 29122779974074708181121581)
                ·
                  refine ⟨10921042490278015567920593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29122779974074708181121581 10921042490278015567920593)
                  ·
                    refine ⟨8190781867708511675940445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10921042490278015567920593 8190781867708511675940445)
                    ·
                      refine ⟨3071543200390691878477667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8190781867708511675940445 3071543200390691878477667)
                      ·
                        rfl

theorem cell23_5981809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3, 2, 3].length) (baseStart_5981809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981809 prefixEnd_5981809 := by exact prefixLift 5981809
  have htrace : WordTrace (prefixWord ++ tailWord_5981809) baseStart_5981809 baseEnd_5981809 := by
    simpa [prefixWord, tailWord_5981809, baseEnd_5981809] using wordTrace_append hprefix tailTrace_5981809
  have hstable : (prefixWord ++ tailWord_5981809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981809).length < 2 ^ (prefixWord ++ tailWord_5981809).sum := by decide
  have hdescent : baseEnd_5981809 < baseStart_5981809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981896 : List Nat := [2, 1, 3, 1, 2, 2, 1, 2, 3, 4, 2]
def baseStart_5981896 : Nat := 118140960795 + 5981896 * 2 ^ 59
def prefixEnd_5981896 : Nat := 4983230072969 + 3 ^ 40 * 5981896 * 2
def baseEnd_5981896 : Nat := 3071587873207633038089767

theorem tailTrace_5981896 : CollatzResearch.WordTrace tailWord_5981896 prefixEnd_5981896 3071587873207633038089767 := by
  unfold tailWord_5981896
  simp only [CollatzResearch.WordTrace]
  refine ⟨109088835568309946673034771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145451780757746595564046361 109088835568309946673034771)
  ·
    refine ⟨163633253352464920009552157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109088835568309946673034771 163633253352464920009552157)
    ·
      refine ⟨61362470007174345003582059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163633253352464920009552157 61362470007174345003582059)
      ·
        refine ⟨92043705010761517505373089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61362470007174345003582059 92043705010761517505373089)
        ·
          refine ⟨69032778758071138129029817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92043705010761517505373089 69032778758071138129029817)
          ·
            refine ⟨51774584068553353596772363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69032778758071138129029817 51774584068553353596772363)
            ·
              refine ⟨77661876102830030395158545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51774584068553353596772363 77661876102830030395158545)
              ·
                refine ⟨58246407077122522796368909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77661876102830030395158545 58246407077122522796368909)
                ·
                  refine ⟨21842402653920946048638341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58246407077122522796368909 21842402653920946048638341)
                  ·
                    refine ⟨4095450497610177384119689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21842402653920946048638341 4095450497610177384119689)
                    ·
                      refine ⟨3071587873207633038089767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4095450497610177384119689 3071587873207633038089767)
                      ·
                        rfl

theorem cell23_5981896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 3, 4, 2].length) (baseStart_5981896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981896 prefixEnd_5981896 := by exact prefixLift 5981896
  have htrace : WordTrace (prefixWord ++ tailWord_5981896) baseStart_5981896 baseEnd_5981896 := by
    simpa [prefixWord, tailWord_5981896, baseEnd_5981896] using wordTrace_append hprefix tailTrace_5981896
  have hstable : (prefixWord ++ tailWord_5981896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981896).length < 2 ^ (prefixWord ++ tailWord_5981896).sum := by decide
  have hdescent : baseEnd_5981896 < baseStart_5981896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981906 : List Nat := [3, 2, 2, 2, 2, 2, 1, 1, 2, 6]
def baseStart_5981906 : Nat := 118140960795 + 5981906 * 2 ^ 59
def prefixEnd_5981906 : Nat := 4983230072969 + 3 ^ 40 * 5981906 * 2
def baseEnd_5981906 : Nat := 1023864336004725999654907

theorem tailTrace_5981906 : CollatzResearch.WordTrace tailWord_5981906 prefixEnd_5981906 1023864336004725999654907 := by
  unfold tailWord_5981906
  simp only [CollatzResearch.WordTrace]
  refine ⟨54544508966645916263483393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145452023911055776702622381 54544508966645916263483393)
  ·
    refine ⟨40908381724984437197612545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54544508966645916263483393 40908381724984437197612545)
    ·
      refine ⟨30681286293738327898209409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40908381724984437197612545 30681286293738327898209409)
      ·
        refine ⟨23010964720303745923657057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30681286293738327898209409 23010964720303745923657057)
        ·
          refine ⟨17258223540227809442742793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23010964720303745923657057 17258223540227809442742793)
          ·
            refine ⟨12943667655170857082057095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17258223540227809442742793 12943667655170857082057095)
            ·
              refine ⟨19415501482756285623085643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12943667655170857082057095 19415501482756285623085643)
              ·
                refine ⟨29123252224134428434628465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19415501482756285623085643 29123252224134428434628465)
                ·
                  refine ⟨21842439168100821325971349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29123252224134428434628465 21842439168100821325971349)
                  ·
                    refine ⟨1023864336004725999654907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21842439168100821325971349 1023864336004725999654907)
                    ·
                      rfl

theorem cell23_5981906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_5981906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981906 prefixEnd_5981906 := by exact prefixLift 5981906
  have htrace : WordTrace (prefixWord ++ tailWord_5981906) baseStart_5981906 baseEnd_5981906 := by
    simpa [prefixWord, tailWord_5981906, baseEnd_5981906] using wordTrace_append hprefix tailTrace_5981906
  have hstable : (prefixWord ++ tailWord_5981906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981906).length < 2 ^ (prefixWord ++ tailWord_5981906).sum := by decide
  have hdescent : baseEnd_5981906 < baseStart_5981906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981913 : List Nat := [1, 2, 1, 2, 3, 4, 2, 1, 1, 4, 2]
def baseStart_5981913 : Nat := 118140960795 + 5981913 * 2 ^ 59
def prefixEnd_5981913 : Nat := 4983230072969 + 3 ^ 40 * 5981913 * 2
def baseEnd_5981913 : Nat := 3071596602378759471577189

theorem tailTrace_5981913 : CollatzResearch.WordTrace tailWord_5981913 prefixEnd_5981913 3071596602378759471577189 := by
  unfold tailWord_5981913
  simp only [CollatzResearch.WordTrace]
  refine ⟨218178291177558305249438393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145452194118372203499625595 218178291177558305249438393)
  ·
    refine ⟨163633718383168728937078795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218178291177558305249438393 163633718383168728937078795)
    ·
      refine ⟨245450577574753093405618193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163633718383168728937078795 245450577574753093405618193)
      ·
        refine ⟨184087933181064820054213645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245450577574753093405618193 184087933181064820054213645)
        ·
          refine ⟨69032974942899307520330117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184087933181064820054213645 69032974942899307520330117)
          ·
            refine ⟨12943682801793620160061897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69032974942899307520330117 12943682801793620160061897)
            ·
              refine ⟨9707762101345215120046423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12943682801793620160061897 9707762101345215120046423)
              ·
                refine ⟨14561643152017822680069635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9707762101345215120046423 14561643152017822680069635)
                ·
                  refine ⟨21842464728026734020104453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14561643152017822680069635 21842464728026734020104453)
                  ·
                    refine ⟨4095462136505012628769585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21842464728026734020104453 4095462136505012628769585)
                    ·
                      refine ⟨3071596602378759471577189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4095462136505012628769585 3071596602378759471577189)
                      ·
                        rfl

theorem cell23_5981913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 4, 2].length) (baseStart_5981913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981913 prefixEnd_5981913 := by exact prefixLift 5981913
  have htrace : WordTrace (prefixWord ++ tailWord_5981913) baseStart_5981913 baseEnd_5981913 := by
    simpa [prefixWord, tailWord_5981913, baseEnd_5981913] using wordTrace_append hprefix tailTrace_5981913
  have hstable : (prefixWord ++ tailWord_5981913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981913).length < 2 ^ (prefixWord ++ tailWord_5981913).sum := by decide
  have hdescent : baseEnd_5981913 < baseStart_5981913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981919 : List Nat := [1, 1, 2, 3, 2, 2, 3, 2, 7]
def baseStart_5981919 : Nat := 118140960795 + 5981919 * 2 ^ 59
def prefixEnd_5981919 : Nat := 4983230072969 + 3 ^ 40 * 5981919 * 2
def baseEnd_5981919 : Nat := 341288853695854049789129

theorem tailTrace_5981919 : CollatzResearch.WordTrace tailWord_5981919 prefixEnd_5981919 341288853695854049789129 := by
  unfold tailWord_5981919
  simp only [CollatzResearch.WordTrace]
  refine ⟨218178510015536568274156811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145452340010357712182771207 218178510015536568274156811)
  ·
    refine ⟨327267765023304852411235217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218178510015536568274156811 327267765023304852411235217)
    ·
      refine ⟨245450823767478639308426413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327267765023304852411235217 245450823767478639308426413)
      ·
        refine ⟨92044058912804489740659905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245450823767478639308426413 92044058912804489740659905)
        ·
          refine ⟨69033044184603367305494929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92044058912804489740659905 69033044184603367305494929)
          ·
            refine ⟨51774783138452525479121197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69033044184603367305494929 51774783138452525479121197)
            ·
              refine ⟨19415543676919697054670449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51774783138452525479121197 19415543676919697054670449)
              ·
                refine ⟨14561657757689772791002837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19415543676919697054670449 14561657757689772791002837)
                ·
                  refine ⟨341288853695854049789129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14561657757689772791002837 341288853695854049789129)
                  ·
                    rfl

theorem cell23_5981919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 7].length) (baseStart_5981919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981919 prefixEnd_5981919 := by exact prefixLift 5981919
  have htrace : WordTrace (prefixWord ++ tailWord_5981919) baseStart_5981919 baseEnd_5981919 := by
    simpa [prefixWord, tailWord_5981919, baseEnd_5981919] using wordTrace_append hprefix tailTrace_5981919
  have hstable : (prefixWord ++ tailWord_5981919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981919).length < 2 ^ (prefixWord ++ tailWord_5981919).sum := by decide
  have hdescent : baseEnd_5981919 < baseStart_5981919 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981929 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 3, 5, 3]
def baseStart_5981929 : Nat := 118140960795 + 5981929 * 2 ^ 59
def prefixEnd_5981929 : Nat := 4983230072969 + 3 ^ 40 * 5981929 * 2
def baseEnd_5981929 : Nat := 3071604818069231408977115

theorem tailTrace_5981929 : CollatzResearch.WordTrace tailWord_5981929 prefixEnd_5981929 3071604818069231408977115 := by
  unfold tailWord_5981929
  simp only [CollatzResearch.WordTrace]
  refine ⟨218178874745500339982020841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145452583163666893321347227 218178874745500339982020841)
  ·
    refine ⟨163634156059125254986515631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218178874745500339982020841 163634156059125254986515631)
    ·
      refine ⟨245451234088687882479773447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163634156059125254986515631 245451234088687882479773447)
      ·
        refine ⟨368176851133031823719660171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245451234088687882479773447 368176851133031823719660171)
        ·
          refine ⟨552265276699547735579490257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368176851133031823719660171 552265276699547735579490257)
          ·
            refine ⟨414198957524660801684617693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 552265276699547735579490257 414198957524660801684617693)
            ·
              refine ⟨155324609071747800631731635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 414198957524660801684617693 155324609071747800631731635)
              ·
                refine ⟨232986913607621700947597453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155324609071747800631731635 232986913607621700947597453)
                ·
                  refine ⟨87370092602858137855349045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 232986913607621700947597453 87370092602858137855349045)
                  ·
                    refine ⟨8190946181517950423938973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 87370092602858137855349045 8190946181517950423938973)
                    ·
                      refine ⟨3071604818069231408977115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8190946181517950423938973 3071604818069231408977115)
                      ·
                        rfl

theorem cell23_5981929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 5, 3].length) (baseStart_5981929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981929 prefixEnd_5981929 := by exact prefixLift 5981929
  have htrace : WordTrace (prefixWord ++ tailWord_5981929) baseStart_5981929 baseEnd_5981929 := by
    simpa [prefixWord, tailWord_5981929, baseEnd_5981929] using wordTrace_append hprefix tailTrace_5981929
  have hstable : (prefixWord ++ tailWord_5981929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981929).length < 2 ^ (prefixWord ++ tailWord_5981929).sum := by decide
  have hdescent : baseEnd_5981929 < baseStart_5981929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981958 : List Nat := [6, 2, 2, 1, 2, 1, 1, 1, 1, 3, 3]
def baseStart_5981958 : Nat := 118140960795 + 5981958 * 2 ^ 59
def prefixEnd_5981958 : Nat := 4983230072969 + 3 ^ 40 * 5981958 * 2
def baseEnd_5981958 : Nat := 3071619709008211795514483

theorem tailTrace_5981958 : CollatzResearch.WordTrace tailWord_5981958 prefixEnd_5981958 3071619709008211795514483 := by
  unfold tailWord_5981958
  simp only [CollatzResearch.WordTrace]
  refine ⟨6818122889449852435463329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 145453288308263518623217685 6818122889449852435463329)
  ·
    refine ⟨5113592167087389326597497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6818122889449852435463329 5113592167087389326597497)
    ·
      refine ⟨3835194125315541994948123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5113592167087389326597497 3835194125315541994948123)
      ·
        refine ⟨5752791187973312992422185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3835194125315541994948123 5752791187973312992422185)
        ·
          refine ⟨4314593390979984744316639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5752791187973312992422185 4314593390979984744316639)
          ·
            refine ⟨6471890086469977116474959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4314593390979984744316639 6471890086469977116474959)
            ·
              refine ⟨9707835129704965674712439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6471890086469977116474959 9707835129704965674712439)
              ·
                refine ⟨14561752694557448512068659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9707835129704965674712439 14561752694557448512068659)
                ·
                  refine ⟨21842629041836172768102989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14561752694557448512068659 21842629041836172768102989)
                  ·
                    refine ⟨8190985890688564788038621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21842629041836172768102989 8190985890688564788038621)
                    ·
                      refine ⟨3071619709008211795514483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8190985890688564788038621 3071619709008211795514483)
                      ·
                        rfl

theorem cell23_5981958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_5981958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981958 prefixEnd_5981958 := by exact prefixLift 5981958
  have htrace : WordTrace (prefixWord ++ tailWord_5981958) baseStart_5981958 baseEnd_5981958 := by
    simpa [prefixWord, tailWord_5981958, baseEnd_5981958] using wordTrace_append hprefix tailTrace_5981958
  have hstable : (prefixWord ++ tailWord_5981958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981958).length < 2 ^ (prefixWord ++ tailWord_5981958).sum := by decide
  have hdescent : baseEnd_5981958 < baseStart_5981958 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981986 : List Nat := [3, 3, 1, 1, 2, 1, 1, 3, 1, 3, 4]
def baseStart_5981986 : Nat := 118140960795 + 5981986 * 2 ^ 59
def prefixEnd_5981986 : Nat := 4983230072969 + 3 ^ 40 * 5981986 * 2
def baseEnd_5981986 : Nat := 3071634086466537685964353

theorem tailTrace_5981986 : CollatzResearch.WordTrace tailWord_5981986 prefixEnd_5981986 3071634086466537685964353 := by
  unfold tailWord_5981986
  simp only [CollatzResearch.WordTrace]
  refine ⟨54545238426573459679211453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145453969137529225811230541 54545238426573459679211453)
  ·
    refine ⟨20454464409965047379704295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54545238426573459679211453 20454464409965047379704295)
    ·
      refine ⟨30681696614947571069556443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20454464409965047379704295 30681696614947571069556443)
      ·
        refine ⟨46022544922421356604334665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30681696614947571069556443 46022544922421356604334665)
        ·
          refine ⟨34516908691816017453250999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46022544922421356604334665 34516908691816017453250999)
          ·
            refine ⟨51775363037724026179876499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34516908691816017453250999 51775363037724026179876499)
            ·
              refine ⟨77663044556586039269814749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51775363037724026179876499 77663044556586039269814749)
              ·
                refine ⟨29123641708719764726180531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77663044556586039269814749 29123641708719764726180531)
                ·
                  refine ⟨43685462563079647089270797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29123641708719764726180531 43685462563079647089270797)
                  ·
                    refine ⟨16382048461154867658476549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43685462563079647089270797 16382048461154867658476549)
                    ·
                      refine ⟨3071634086466537685964353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16382048461154867658476549 3071634086466537685964353)
                      ·
                        rfl

theorem cell23_5981986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_5981986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981986 prefixEnd_5981986 := by exact prefixLift 5981986
  have htrace : WordTrace (prefixWord ++ tailWord_5981986) baseStart_5981986 baseEnd_5981986 := by
    simpa [prefixWord, tailWord_5981986, baseEnd_5981986] using wordTrace_append hprefix tailTrace_5981986
  have hstable : (prefixWord ++ tailWord_5981986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981986).length < 2 ^ (prefixWord ++ tailWord_5981986).sum := by decide
  have hdescent : baseEnd_5981986 < baseStart_5981986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5981999 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 1, 6, 4]
def baseStart_5981999 : Nat := 118140960795 + 5981999 * 2 ^ 59
def prefixEnd_5981999 : Nat := 4983230072969 + 3 ^ 40 * 5981999 * 2
def baseEnd_5981999 : Nat := 3071640761715046135101793

theorem tailTrace_5981999 : CollatzResearch.WordTrace tailWord_5981999 prefixEnd_5981999 3071640761715046135101793 := by
  unfold tailWord_5981999
  simp only [CollatzResearch.WordTrace]
  refine ⟨218181427855246741937069051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145454285236831161291379367 218181427855246741937069051)
  ·
    refine ⟨327272141782870112905603577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218181427855246741937069051 327272141782870112905603577)
    ·
      refine ⟨245454106337152584679202683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327272141782870112905603577 245454106337152584679202683)
      ·
        refine ⟨368181159505728877018804025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245454106337152584679202683 368181159505728877018804025)
        ·
          refine ⟨276135869629296657764103019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368181159505728877018804025 276135869629296657764103019)
          ·
            refine ⟨414203804443944986646154529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276135869629296657764103019 414203804443944986646154529)
            ·
              refine ⟨310652853332958739984615897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 414203804443944986646154529 310652853332958739984615897)
              ·
                refine ⟨232989639999719054988461923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 310652853332958739984615897 232989639999719054988461923)
                ·
                  refine ⟨349484459999578582482692885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 232989639999719054988461923 349484459999578582482692885)
                  ·
                    refine ⟨16382084062480246053876229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 349484459999578582482692885 16382084062480246053876229)
                    ·
                      refine ⟨3071640761715046135101793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16382084062480246053876229 3071640761715046135101793)
                      ·
                        rfl

theorem cell23_5981999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6, 4].length) (baseStart_5981999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5981999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5981999 prefixEnd_5981999 := by exact prefixLift 5981999
  have htrace : WordTrace (prefixWord ++ tailWord_5981999) baseStart_5981999 baseEnd_5981999 := by
    simpa [prefixWord, tailWord_5981999, baseEnd_5981999] using wordTrace_append hprefix tailTrace_5981999
  have hstable : (prefixWord ++ tailWord_5981999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5981999).length < 2 ^ (prefixWord ++ tailWord_5981999).sum := by decide
  have hdescent : baseEnd_5981999 < baseStart_5981999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5981999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5982003 : List Nat := [1, 1, 1, 2, 7, 1, 1, 2, 2, 1, 4]
def baseStart_5982003 : Nat := 118140960795 + 5982003 * 2 ^ 59
def prefixEnd_5982003 : Nat := 4983230072969 + 3 ^ 40 * 5982003 * 2
def baseEnd_5982003 : Nat := 3071642815637664119451775

theorem tailTrace_5982003 : CollatzResearch.WordTrace tailWord_5982003 prefixEnd_5982003 3071642815637664119451775 := by
  unfold tailWord_5982003
  simp only [CollatzResearch.WordTrace]
  refine ⟨218181573747232250620214663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145454382498154833746809775 218181573747232250620214663)
  ·
    refine ⟨327272360620848375930321995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218181573747232250620214663 327272360620848375930321995)
    ·
      refine ⟨490908540931272563895482993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327272360620848375930321995 490908540931272563895482993)
      ·
        refine ⟨368181405698454422921612245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 490908540931272563895482993 368181405698454422921612245)
        ·
          refine ⟨8629251696057525537225287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 368181405698454422921612245 8629251696057525537225287)
          ·
            refine ⟨12943877544086288305837931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8629251696057525537225287 12943877544086288305837931)
            ·
              refine ⟨19415816316129432458756897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12943877544086288305837931 19415816316129432458756897)
              ·
                refine ⟨14561862237097074344067673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19415816316129432458756897 14561862237097074344067673)
                ·
                  refine ⟨10921396677822805758050755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14561862237097074344067673 10921396677822805758050755)
                  ·
                    refine ⟨16382095016734208637076133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10921396677822805758050755 16382095016734208637076133)
                    ·
                      refine ⟨3071642815637664119451775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16382095016734208637076133 3071642815637664119451775)
                      ·
                        rfl

theorem cell23_5982003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 2, 1, 4].length) (baseStart_5982003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5982003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5982003 prefixEnd_5982003 := by exact prefixLift 5982003
  have htrace : WordTrace (prefixWord ++ tailWord_5982003) baseStart_5982003 baseEnd_5982003 := by
    simpa [prefixWord, tailWord_5982003, baseEnd_5982003] using wordTrace_append hprefix tailTrace_5982003
  have hstable : (prefixWord ++ tailWord_5982003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5982003).length < 2 ^ (prefixWord ++ tailWord_5982003).sum := by decide
  have hdescent : baseEnd_5982003 < baseStart_5982003 := by decide
  rcases family_descends (prefixWord ++ tailWord_5982003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5982026 : List Nat := [3, 1, 2, 1, 1, 1, 5, 3, 6]
def baseStart_5982026 : Nat := 118140960795 + 5982026 * 2 ^ 59
def prefixEnd_5982026 : Nat := 4983230072969 + 3 ^ 40 * 5982026 * 2
def baseEnd_5982026 : Nat := 341294958410301947718241

theorem tailTrace_5982026 : CollatzResearch.WordTrace tailWord_5982026 prefixEnd_5982026 341294958410301947718241 := by
  unfold tailWord_5982026
  simp only [CollatzResearch.WordTrace]
  refine ⟨54545603156537231387075483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145454941750765950365534621 54545603156537231387075483)
  ·
    refine ⟨81818404734805847080613225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54545603156537231387075483 81818404734805847080613225)
    ·
      refine ⟨61363803551104385310459919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81818404734805847080613225 61363803551104385310459919)
      ·
        refine ⟨92045705326656577965689879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61363803551104385310459919 92045705326656577965689879)
        ·
          refine ⟨138068557989984866948534819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92045705326656577965689879 138068557989984866948534819)
          ·
            refine ⟨207102836984977300422802229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138068557989984866948534819 207102836984977300422802229)
            ·
              refine ⟨19415890967341621914637709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 207102836984977300422802229 19415890967341621914637709)
              ·
                refine ⟨7280959112753108217989141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19415890967341621914637709 7280959112753108217989141)
                ·
                  refine ⟨341294958410301947718241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7280959112753108217989141 341294958410301947718241)
                  ·
                    rfl

theorem cell23_5982026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3, 6].length) (baseStart_5982026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5982026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5982026 prefixEnd_5982026 := by exact prefixLift 5982026
  have htrace : WordTrace (prefixWord ++ tailWord_5982026) baseStart_5982026 baseEnd_5982026 := by
    simpa [prefixWord, tailWord_5982026, baseEnd_5982026] using wordTrace_append hprefix tailTrace_5982026
  have hstable : (prefixWord ++ tailWord_5982026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5982026).length < 2 ^ (prefixWord ++ tailWord_5982026).sum := by decide
  have hdescent : baseEnd_5982026 < baseStart_5982026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5982026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5982116 : List Nat := [2, 3, 1, 2, 1, 4, 10]
def baseStart_5982116 : Nat := 118140960795 + 5982116 * 2 ^ 59
def prefixEnd_5982116 : Nat := 4983230072969 + 3 ^ 40 * 5982116 * 2
def baseEnd_5982116 : Nat := 37922232579649656510355

theorem tailTrace_5982116 : CollatzResearch.WordTrace tailWord_5982116 prefixEnd_5982116 37922232579649656510355 := by
  unfold tailWord_5982116
  simp only [CollatzResearch.WordTrace]
  refine ⟨109092847597911435459539101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145457130130548580612718801 109092847597911435459539101)
  ·
    refine ⟨40909817849216788297327163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109092847597911435459539101 40909817849216788297327163)
    ·
      refine ⟨61364726773825182445990745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40909817849216788297327163 61364726773825182445990745)
      ·
        refine ⟨46023545080368886834493059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61364726773825182445990745 46023545080368886834493059)
        ·
          refine ⟨69035317620553330251739589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46023545080368886834493059 69035317620553330251739589)
          ·
            refine ⟨12944122053853749422201173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69035317620553330251739589 12944122053853749422201173)
            ·
              refine ⟨37922232579649656510355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12944122053853749422201173 37922232579649656510355)
              ·
                rfl

theorem cell23_5982116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 10].length) (baseStart_5982116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5982116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5982116 prefixEnd_5982116 := by exact prefixLift 5982116
  have htrace : WordTrace (prefixWord ++ tailWord_5982116) baseStart_5982116 baseEnd_5982116 := by
    simpa [prefixWord, tailWord_5982116, baseEnd_5982116] using wordTrace_append hprefix tailTrace_5982116
  have hstable : (prefixWord ++ tailWord_5982116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5982116).length < 2 ^ (prefixWord ++ tailWord_5982116).sum := by decide
  have hdescent : baseEnd_5982116 < baseStart_5982116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5982116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5982127 : List Nat := [1, 1, 2, 1, 2, 2, 3, 6, 1, 2, 2]
def baseStart_5982127 : Nat := 118140960795 + 5982127 * 2 ^ 59
def prefixEnd_5982127 : Nat := 4983230072969 + 3 ^ 40 * 5982127 * 2
def baseEnd_5982127 : Nat := 3071706487238821634301205

theorem tailTrace_5982127 : CollatzResearch.WordTrace tailWord_5982127 prefixEnd_5982127 3071706487238821634301205 := by
  unfold tailWord_5982127
  simp only [CollatzResearch.WordTrace]
  refine ⟨218186096398783019797728635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145457397599188679865152423 218186096398783019797728635)
  ·
    refine ⟨327279144598174529696592953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218186096398783019797728635 327279144598174529696592953)
    ·
      refine ⟨245459358448630897272444715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327279144598174529696592953 245459358448630897272444715)
      ·
        refine ⟨368189037672946345908667073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245459358448630897272444715 368189037672946345908667073)
        ·
          refine ⟨276141778254709759431500305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368189037672946345908667073 276141778254709759431500305)
          ·
            refine ⟨207106333691032319573625229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276141778254709759431500305 207106333691032319573625229)
            ·
              refine ⟨77664875134137119840109461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 207106333691032319573625229 77664875134137119840109461)
              ·
                refine ⟨3640541021912677492505131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77664875134137119840109461 3640541021912677492505131)
                ·
                  refine ⟨5460811532869016238757697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3640541021912677492505131 5460811532869016238757697)
                  ·
                    refine ⟨4095608649651762179068273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5460811532869016238757697 4095608649651762179068273)
                    ·
                      refine ⟨3071706487238821634301205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4095608649651762179068273 3071706487238821634301205)
                      ·
                        rfl

theorem cell23_5982127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 6, 1, 2, 2].length) (baseStart_5982127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5982127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5982127 prefixEnd_5982127 := by exact prefixLift 5982127
  have htrace : WordTrace (prefixWord ++ tailWord_5982127) baseStart_5982127 baseEnd_5982127 := by
    simpa [prefixWord, tailWord_5982127, baseEnd_5982127] using wordTrace_append hprefix tailTrace_5982127
  have hstable : (prefixWord ++ tailWord_5982127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5982127).length < 2 ^ (prefixWord ++ tailWord_5982127).sum := by decide
  have hdescent : baseEnd_5982127 < baseStart_5982127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5982127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5982140 : List Nat := [2, 2, 2, 5, 1, 1, 1, 1, 1, 1, 6]
def baseStart_5982140 : Nat := 118140960795 + 5982140 * 2 ^ 59
def prefixEnd_5982140 : Nat := 4983230072969 + 3 ^ 40 * 5982140 * 2
def baseEnd_5982140 : Nat := 3071713162487330083438645

theorem tailTrace_5982140 : CollatzResearch.WordTrace tailWord_5982140 prefixEnd_5982140 3071713162487330083438645 := by
  unfold tailWord_5982140
  simp only [CollatzResearch.WordTrace]
  refine ⟨109093285273867961508975937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145457713698490615345301249 109093285273867961508975937)
  ·
    refine ⟨81819963955400971131731953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109093285273867961508975937 81819963955400971131731953)
    ·
      refine ⟨61364972966550728348798965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81819963955400971131731953 61364972966550728348798965)
      ·
        refine ⟨5752966215614130782699903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61364972966550728348798965 5752966215614130782699903)
        ·
          refine ⟨8629449323421196174049855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5752966215614130782699903 8629449323421196174049855)
          ·
            refine ⟨12944173985131794261074783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8629449323421196174049855 12944173985131794261074783)
            ·
              refine ⟨19416260977697691391612175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12944173985131794261074783 19416260977697691391612175)
              ·
                refine ⟨29124391466546537087418263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19416260977697691391612175 29124391466546537087418263)
                ·
                  refine ⟨43686587199819805631127395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29124391466546537087418263 43686587199819805631127395)
                  ·
                    refine ⟨65529880799729708446691093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43686587199819805631127395 65529880799729708446691093)
                    ·
                      refine ⟨3071713162487330083438645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65529880799729708446691093 3071713162487330083438645)
                      ·
                        rfl

theorem cell23_5982140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_5982140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5982140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5982140 prefixEnd_5982140 := by exact prefixLift 5982140
  have htrace : WordTrace (prefixWord ++ tailWord_5982140) baseStart_5982140 baseEnd_5982140 := by
    simpa [prefixWord, tailWord_5982140, baseEnd_5982140] using wordTrace_append hprefix tailTrace_5982140
  have hstable : (prefixWord ++ tailWord_5982140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5982140).length < 2 ^ (prefixWord ++ tailWord_5982140).sum := by decide
  have hdescent : baseEnd_5982140 < baseStart_5982140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5982140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5982176 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 4, 6]
def baseStart_5982176 : Nat := 118140960795 + 5982176 * 2 ^ 59
def prefixEnd_5982176 : Nat := 4983230072969 + 3 ^ 40 * 5982176 * 2
def baseEnd_5982176 : Nat := 1023910549263630647529493

theorem tailTrace_5982176 : CollatzResearch.WordTrace tailWord_5982176 prefixEnd_5982176 1023910549263630647529493 := by
  unfold tailWord_5982176
  simp only [CollatzResearch.WordTrace]
  refine ⟨109093941787802750583131191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145458589050403667444174921 109093941787802750583131191)
  ·
    refine ⟨163640912681704125874696787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109093941787802750583131191 163640912681704125874696787)
    ·
      refine ⟨245461369022556188812045181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163640912681704125874696787 245461369022556188812045181)
      ·
        refine ⟨92048013383458570804516943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245461369022556188812045181 92048013383458570804516943)
        ·
          refine ⟨138072020075187856206775415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92048013383458570804516943 138072020075187856206775415)
          ·
            refine ⟨207108030112781784310163123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138072020075187856206775415 207108030112781784310163123)
            ·
              refine ⟨310662045169172676465244685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207108030112781784310163123 310662045169172676465244685)
              ·
                refine ⟨116498266938439753674466757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 310662045169172676465244685 116498266938439753674466757)
                ·
                  refine ⟨21843425050957453813962517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116498266938439753674466757 21843425050957453813962517)
                  ·
                    refine ⟨1023910549263630647529493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21843425050957453813962517 1023910549263630647529493)
                    ·
                      rfl

theorem cell23_5982176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 4, 6].length) (baseStart_5982176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5982176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5982176 prefixEnd_5982176 := by exact prefixLift 5982176
  have htrace : WordTrace (prefixWord ++ tailWord_5982176) baseStart_5982176 baseEnd_5982176 := by
    simpa [prefixWord, tailWord_5982176, baseEnd_5982176] using wordTrace_append hprefix tailTrace_5982176
  have hstable : (prefixWord ++ tailWord_5982176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5982176).length < 2 ^ (prefixWord ++ tailWord_5982176).sum := by decide
  have hdescent : baseEnd_5982176 < baseStart_5982176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5982176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5982178 : List Nat := [3, 3, 3, 1, 3, 1, 1, 1, 3, 2, 2]
def baseStart_5982178 : Nat := 118140960795 + 5982178 * 2 ^ 59
def prefixEnd_5982178 : Nat := 4983230072969 + 3 ^ 40 * 5982178 * 2
def baseEnd_5982178 : Nat := 3071732674752200934763471

theorem tailTrace_5982178 : CollatzResearch.WordTrace tailWord_5982178 prefixEnd_5982178 3071732674752200934763471 := by
  unfold tailWord_5982178
  simp only [CollatzResearch.WordTrace]
  refine ⟨54546989130399563876958797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145458637681065503671890125 54546989130399563876958797)
  ·
    refine ⟨20455120923899836453859549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54546989130399563876958797 20455120923899836453859549)
    ·
      refine ⟨7670670346462438670197331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20455120923899836453859549 7670670346462438670197331)
      ·
        refine ⟨11506005519693658005295997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7670670346462438670197331 11506005519693658005295997)
        ·
          refine ⟨4314752069885121751985999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11506005519693658005295997 4314752069885121751985999)
          ·
            refine ⟨6472128104827682627978999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4314752069885121751985999 6472128104827682627978999)
            ·
              refine ⟨9708192157241523941968499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6472128104827682627978999 9708192157241523941968499)
              ·
                refine ⟨14562288235862285912952749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9708192157241523941968499 14562288235862285912952749)
                ·
                  refine ⟨5460858088448357217357281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14562288235862285912952749 5460858088448357217357281)
                  ·
                    refine ⟨4095643566336267913017961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5460858088448357217357281 4095643566336267913017961)
                    ·
                      refine ⟨3071732674752200934763471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4095643566336267913017961 3071732674752200934763471)
                      ·
                        rfl

theorem cell23_5982178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_5982178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5982178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5982178 prefixEnd_5982178 := by exact prefixLift 5982178
  have htrace : WordTrace (prefixWord ++ tailWord_5982178) baseStart_5982178 baseEnd_5982178 := by
    simpa [prefixWord, tailWord_5982178, baseEnd_5982178] using wordTrace_append hprefix tailTrace_5982178
  have hstable : (prefixWord ++ tailWord_5982178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5982178).length < 2 ^ (prefixWord ++ tailWord_5982178).sum := by decide
  have hdescent : baseEnd_5982178 < baseStart_5982178 := by decide
  rcases family_descends (prefixWord ++ tailWord_5982178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5982233 : List Nat := [1, 2, 1, 2, 1, 1, 3, 4, 2, 3, 3]
def baseStart_5982233 : Nat := 118140960795 + 5982233 * 2 ^ 59
def prefixEnd_5982233 : Nat := 4983230072969 + 3 ^ 40 * 5982233 * 2
def baseEnd_5982233 : Nat := 3071760916188198219575717

theorem tailTrace_5982233 : CollatzResearch.WordTrace tailWord_5982233 prefixEnd_5982233 3071760916188198219575717 := by
  unfold tailWord_5982233
  simp only [CollatzResearch.WordTrace]
  refine ⟨218189962536398999901087353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145459975024265999934058235 218189962536398999901087353)
  ·
    refine ⟨163642471902299249925815515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218189962536398999901087353 163642471902299249925815515)
    ·
      refine ⟨245463707853448874888723273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163642471902299249925815515 245463707853448874888723273)
      ·
        refine ⟨184097780890086656166542455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245463707853448874888723273 184097780890086656166542455)
        ·
          refine ⟨276146671335129984249813683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184097780890086656166542455 276146671335129984249813683)
          ·
            refine ⟨414220007002694976374720525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276146671335129984249813683 414220007002694976374720525)
            ·
              refine ⟨155332502626010616140520197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 414220007002694976374720525 155332502626010616140520197)
              ·
                refine ⟨29124844242376990526347537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 155332502626010616140520197 29124844242376990526347537)
                ·
                  refine ⟨21843633181782742894760653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29124844242376990526347537 21843633181782742894760653)
                  ·
                    refine ⟨8191362443168528585535245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21843633181782742894760653 8191362443168528585535245)
                    ·
                      refine ⟨3071760916188198219575717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8191362443168528585535245 3071760916188198219575717)
                      ·
                        rfl

theorem cell23_5982233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 3, 3].length) (baseStart_5982233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5982233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5982233 prefixEnd_5982233 := by exact prefixLift 5982233
  have htrace : WordTrace (prefixWord ++ tailWord_5982233) baseStart_5982233 baseEnd_5982233 := by
    simpa [prefixWord, tailWord_5982233, baseEnd_5982233] using wordTrace_append hprefix tailTrace_5982233
  have hstable : (prefixWord ++ tailWord_5982233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5982233).length < 2 ^ (prefixWord ++ tailWord_5982233).sum := by decide
  have hdescent : baseEnd_5982233 < baseStart_5982233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5982233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5982234 : List Nat := [3, 1, 1, 3, 1, 4, 2, 2, 2, 2, 2]
def baseStart_5982234 : Nat := 118140960795 + 5982234 * 2 ^ 59
def prefixEnd_5982234 : Nat := 4983230072969 + 3 ^ 40 * 5982234 * 2
def baseEnd_5982234 : Nat := 3071761429668852715663213

theorem tailTrace_5982234 : CollatzResearch.WordTrace tailWord_5982234 prefixEnd_5982234 3071761429668852715663213 := by
  unfold tailWord_5982234
  simp only [CollatzResearch.WordTrace]
  refine ⟨54547499752348844267968439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145459999339596918047915837 54547499752348844267968439)
  ·
    refine ⟨81821249628523266401952659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54547499752348844267968439 81821249628523266401952659)
    ·
      refine ⟨122731874442784899602928989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81821249628523266401952659 122731874442784899602928989)
      ·
        refine ⟨46024452916044337351098371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122731874442784899602928989 46024452916044337351098371)
        ·
          refine ⟨69036679374066506026647557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46024452916044337351098371 69036679374066506026647557)
          ·
            refine ⟨12944377382637469879996417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69036679374066506026647557 12944377382637469879996417)
            ·
              refine ⟨9708283036978102409997313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12944377382637469879996417 9708283036978102409997313)
              ·
                refine ⟨7281212277733576807497985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9708283036978102409997313 7281212277733576807497985)
                ·
                  refine ⟨5460909208300182605623489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7281212277733576807497985 5460909208300182605623489)
                  ·
                    refine ⟨4095681906225136954217617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5460909208300182605623489 4095681906225136954217617)
                    ·
                      refine ⟨3071761429668852715663213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4095681906225136954217617 3071761429668852715663213)
                      ·
                        rfl

theorem cell23_5982234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2, 2, 2, 2].length) (baseStart_5982234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5982234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5982234 prefixEnd_5982234 := by exact prefixLift 5982234
  have htrace : WordTrace (prefixWord ++ tailWord_5982234) baseStart_5982234 baseEnd_5982234 := by
    simpa [prefixWord, tailWord_5982234, baseEnd_5982234] using wordTrace_append hprefix tailTrace_5982234
  have hstable : (prefixWord ++ tailWord_5982234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5982234).length < 2 ^ (prefixWord ++ tailWord_5982234).sum := by decide
  have hdescent : baseEnd_5982234 < baseStart_5982234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5982234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5982247 : List Nat := [1, 1, 7, 1, 2, 1, 1, 1, 2, 2, 4]
def baseStart_5982247 : Nat := 118140960795 + 5982247 * 2 ^ 59
def prefixEnd_5982247 : Nat := 4983230072969 + 3 ^ 40 * 5982247 * 2
def baseEnd_5982247 : Nat := 3071768104917361164800653

theorem tailTrace_5982247 : CollatzResearch.WordTrace tailWord_5982247 prefixEnd_5982247 3071768104917361164800653 := by
  unfold tailWord_5982247
  simp only [CollatzResearch.WordTrace]
  refine ⟨218190473158348280292096995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145460315438898853528064663 218190473158348280292096995)
  ·
    refine ⟨327285709737522420438145493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218190473158348280292096995 327285709737522420438145493)
    ·
      refine ⟨7670758821973181729019035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 327285709737522420438145493 7670758821973181729019035)
      ·
        refine ⟨11506138232959772593528553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7670758821973181729019035 11506138232959772593528553)
        ·
          refine ⟨8629603674719829445146415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11506138232959772593528553 8629603674719829445146415)
          ·
            refine ⟨12944405512079744167719623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8629603674719829445146415 12944405512079744167719623)
            ·
              refine ⟨19416608268119616251579435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12944405512079744167719623 19416608268119616251579435)
              ·
                refine ⟨29124912402179424377369153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19416608268119616251579435 29124912402179424377369153)
                ·
                  refine ⟨21843684301634568283026865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29124912402179424377369153 21843684301634568283026865)
                  ·
                    refine ⟨16382763226225926212270149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21843684301634568283026865 16382763226225926212270149)
                    ·
                      refine ⟨3071768104917361164800653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16382763226225926212270149 3071768104917361164800653)
                      ·
                        rfl

theorem cell23_5982247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_5982247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5982247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5982247 prefixEnd_5982247 := by exact prefixLift 5982247
  have htrace : WordTrace (prefixWord ++ tailWord_5982247) baseStart_5982247 baseEnd_5982247 := by
    simpa [prefixWord, tailWord_5982247, baseEnd_5982247] using wordTrace_append hprefix tailTrace_5982247
  have hstable : (prefixWord ++ tailWord_5982247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5982247).length < 2 ^ (prefixWord ++ tailWord_5982247).sum := by decide
  have hdescent : baseEnd_5982247 < baseStart_5982247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5982247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5982250 : List Nat := [3, 1, 4, 1, 2, 1, 1, 1, 1, 5, 3]
def baseStart_5982250 : Nat := 118140960795 + 5982250 * 2 ^ 59
def prefixEnd_5982250 : Nat := 4983230072969 + 3 ^ 40 * 5982250 * 2
def baseEnd_5982250 : Nat := 3071769645359324653063139

theorem tailTrace_5982250 : CollatzResearch.WordTrace tailWord_5982250 prefixEnd_5982250 3071769645359324653063139 := by
  unfold tailWord_5982250
  simp only [CollatzResearch.WordTrace]
  refine ⟨54547645644334352951114051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145460388384891607869637469 54547645644334352951114051)
  ·
    refine ⟨81821468466501529426671077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54547645644334352951114051 81821468466501529426671077)
    ·
      refine ⟨15341525337469036767500827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81821468466501529426671077 15341525337469036767500827)
      ·
        refine ⟨23012288006203555151251241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15341525337469036767500827 23012288006203555151251241)
        ·
          refine ⟨17259216004652666363438431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23012288006203555151251241 17259216004652666363438431)
          ·
            refine ⟨25888824006978999545157647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17259216004652666363438431 25888824006978999545157647)
            ·
              refine ⟨38833236010468499317736471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25888824006978999545157647 38833236010468499317736471)
              ·
                refine ⟨58249854015702748976604707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38833236010468499317736471 58249854015702748976604707)
                ·
                  refine ⟨87374781023554123464907061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58249854015702748976604707 87374781023554123464907061)
                  ·
                    refine ⟨8191385720958199074835037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 87374781023554123464907061 8191385720958199074835037)
                    ·
                      refine ⟨3071769645359324653063139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8191385720958199074835037 3071769645359324653063139)
                      ·
                        rfl

theorem cell23_5982250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_5982250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5982250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5982250 prefixEnd_5982250 := by exact prefixLift 5982250
  have htrace : WordTrace (prefixWord ++ tailWord_5982250) baseStart_5982250 baseEnd_5982250 := by
    simpa [prefixWord, tailWord_5982250, baseEnd_5982250] using wordTrace_append hprefix tailTrace_5982250
  have hstable : (prefixWord ++ tailWord_5982250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5982250).length < 2 ^ (prefixWord ++ tailWord_5982250).sum := by decide
  have hdescent : baseEnd_5982250 < baseStart_5982250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5982250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5982410 : List Nat := [3, 1, 2, 1, 3, 1, 1, 2, 3, 2, 4]
def baseStart_5982410 : Nat := 118140960795 + 5982410 * 2 ^ 59
def prefixEnd_5982410 : Nat := 4983230072969 + 3 ^ 40 * 5982410 * 2
def baseEnd_5982410 : Nat := 3071851802264044027062403

theorem tailTrace_5982410 : CollatzResearch.WordTrace tailWord_5982410 prefixEnd_5982410 3071851802264044027062403 := by
  unfold tailWord_5982410
  simp only [CollatzResearch.WordTrace]
  refine ⟨54549104564189439782570171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145464278837838506086853789 54549104564189439782570171)
  ·
    refine ⟨81823656846284159673855257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54549104564189439782570171 81823656846284159673855257)
    ·
      refine ⟨61367742634713119755391443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81823656846284159673855257 61367742634713119755391443)
      ·
        refine ⟨92051613952069679633087165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61367742634713119755391443 92051613952069679633087165)
        ·
          refine ⟨34519355232026129862407687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92051613952069679633087165 34519355232026129862407687)
          ·
            refine ⟨51779032848039194793611531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34519355232026129862407687 51779032848039194793611531)
            ·
              refine ⟨77668549272058792190417297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51779032848039194793611531 77668549272058792190417297)
              ·
                refine ⟨58251411954044094142812973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77668549272058792190417297 58251411954044094142812973)
                ·
                  refine ⟨21844279482766535303554865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58251411954044094142812973 21844279482766535303554865)
                  ·
                    refine ⟨16383209612074901477666149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21844279482766535303554865 16383209612074901477666149)
                    ·
                      refine ⟨3071851802264044027062403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16383209612074901477666149 3071851802264044027062403)
                      ·
                        rfl

theorem cell23_5982410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_5982410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5982410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5982410 prefixEnd_5982410 := by exact prefixLift 5982410
  have htrace : WordTrace (prefixWord ++ tailWord_5982410) baseStart_5982410 baseEnd_5982410 := by
    simpa [prefixWord, tailWord_5982410, baseEnd_5982410] using wordTrace_append hprefix tailTrace_5982410
  have hstable : (prefixWord ++ tailWord_5982410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5982410).length < 2 ^ (prefixWord ++ tailWord_5982410).sum := by decide
  have hdescent : baseEnd_5982410 < baseStart_5982410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5982410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5982437 : List Nat := [1, 3, 1, 4, 2, 2, 3, 7]
def baseStart_5982437 : Nat := 118140960795 + 5982437 * 2 ^ 59
def prefixEnd_5982437 : Nat := 4983230072969 + 3 ^ 40 * 5982437 * 2
def baseEnd_5982437 : Nat := 113772802453396867460177

theorem tailTrace_5982437 : CollatzResearch.WordTrace tailWord_5982437 prefixEnd_5982437 113772802453396867460177 := by
  unfold tailWord_5982437
  simp only [CollatzResearch.WordTrace]
  refine ⟨218197403027659942741513565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145464935351773295161009043 218197403027659942741513565)
  ·
    refine ⟨81824026135372478528067587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218197403027659942741513565 81824026135372478528067587)
    ·
      refine ⟨122736039203058717792101381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81824026135372478528067587 122736039203058717792101381)
      ·
        refine ⟨23013007350573509586019009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122736039203058717792101381 23013007350573509586019009)
        ·
          refine ⟨17259755512930132189514257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23013007350573509586019009 17259755512930132189514257)
          ·
            refine ⟨12944816634697599142135693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17259755512930132189514257 12944816634697599142135693)
            ·
              refine ⟨4854306238011599678300885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12944816634697599142135693 4854306238011599678300885)
              ·
                refine ⟨113772802453396867460177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4854306238011599678300885 113772802453396867460177)
                ·
                  rfl

theorem cell23_5982437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 7].length) (baseStart_5982437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5982437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5982437 prefixEnd_5982437 := by exact prefixLift 5982437
  have htrace : WordTrace (prefixWord ++ tailWord_5982437) baseStart_5982437 baseEnd_5982437 := by
    simpa [prefixWord, tailWord_5982437, baseEnd_5982437] using wordTrace_append hprefix tailTrace_5982437
  have hstable : (prefixWord ++ tailWord_5982437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5982437).length < 2 ^ (prefixWord ++ tailWord_5982437).sum := by decide
  have hdescent : baseEnd_5982437 < baseStart_5982437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5982437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5982447 : List Nat := [1, 1, 2, 1, 6, 1, 2, 2, 1, 3, 3]
def baseStart_5982447 : Nat := 118140960795 + 5982447 * 2 ^ 59
def prefixEnd_5982447 : Nat := 4983230072969 + 3 ^ 40 * 5982447 * 2
def baseEnd_5982447 : Nat := 3071870801048260382299733

theorem tailTrace_5982447 : CollatzResearch.WordTrace tailWord_5982447 prefixEnd_5982447 3071870801048260382299733 := by
  unfold tailWord_5982447
  simp only [CollatzResearch.WordTrace]
  refine ⟨218197767757623714449377595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145465178505082476299585063 218197767757623714449377595)
  ·
    refine ⟨327296651636435571674066393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218197767757623714449377595 327296651636435571674066393)
    ·
      refine ⟨245472488727326678755549795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327296651636435571674066393 245472488727326678755549795)
      ·
        refine ⟨368208733090990018133324693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245472488727326678755549795 368208733090990018133324693)
        ·
          refine ⟨17259784363640157099999595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 368208733090990018133324693 17259784363640157099999595)
          ·
            refine ⟨25889676545460235649999393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17259784363640157099999595 25889676545460235649999393)
            ·
              refine ⟨19417257409095176737499545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25889676545460235649999393 19417257409095176737499545)
              ·
                refine ⟨14562943056821382553124659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19417257409095176737499545 14562943056821382553124659)
                ·
                  refine ⟨21844414585232073829686989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14562943056821382553124659 21844414585232073829686989)
                  ·
                    refine ⟨8191655469462027686132621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21844414585232073829686989 8191655469462027686132621)
                    ·
                      refine ⟨3071870801048260382299733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8191655469462027686132621 3071870801048260382299733)
                      ·
                        rfl

theorem cell23_5982447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 3, 3].length) (baseStart_5982447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5982447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5982447 prefixEnd_5982447 := by exact prefixLift 5982447
  have htrace : WordTrace (prefixWord ++ tailWord_5982447) baseStart_5982447 baseEnd_5982447 := by
    simpa [prefixWord, tailWord_5982447, baseEnd_5982447] using wordTrace_append hprefix tailTrace_5982447
  have hstable : (prefixWord ++ tailWord_5982447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5982447).length < 2 ^ (prefixWord ++ tailWord_5982447).sum := by decide
  have hdescent : baseEnd_5982447 < baseStart_5982447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5982447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5982457 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 5, 3, 2]
def baseStart_5982457 : Nat := 118140960795 + 5982457 * 2 ^ 59
def prefixEnd_5982457 : Nat := 4983230072969 + 3 ^ 40 * 5982457 * 2
def baseEnd_5982457 : Nat := 3071875935854805343174687

theorem tailTrace_5982457 : CollatzResearch.WordTrace tailWord_5982457 prefixEnd_5982457 3071875935854805343174687 := by
  unfold tailWord_5982457
  simp only [CollatzResearch.WordTrace]
  refine ⟨218198132487587486157241625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145465421658391657438161083 218198132487587486157241625)
  ·
    refine ⟨163648599365690614617931219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218198132487587486157241625 163648599365690614617931219)
    ·
      refine ⟨245472899048535921926896829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163648599365690614617931219 245472899048535921926896829)
      ·
        refine ⟨92052337143200970722586311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245472899048535921926896829 92052337143200970722586311)
        ·
          refine ⟨138078505714801456083879467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92052337143200970722586311 138078505714801456083879467)
          ·
            refine ⟨207117758572202184125819201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138078505714801456083879467 207117758572202184125819201)
            ·
              refine ⟨155338318929151638094364401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207117758572202184125819201 155338318929151638094364401)
              ·
                refine ⟨116503739196863728570773301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155338318929151638094364401 116503739196863728570773301)
                ·
                  refine ⟨10922225549705974553509997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 116503739196863728570773301 10922225549705974553509997)
                  ·
                    refine ⟨4095834581139740457566249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10922225549705974553509997 4095834581139740457566249)
                    ·
                      refine ⟨3071875935854805343174687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4095834581139740457566249 3071875935854805343174687)
                      ·
                        rfl

theorem cell23_5982457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5, 3, 2].length) (baseStart_5982457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5982457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5982457 prefixEnd_5982457 := by exact prefixLift 5982457
  have htrace : WordTrace (prefixWord ++ tailWord_5982457) baseStart_5982457 baseEnd_5982457 := by
    simpa [prefixWord, tailWord_5982457, baseEnd_5982457] using wordTrace_append hprefix tailTrace_5982457
  have hstable : (prefixWord ++ tailWord_5982457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5982457).length < 2 ^ (prefixWord ++ tailWord_5982457).sum := by decide
  have hdescent : baseEnd_5982457 < baseStart_5982457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5982457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5982464 : List Nat := [2, 1, 1, 2, 1, 1, 7, 2, 2, 1, 3]
def baseStart_5982464 : Nat := 118140960795 + 5982464 * 2 ^ 59
def prefixEnd_5982464 : Nat := 4983230072969 + 3 ^ 40 * 5982464 * 2
def baseEnd_5982464 : Nat := 3071879530219386815787155

theorem tailTrace_5982464 : CollatzResearch.WordTrace tailWord_5982464 prefixEnd_5982464 3071879530219386815787155 := by
  unfold tailWord_5982464
  simp only [CollatzResearch.WordTrace]
  refine ⟨109099193899281063176373223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145465591865708084235164297 109099193899281063176373223)
  ·
    refine ⟨163648790848921594764559835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109099193899281063176373223 163648790848921594764559835)
    ·
      refine ⟨245473186273382392146839753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163648790848921594764559835 245473186273382392146839753)
      ·
        refine ⟨184104889705036794110129815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245473186273382392146839753 184104889705036794110129815)
        ·
          refine ⟨276157334557555191165194723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184104889705036794110129815 276157334557555191165194723)
          ·
            refine ⟨414236001836332786747792085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276157334557555191165194723 414236001836332786747792085)
            ·
              refine ⟨9708656293039049689401377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 414236001836332786747792085 9708656293039049689401377)
              ·
                refine ⟨7281492219779287267051033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9708656293039049689401377 7281492219779287267051033)
                ·
                  refine ⟨5461119164834465450288275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7281492219779287267051033 5461119164834465450288275)
                  ·
                    refine ⟨8191678747251698175432413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5461119164834465450288275 8191678747251698175432413)
                    ·
                      refine ⟨3071879530219386815787155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8191678747251698175432413 3071879530219386815787155)
                      ·
                        rfl

theorem cell23_5982464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2, 2, 1, 3].length) (baseStart_5982464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5982464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5982464 prefixEnd_5982464 := by exact prefixLift 5982464
  have htrace : WordTrace (prefixWord ++ tailWord_5982464) baseStart_5982464 baseEnd_5982464 := by
    simpa [prefixWord, tailWord_5982464, baseEnd_5982464] using wordTrace_append hprefix tailTrace_5982464
  have hstable : (prefixWord ++ tailWord_5982464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5982464).length < 2 ^ (prefixWord ++ tailWord_5982464).sum := by decide
  have hdescent : baseEnd_5982464 < baseStart_5982464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5982464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5982481 : List Nat := [1, 2, 2, 1, 1, 6, 3, 1, 2, 1, 3]
def baseStart_5982481 : Nat := 118140960795 + 5982481 * 2 ^ 59
def prefixEnd_5982481 : Nat := 4983230072969 + 3 ^ 40 * 5982481 * 2
def baseEnd_5982481 : Nat := 3071888259390513249274577

theorem tailTrace_5982481 : CollatzResearch.WordTrace tailWord_5982481 prefixEnd_5982481 3071888259390513249274577 := by
  unfold tailWord_5982481
  simp only [CollatzResearch.WordTrace]
  refine ⟨218199007839500538256115297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145466005226333692170743531 218199007839500538256115297)
  ·
    refine ⟨163649255879625403692086473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218199007839500538256115297 163649255879625403692086473)
    ·
      refine ⟨122736941909719052769064855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163649255879625403692086473 122736941909719052769064855)
      ·
        refine ⟨184105412864578579153597283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122736941909719052769064855 184105412864578579153597283)
        ·
          refine ⟨276158119296867868730395925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184105412864578579153597283 276158119296867868730395925)
          ·
            refine ⟨12944911842040681346737309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 276158119296867868730395925 12944911842040681346737309)
            ·
              refine ⟨4854341940765255505026491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12944911842040681346737309 4854341940765255505026491)
              ·
                refine ⟨7281512911147883257539737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4854341940765255505026491 7281512911147883257539737)
                ·
                  refine ⟨5461134683360912443154803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7281512911147883257539737 5461134683360912443154803)
                  ·
                    refine ⟨8191702025041368664732205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5461134683360912443154803 8191702025041368664732205)
                    ·
                      refine ⟨3071888259390513249274577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8191702025041368664732205 3071888259390513249274577)
                      ·
                        rfl

theorem cell23_5982481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 1, 2, 1, 3].length) (baseStart_5982481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5982481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5982481 prefixEnd_5982481 := by exact prefixLift 5982481
  have htrace : WordTrace (prefixWord ++ tailWord_5982481) baseStart_5982481 baseEnd_5982481 := by
    simpa [prefixWord, tailWord_5982481, baseEnd_5982481] using wordTrace_append hprefix tailTrace_5982481
  have hstable : (prefixWord ++ tailWord_5982481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5982481).length < 2 ^ (prefixWord ++ tailWord_5982481).sum := by decide
  have hdescent : baseEnd_5982481 < baseStart_5982481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5982481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5982494 : List Nat := [4, 3, 2, 1, 1, 1, 1, 1, 2, 2, 5]
def baseStart_5982494 : Nat := 118140960795 + 5982494 * 2 ^ 59
def prefixEnd_5982494 : Nat := 4983230072969 + 3 ^ 40 * 5982494 * 2
def baseEnd_5982494 : Nat := 3071894934639021698412017

theorem tailTrace_5982494 : CollatzResearch.WordTrace tailWord_5982494 prefixEnd_5982494 3071894934639021698412017 := by
  unfold tailWord_5982494
  simp only [CollatzResearch.WordTrace]
  refine ⟨27274935248556680184542317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145466321325635627650892357 27274935248556680184542317)
  ·
    refine ⟨10228100718208755069203369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27274935248556680184542317 10228100718208755069203369)
    ·
      refine ⟨7671075538656566301902527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10228100718208755069203369 7671075538656566301902527)
      ·
        refine ⟨11506613307984849452853791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7671075538656566301902527 11506613307984849452853791)
        ·
          refine ⟨17259919961977274179280687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11506613307984849452853791 17259919961977274179280687)
          ·
            refine ⟨25889879942965911268921031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17259919961977274179280687 25889879942965911268921031)
            ·
              refine ⟨38834819914448866903381547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25889879942965911268921031 38834819914448866903381547)
              ·
                refine ⟨58252229871673300355072321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38834819914448866903381547 58252229871673300355072321)
                ·
                  refine ⟨43689172403754975266304241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58252229871673300355072321 43689172403754975266304241)
                  ·
                    refine ⟨32766879302816231449728181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43689172403754975266304241 32766879302816231449728181)
                    ·
                      refine ⟨3071894934639021698412017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32766879302816231449728181 3071894934639021698412017)
                      ·
                        rfl

theorem cell23_5982494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_5982494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5982494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5982494 prefixEnd_5982494 := by exact prefixLift 5982494
  have htrace : WordTrace (prefixWord ++ tailWord_5982494) baseStart_5982494 baseEnd_5982494 := by
    simpa [prefixWord, tailWord_5982494, baseEnd_5982494] using wordTrace_append hprefix tailTrace_5982494
  have hstable : (prefixWord ++ tailWord_5982494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5982494).length < 2 ^ (prefixWord ++ tailWord_5982494).sum := by decide
  have hdescent : baseEnd_5982494 < baseStart_5982494 := by decide
  rcases family_descends (prefixWord ++ tailWord_5982494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5982521 : List Nat := [1, 2, 1, 6, 1, 1, 2, 1, 4, 2, 2]
def baseStart_5982521 : Nat := 118140960795 + 5982521 * 2 ^ 59
def prefixEnd_5982521 : Nat := 4983230072969 + 3 ^ 40 * 5982521 * 2
def baseEnd_5982521 : Nat := 3071908798616693092774393

theorem tailTrace_5982521 : CollatzResearch.WordTrace tailWord_5982521 prefixEnd_5982521 3071908798616693092774393 := by
  unfold tailWord_5982521
  simp only [CollatzResearch.WordTrace]
  refine ⟨218200466759355625087571417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145466977839570416725047611 218200466759355625087571417)
  ·
    refine ⟨163650350069516718815678563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218200466759355625087571417 163650350069516718815678563)
    ·
      refine ⟨245475525104275078223517845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163650350069516718815678563 245475525104275078223517845)
      ·
        refine ⟨11506665239262894291727399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 245475525104275078223517845 11506665239262894291727399)
        ·
          refine ⟨17259997858894341437591099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11506665239262894291727399 17259997858894341437591099)
          ·
            refine ⟨25889996788341512156386649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17259997858894341437591099 25889996788341512156386649)
            ·
              refine ⟨19417497591256134117289987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25889996788341512156386649 19417497591256134117289987)
              ·
                refine ⟨29126246386884201175934981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19417497591256134117289987 29126246386884201175934981)
                ·
                  refine ⟨5461171197540787720487809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29126246386884201175934981 5461171197540787720487809)
                  ·
                    refine ⟨4095878398155590790365857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5461171197540787720487809 4095878398155590790365857)
                    ·
                      refine ⟨3071908798616693092774393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4095878398155590790365857 3071908798616693092774393)
                      ·
                        rfl

theorem cell23_5982521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_5982521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5982521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5982521 prefixEnd_5982521 := by exact prefixLift 5982521
  have htrace : WordTrace (prefixWord ++ tailWord_5982521) baseStart_5982521 baseEnd_5982521 := by
    simpa [prefixWord, tailWord_5982521, baseEnd_5982521] using wordTrace_append hprefix tailTrace_5982521
  have hstable : (prefixWord ++ tailWord_5982521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5982521).length < 2 ^ (prefixWord ++ tailWord_5982521).sum := by decide
  have hdescent : baseEnd_5982521 < baseStart_5982521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5982521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5982532 : List Nat := [2, 3, 4, 1, 3, 1, 2, 1, 2, 1, 3]
def baseStart_5982532 : Nat := 118140960795 + 5982532 * 2 ^ 59
def prefixEnd_5982532 : Nat := 4983230072969 + 3 ^ 40 * 5982532 * 2
def baseEnd_5982532 : Nat := 3071914446903892549736843

theorem tailTrace_5982532 : CollatzResearch.WordTrace tailWord_5982532 prefixEnd_5982532 3071914446903892549736843 := by
  unfold tailWord_5982532
  simp only [CollatzResearch.WordTrace]
  refine ⟨109100433981157886983110925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145467245308210515977481233 109100433981157886983110925)
  ·
    refine ⟨40912662742934207618666597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109100433981157886983110925 40912662742934207618666597)
    ·
      refine ⟨7671124264300163928499987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40912662742934207618666597 7671124264300163928499987)
      ·
        refine ⟨11506686396450245892749981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7671124264300163928499987 11506686396450245892749981)
        ·
          refine ⟨4315007398668842209781243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11506686396450245892749981 4315007398668842209781243)
          ·
            refine ⟨6472511098003263314671865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4315007398668842209781243 6472511098003263314671865)
            ·
              refine ⟨4854383323502447486003899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6472511098003263314671865 4854383323502447486003899)
              ·
                refine ⟨7281574985253671229005849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4854383323502447486003899 7281574985253671229005849)
                ·
                  refine ⟨5461181238940253421754387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7281574985253671229005849 5461181238940253421754387)
                  ·
                    refine ⟨8191771858410380132631581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5461181238940253421754387 8191771858410380132631581)
                    ·
                      refine ⟨3071914446903892549736843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8191771858410380132631581 3071914446903892549736843)
                      ·
                        rfl

theorem cell23_5982532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_5982532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5982532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5982532 prefixEnd_5982532 := by exact prefixLift 5982532
  have htrace : WordTrace (prefixWord ++ tailWord_5982532) baseStart_5982532 baseEnd_5982532 := by
    simpa [prefixWord, tailWord_5982532, baseEnd_5982532] using wordTrace_append hprefix tailTrace_5982532
  have hstable : (prefixWord ++ tailWord_5982532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5982532).length < 2 ^ (prefixWord ++ tailWord_5982532).sum := by decide
  have hdescent : baseEnd_5982532 < baseStart_5982532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5982532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5982547 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 4, 5, 2]
def baseStart_5982547 : Nat := 118140960795 + 5982547 * 2 ^ 59
def prefixEnd_5982547 : Nat := 4983230072969 + 3 ^ 40 * 5982547 * 2
def baseEnd_5982547 : Nat := 3071922149113709991049273

theorem tailTrace_5982547 : CollatzResearch.WordTrace tailWord_5982547 prefixEnd_5982547 3071922149113709991049273 := by
  unfold tailWord_5982547
  simp only [CollatzResearch.WordTrace]
  refine ⟨218201415057261431528017895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145467610038174287685345263 218201415057261431528017895)
  ·
    refine ⟨327302122585892147292026843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218201415057261431528017895 327302122585892147292026843)
    ·
      refine ⟨490953183878838220938040265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327302122585892147292026843 490953183878838220938040265)
      ·
        refine ⟨368214887909128665703530199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 490953183878838220938040265 368214887909128665703530199)
        ·
          refine ⟨552322331863692998555295299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368214887909128665703530199 552322331863692998555295299)
          ·
            refine ⟨828483497795539497832942949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552322331863692998555295299 828483497795539497832942949)
            ·
              refine ⟨155340655836663655843676803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 828483497795539497832942949 155340655836663655843676803)
              ·
                refine ⟨233010983754995483765515205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155340655836663655843676803 233010983754995483765515205)
                ·
                  refine ⟨43689559454061653206034101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 233010983754995483765515205 43689559454061653206034101)
                  ·
                    refine ⟨4095896198818279988065697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43689559454061653206034101 4095896198818279988065697)
                    ·
                      refine ⟨3071922149113709991049273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4095896198818279988065697 3071922149113709991049273)
                      ·
                        rfl

theorem cell23_5982547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 5, 2].length) (baseStart_5982547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5982547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5982547 prefixEnd_5982547 := by exact prefixLift 5982547
  have htrace : WordTrace (prefixWord ++ tailWord_5982547) baseStart_5982547 baseEnd_5982547 := by
    simpa [prefixWord, tailWord_5982547, baseEnd_5982547] using wordTrace_append hprefix tailTrace_5982547
  have hstable : (prefixWord ++ tailWord_5982547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5982547).length < 2 ^ (prefixWord ++ tailWord_5982547).sum := by decide
  have hdescent : baseEnd_5982547 < baseStart_5982547 := by decide
  rcases family_descends (prefixWord ++ tailWord_5982547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5982567 : List Nat := [1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 5]
def baseStart_5982567 : Nat := 118140960795 + 5982567 * 2 ^ 59
def prefixEnd_5982567 : Nat := 4983230072969 + 3 ^ 40 * 5982567 * 2
def baseEnd_5982567 : Nat := 3071932418726799912799181

theorem tailTrace_5982567 : CollatzResearch.WordTrace tailWord_5982567 prefixEnd_5982567 3071932418726799912799181 := by
  unfold tailWord_5982567
  simp only [CollatzResearch.WordTrace]
  refine ⟨218202144517188974943745955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145468096344792649962497303 218202144517188974943745955)
  ·
    refine ⟨327303216775783462415618933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218202144517188974943745955 327303216775783462415618933)
    ·
      refine ⟨30684676572729699601464275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 327303216775783462415618933 30684676572729699601464275)
      ·
        refine ⟨46027014859094549402196413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30684676572729699601464275 46027014859094549402196413)
        ·
          refine ⟨17260130572160456025823655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46027014859094549402196413 17260130572160456025823655)
          ·
            refine ⟨25890195858240684038735483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17260130572160456025823655 25890195858240684038735483)
            ·
              refine ⟨38835293787361026058103225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25890195858240684038735483 38835293787361026058103225)
              ·
                refine ⟨29126470340520769543577419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38835293787361026058103225 29126470340520769543577419)
                ·
                  refine ⟨43689705510781154315366129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29126470340520769543577419 43689705510781154315366129)
                  ·
                    refine ⟨32767279133085865736524597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43689705510781154315366129 32767279133085865736524597)
                    ·
                      refine ⟨3071932418726799912799181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32767279133085865736524597 3071932418726799912799181)
                      ·
                        rfl

theorem cell23_5982567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_5982567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5982567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5982567 prefixEnd_5982567 := by exact prefixLift 5982567
  have htrace : WordTrace (prefixWord ++ tailWord_5982567) baseStart_5982567 baseEnd_5982567 := by
    simpa [prefixWord, tailWord_5982567, baseEnd_5982567] using wordTrace_append hprefix tailTrace_5982567
  have hstable : (prefixWord ++ tailWord_5982567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5982567).length < 2 ^ (prefixWord ++ tailWord_5982567).sum := by decide
  have hdescent : baseEnd_5982567 < baseStart_5982567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5982567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5982597 : List Nat := [1, 3, 1, 1, 3, 1, 1, 4, 1, 4, 3]
def baseStart_5982597 : Nat := 118140960795 + 5982597 * 2 ^ 59
def prefixEnd_5982597 : Nat := 4983230072969 + 3 ^ 40 * 5982597 * 2
def baseEnd_5982597 : Nat := 3071947823146434795424043

theorem tailTrace_5982597 : CollatzResearch.WordTrace tailWord_5982597 prefixEnd_5982597 3071947823146434795424043 := by
  unfold tailWord_5982597
  simp only [CollatzResearch.WordTrace]
  refine ⟨218203238707080290067338045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145468825804720193378225363 218203238707080290067338045)
  ·
    refine ⟨81826214515155108775251767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218203238707080290067338045 81826214515155108775251767)
    ·
      refine ⟨122739321772732663162877651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81826214515155108775251767 122739321772732663162877651)
      ·
        refine ⟨184108982659098994744316477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122739321772732663162877651 184108982659098994744316477)
        ·
          refine ⟨69040868497162123029118679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184108982659098994744316477 69040868497162123029118679)
          ·
            refine ⟨103561302745743184543678019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69040868497162123029118679 103561302745743184543678019)
            ·
              refine ⟨155341954118614776815517029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103561302745743184543678019 155341954118614776815517029)
              ·
                refine ⟨29126616397240270652909443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 155341954118614776815517029 29126616397240270652909443)
                ·
                  refine ⟨43689924595860405979364165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29126616397240270652909443 43689924595860405979364165)
                  ·
                    refine ⟨8191860861723826121130781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43689924595860405979364165 8191860861723826121130781)
                    ·
                      refine ⟨3071947823146434795424043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8191860861723826121130781 3071947823146434795424043)
                      ·
                        rfl

theorem cell23_5982597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 4, 3].length) (baseStart_5982597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5982597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5982597 prefixEnd_5982597 := by exact prefixLift 5982597
  have htrace : WordTrace (prefixWord ++ tailWord_5982597) baseStart_5982597 baseEnd_5982597 := by
    simpa [prefixWord, tailWord_5982597, baseEnd_5982597] using wordTrace_append hprefix tailTrace_5982597
  have hstable : (prefixWord ++ tailWord_5982597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5982597).length < 2 ^ (prefixWord ++ tailWord_5982597).sum := by decide
  have hdescent : baseEnd_5982597 < baseStart_5982597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5982597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5982604 : List Nat := [2, 2, 1, 2, 1, 5, 1, 2, 3, 4]
def baseStart_5982604 : Nat := 118140960795 + 5982604 * 2 ^ 59
def prefixEnd_5982604 : Nat := 4983230072969 + 3 ^ 40 * 5982604 * 2
def baseEnd_5982604 : Nat := 1023983805837005422678837

theorem tailTrace_5982604 : CollatzResearch.WordTrace tailWord_5982604 prefixEnd_5982604 1023983805837005422678837 := by
  unfold tailWord_5982604
  simp only [CollatzResearch.WordTrace]
  refine ⟨109101747009027465131421433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145468996012036620175228577 109101747009027465131421433)
  ·
    refine ⟨81826310256770598848566075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109101747009027465131421433 81826310256770598848566075)
    ·
      refine ⟨122739465385155898272849113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81826310256770598848566075 122739465385155898272849113)
      ·
        refine ⟨92054599038866923704636835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122739465385155898272849113 92054599038866923704636835)
        ·
          refine ⟨138081898558300385556955253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92054599038866923704636835 138081898558300385556955253)
          ·
            refine ⟨12945177989840661145964555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 138081898558300385556955253 12945177989840661145964555)
            ·
              refine ⟨19417766984760991718946833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12945177989840661145964555 19417766984760991718946833)
              ·
                refine ⟨14563325238570743789210125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19417766984760991718946833 14563325238570743789210125)
                ·
                  refine ⟨5461246964464028920953797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14563325238570743789210125 5461246964464028920953797)
                  ·
                    refine ⟨1023983805837005422678837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5461246964464028920953797 1023983805837005422678837)
                    ·
                      rfl

theorem cell23_5982604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 3, 4].length) (baseStart_5982604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5982604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5982604 prefixEnd_5982604 := by exact prefixLift 5982604
  have htrace : WordTrace (prefixWord ++ tailWord_5982604) baseStart_5982604 baseEnd_5982604 := by
    simpa [prefixWord, tailWord_5982604, baseEnd_5982604] using wordTrace_append hprefix tailTrace_5982604
  have hstable : (prefixWord ++ tailWord_5982604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5982604).length < 2 ^ (prefixWord ++ tailWord_5982604).sum := by decide
  have hdescent : baseEnd_5982604 < baseStart_5982604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5982604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5982664 : List Nat := [2, 1, 3, 1, 3, 2, 1, 4, 1, 5]
def baseStart_5982664 : Nat := 118140960795 + 5982664 * 2 ^ 59
def prefixEnd_5982664 : Nat := 4983230072969 + 3 ^ 40 * 5982664 * 2
def baseEnd_5982664 : Nat := 1023994075450095344428745

theorem tailTrace_5982664 : CollatzResearch.WordTrace tailWord_5982664 prefixEnd_5982664 1023994075450095344428745 := by
  unfold tailWord_5982664
  simp only [CollatzResearch.WordTrace]
  refine ⟨109102841198918780255013523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145470454931891707006684697 109102841198918780255013523)
  ·
    refine ⟨163654261798378170382520285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109102841198918780255013523 163654261798378170382520285)
    ·
      refine ⟨61370348174391813893445107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163654261798378170382520285 61370348174391813893445107)
      ·
        refine ⟨92055522261587720840167661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61370348174391813893445107 92055522261587720840167661)
        ·
          refine ⟨34520820848095395315062873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92055522261587720840167661 34520820848095395315062873)
          ·
            refine ⟨25890615636071546486297155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34520820848095395315062873 25890615636071546486297155)
            ·
              refine ⟨38835923454107319729445733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25890615636071546486297155 38835923454107319729445733)
              ·
                refine ⟨7281735647645122449271075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38835923454107319729445733 7281735647645122449271075)
                ·
                  refine ⟨10922603471467683673906613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7281735647645122449271075 10922603471467683673906613)
                  ·
                    refine ⟨1023994075450095344428745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10922603471467683673906613 1023994075450095344428745)
                    ·
                      rfl

theorem cell23_5982664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4, 1, 5].length) (baseStart_5982664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5982664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5982664 prefixEnd_5982664 := by exact prefixLift 5982664
  have htrace : WordTrace (prefixWord ++ tailWord_5982664) baseStart_5982664 baseEnd_5982664 := by
    simpa [prefixWord, tailWord_5982664, baseEnd_5982664] using wordTrace_append hprefix tailTrace_5982664
  have hstable : (prefixWord ++ tailWord_5982664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5982664).length < 2 ^ (prefixWord ++ tailWord_5982664).sum := by decide
  have hdescent : baseEnd_5982664 < baseStart_5982664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5982664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5982695 : List Nat := [1, 1, 5, 2, 1, 1, 5, 2, 1, 1, 3]
def baseStart_5982695 : Nat := 118140960795 + 5982695 * 2 ^ 59
def prefixEnd_5982695 : Nat := 4983230072969 + 3 ^ 40 * 5982695 * 2
def baseEnd_5982695 : Nat := 3071998144250575411998593

theorem tailTrace_5982695 : CollatzResearch.WordTrace tailWord_5982695 prefixEnd_5982695 3071998144250575411998593 := by
  unfold tailWord_5982695
  simp only [CollatzResearch.WordTrace]
  refine ⟨218206813060725252804405539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145471208707150168536270359 218206813060725252804405539)
  ·
    refine ⟨327310219591087879206608309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218206813060725252804405539 327310219591087879206608309)
    ·
      refine ⟨30685333086664488675619529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 327310219591087879206608309 30685333086664488675619529)
      ·
        refine ⟨23013999814998366506714647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30685333086664488675619529 23013999814998366506714647)
        ·
          refine ⟨34520999722497549760071971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23013999814998366506714647 34520999722497549760071971)
          ·
            refine ⟨51781499583746324640107957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34520999722497549760071971 51781499583746324640107957)
            ·
              refine ⟨4854515585976217935010121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51781499583746324640107957 4854515585976217935010121)
              ·
                refine ⟨3640886689482163451257591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4854515585976217935010121 3640886689482163451257591)
                ·
                  refine ⟨5461330034223245176886387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3640886689482163451257591 5461330034223245176886387)
                  ·
                    refine ⟨8191995051334867765329581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5461330034223245176886387 8191995051334867765329581)
                    ·
                      refine ⟨3071998144250575411998593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8191995051334867765329581 3071998144250575411998593)
                      ·
                        rfl

theorem cell23_5982695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_5982695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5982695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5982695 prefixEnd_5982695 := by exact prefixLift 5982695
  have htrace : WordTrace (prefixWord ++ tailWord_5982695) baseStart_5982695 baseEnd_5982695 := by
    simpa [prefixWord, tailWord_5982695, baseEnd_5982695] using wordTrace_append hprefix tailTrace_5982695
  have hstable : (prefixWord ++ tailWord_5982695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5982695).length < 2 ^ (prefixWord ++ tailWord_5982695).sum := by decide
  have hdescent : baseEnd_5982695 < baseStart_5982695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5982695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5982697 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 5, 2, 4]
def baseStart_5982697 : Nat := 118140960795 + 5982697 * 2 ^ 59
def prefixEnd_5982697 : Nat := 4983230072969 + 3 ^ 40 * 5982697 * 2
def baseEnd_5982697 : Nat := 3071999171211884404173583

theorem tailTrace_5982697 : CollatzResearch.WordTrace tailWord_5982697 prefixEnd_5982697 3071999171211884404173583 := by
  unfold tailWord_5982697
  simp only [CollatzResearch.WordTrace]
  refine ⟨218206886006718007145978345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145471257337812004763985563 218206886006718007145978345)
  ·
    refine ⟨163655164505038505359483759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218206886006718007145978345 163655164505038505359483759)
    ·
      refine ⟨245482746757557758039225639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163655164505038505359483759 245482746757557758039225639)
      ·
        refine ⟨368224120136336637058838459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245482746757557758039225639 368224120136336637058838459)
        ·
          refine ⟨552336180204504955588257689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368224120136336637058838459 552336180204504955588257689)
          ·
            refine ⟨414252135153378716691193267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 552336180204504955588257689 414252135153378716691193267)
            ·
              refine ⟨621378202730068075036789901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414252135153378716691193267 621378202730068075036789901)
              ·
                refine ⟨233016826023775528138796213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 621378202730068075036789901 233016826023775528138796213)
                ·
                  refine ⟨21845327439728955763012145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 233016826023775528138796213 21845327439728955763012145)
                  ·
                    refine ⟨16383995579796716822259109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21845327439728955763012145 16383995579796716822259109)
                    ·
                      refine ⟨3071999171211884404173583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16383995579796716822259109 3071999171211884404173583)
                      ·
                        rfl

theorem cell23_5982697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 2, 4].length) (baseStart_5982697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5982697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5982697 prefixEnd_5982697 := by exact prefixLift 5982697
  have htrace : WordTrace (prefixWord ++ tailWord_5982697) baseStart_5982697 baseEnd_5982697 := by
    simpa [prefixWord, tailWord_5982697, baseEnd_5982697] using wordTrace_append hprefix tailTrace_5982697
  have hstable : (prefixWord ++ tailWord_5982697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5982697).length < 2 ^ (prefixWord ++ tailWord_5982697).sum := by decide
  have hdescent : baseEnd_5982697 < baseStart_5982697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5982697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5982704 : List Nat := [2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 3]
def baseStart_5982704 : Nat := 118140960795 + 5982704 * 2 ^ 59
def prefixEnd_5982704 : Nat := 4983230072969 + 3 ^ 40 * 5982704 * 2
def baseEnd_5982704 : Nat := 3072002765576465876786051

theorem tailTrace_5982704 : CollatzResearch.WordTrace tailWord_5982704 prefixEnd_5982704 3072002765576465876786051 := by
  unfold tailWord_5982704
  simp only [CollatzResearch.WordTrace]
  refine ⟨109103570658846323670741583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145471427545128431560988777 109103570658846323670741583)
  ·
    refine ⟨163655355988269485506112375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109103570658846323670741583 163655355988269485506112375)
    ·
      refine ⟨245483033982404228259168563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163655355988269485506112375 245483033982404228259168563)
      ·
        refine ⟨368224550973606342388752845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245483033982404228259168563 368224550973606342388752845)
        ·
          refine ⟨138084206615102378395782317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 368224550973606342388752845 138084206615102378395782317)
          ·
            refine ⟨51781577480663391898418369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138084206615102378395782317 51781577480663391898418369)
            ·
              refine ⟨38836183110497543923813777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51781577480663391898418369 38836183110497543923813777)
              ·
                refine ⟨29127137332873157942860333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38836183110497543923813777 29127137332873157942860333)
                ·
                  refine ⟨10922676499827434228572625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29127137332873157942860333 10922676499827434228572625)
                  ·
                    refine ⟨8192007374870575671429469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10922676499827434228572625 8192007374870575671429469)
                    ·
                      refine ⟨3072002765576465876786051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8192007374870575671429469 3072002765576465876786051)
                      ·
                        rfl

theorem cell23_5982704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 3].length) (baseStart_5982704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5982704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5982704 prefixEnd_5982704 := by exact prefixLift 5982704
  have htrace : WordTrace (prefixWord ++ tailWord_5982704) baseStart_5982704 baseEnd_5982704 := by
    simpa [prefixWord, tailWord_5982704, baseEnd_5982704] using wordTrace_append hprefix tailTrace_5982704
  have hstable : (prefixWord ++ tailWord_5982704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5982704).length < 2 ^ (prefixWord ++ tailWord_5982704).sum := by decide
  have hdescent : baseEnd_5982704 < baseStart_5982704 := by decide
  rcases family_descends (prefixWord ++ tailWord_5982704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5982707 : List Nat := [1, 1, 1, 2, 2, 2, 6, 8]
def baseStart_5982707 : Nat := 118140960795 + 5982707 * 2 ^ 59
def prefixEnd_5982707 : Nat := 4983230072969 + 3 ^ 40 * 5982707 * 2
def baseEnd_5982707 : Nat := 113777937259941828335131

theorem tailTrace_5982707 : CollatzResearch.WordTrace tailWord_5982707 prefixEnd_5982707 113777937259941828335131 := by
  unfold tailWord_5982707
  simp only [CollatzResearch.WordTrace]
  refine ⟨218207250736681778853842375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145471500491121185902561583 218207250736681778853842375)
  ·
    refine ⟨327310876105022668280763563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218207250736681778853842375 327310876105022668280763563)
    ·
      refine ⟨490966314157534002421145345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327310876105022668280763563 490966314157534002421145345)
      ·
        refine ⟨368224735618150501815859009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 490966314157534002421145345 368224735618150501815859009)
        ·
          refine ⟨276168551713612876361894257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368224735618150501815859009 276168551713612876361894257)
          ·
            refine ⟨207126413785209657271420693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276168551713612876361894257 207126413785209657271420693)
            ·
              refine ⟨9709050646181702684597845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 207126413785209657271420693 9709050646181702684597845)
              ·
                refine ⟨113777937259941828335131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9709050646181702684597845 113777937259941828335131)
                ·
                  rfl

theorem cell23_5982707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 8].length) (baseStart_5982707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5982707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5982707 prefixEnd_5982707 := by exact prefixLift 5982707
  have htrace : WordTrace (prefixWord ++ tailWord_5982707) baseStart_5982707 baseEnd_5982707 := by
    simpa [prefixWord, tailWord_5982707, baseEnd_5982707] using wordTrace_append hprefix tailTrace_5982707
  have hstable : (prefixWord ++ tailWord_5982707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5982707).length < 2 ^ (prefixWord ++ tailWord_5982707).sum := by decide
  have hdescent : baseEnd_5982707 < baseStart_5982707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5982707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5982721 : List Nat := [1, 2, 4, 1, 3, 2, 1, 1, 3, 2, 3]
def baseStart_5982721 : Nat := 118140960795 + 5982721 * 2 ^ 59
def prefixEnd_5982721 : Nat := 4983230072969 + 3 ^ 40 * 5982721 * 2
def baseEnd_5982721 : Nat := 3072011494747592310273473

theorem tailTrace_5982721 : CollatzResearch.WordTrace tailWord_5982721 prefixEnd_5982721 3072011494747592310273473 := by
  unfold tailWord_5982721
  simp only [CollatzResearch.WordTrace]
  refine ⟨218207761358631059244852017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145471840905754039496568011 218207761358631059244852017)
  ·
    refine ⟨163655821018973294433639013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218207761358631059244852017 163655821018973294433639013)
    ·
      refine ⟨30685466441057492706307315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163655821018973294433639013 30685466441057492706307315)
      ·
        refine ⟨46028199661586239059460973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30685466441057492706307315 46028199661586239059460973)
        ·
          refine ⟨17260574873094839647297865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46028199661586239059460973 17260574873094839647297865)
          ·
            refine ⟨12945431154821129735473399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17260574873094839647297865 12945431154821129735473399)
            ·
              refine ⟨19418146732231694603210099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12945431154821129735473399 19418146732231694603210099)
              ·
                refine ⟨29127220098347541904815149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19418146732231694603210099 29127220098347541904815149)
                ·
                  refine ⟨10922707536880328214305681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29127220098347541904815149 10922707536880328214305681)
                  ·
                    refine ⟨8192030652660246160729261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10922707536880328214305681 8192030652660246160729261)
                    ·
                      refine ⟨3072011494747592310273473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8192030652660246160729261 3072011494747592310273473)
                      ·
                        rfl

theorem cell23_5982721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_5982721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5982721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5982721 prefixEnd_5982721 := by exact prefixLift 5982721
  have htrace : WordTrace (prefixWord ++ tailWord_5982721) baseStart_5982721 baseEnd_5982721 := by
    simpa [prefixWord, tailWord_5982721, baseEnd_5982721] using wordTrace_append hprefix tailTrace_5982721
  have hstable : (prefixWord ++ tailWord_5982721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5982721).length < 2 ^ (prefixWord ++ tailWord_5982721).sum := by decide
  have hdescent : baseEnd_5982721 < baseStart_5982721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5982721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5982724 : List Nat := [2, 3, 2, 3, 1, 1, 2, 9]
def baseStart_5982724 : Nat := 118140960795 + 5982724 * 2 ^ 59
def prefixEnd_5982724 : Nat := 4983230072969 + 3 ^ 40 * 5982724 * 2
def baseEnd_5982724 : Nat := 113778260562576140686517

theorem tailTrace_5982724 : CollatzResearch.WordTrace tailWord_5982724 prefixEnd_5982724 113778260562576140686517 := by
  unfold tailWord_5982724
  simp only [CollatzResearch.WordTrace]
  refine ⟨109103935388810095378605613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145471913851746793838140817 109103935388810095378605613)
  ·
    refine ⟨40913975770803785766977105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109103935388810095378605613 40913975770803785766977105)
    ·
      refine ⟨30685481828102839325232829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40913975770803785766977105 30685481828102839325232829)
      ·
        refine ⟨11507055685538564746962311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30685481828102839325232829 11507055685538564746962311)
        ·
          refine ⟨17260583528307847120443467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11507055685538564746962311 17260583528307847120443467)
          ·
            refine ⟨25890875292461770680665201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17260583528307847120443467 25890875292461770680665201)
            ·
              refine ⟨19418156469346328010498901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25890875292461770680665201 19418156469346328010498901)
              ·
                refine ⟨113778260562576140686517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19418156469346328010498901 113778260562576140686517)
                ·
                  rfl

theorem cell23_5982724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 9].length) (baseStart_5982724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5982724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5982724 prefixEnd_5982724 := by exact prefixLift 5982724
  have htrace : WordTrace (prefixWord ++ tailWord_5982724) baseStart_5982724 baseEnd_5982724 := by
    simpa [prefixWord, tailWord_5982724, baseEnd_5982724] using wordTrace_append hprefix tailTrace_5982724
  have hstable : (prefixWord ++ tailWord_5982724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5982724).length < 2 ^ (prefixWord ++ tailWord_5982724).sum := by decide
  have hdescent : baseEnd_5982724 < baseStart_5982724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5982724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5982752 : List Nat := [2, 1, 1, 6, 2, 1, 1, 4, 1, 2, 2]
def baseStart_5982752 : Nat := 118140960795 + 5982752 * 2 ^ 59
def prefixEnd_5982752 : Nat := 4983230072969 + 3 ^ 40 * 5982752 * 2
def baseEnd_5982752 : Nat := 3072027412647881688985831

theorem tailTrace_5982752 : CollatzResearch.WordTrace tailWord_5982752 prefixEnd_5982752 3072027412647881688985831 := by
  unfold tailWord_5982752
  simp only [CollatzResearch.WordTrace]
  refine ⟨109104446010759375769615255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145472594681012501026153673 109104446010759375769615255)
  ·
    refine ⟨163656669016139063654422883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109104446010759375769615255 163656669016139063654422883)
    ·
      refine ⟨245485003524208595481634325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163656669016139063654422883 245485003524208595481634325)
      ·
        refine ⟨11507109540197277913201609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 245485003524208595481634325 11507109540197277913201609)
        ·
          refine ⟨8630332155147958434901207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11507109540197277913201609 8630332155147958434901207)
          ·
            refine ⟨12945498232721937652351811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8630332155147958434901207 12945498232721937652351811)
            ·
              refine ⟨19418247349082906478527717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12945498232721937652351811 19418247349082906478527717)
              ·
                refine ⟨3640921377953044964723947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19418247349082906478527717 3640921377953044964723947)
                ·
                  refine ⟨5461382066929567447085921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3640921377953044964723947 5461382066929567447085921)
                  ·
                    refine ⟨4096036550197175585314441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5461382066929567447085921 4096036550197175585314441)
                    ·
                      refine ⟨3072027412647881688985831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4096036550197175585314441 3072027412647881688985831)
                      ·
                        rfl

theorem cell23_5982752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_5982752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5982752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5982752 prefixEnd_5982752 := by exact prefixLift 5982752
  have htrace : WordTrace (prefixWord ++ tailWord_5982752) baseStart_5982752 baseEnd_5982752 := by
    simpa [prefixWord, tailWord_5982752, baseEnd_5982752] using wordTrace_append hprefix tailTrace_5982752
  have hstable : (prefixWord ++ tailWord_5982752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5982752).length < 2 ^ (prefixWord ++ tailWord_5982752).sum := by decide
  have hdescent : baseEnd_5982752 < baseStart_5982752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5982752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5982844 : List Nat := [2, 2, 2, 1, 1, 2, 4, 1, 1, 7]
def baseStart_5982844 : Nat := 118140960795 + 5982844 * 2 ^ 59
def prefixEnd_5982844 : Nat := 4983230072969 + 3 ^ 40 * 5982844 * 2
def baseEnd_5982844 : Nat := 1024024884289365109678469

theorem tailTrace_5982844 : CollatzResearch.WordTrace tailWord_5982844 prefixEnd_5982844 1024024884289365109678469 := by
  unfold tailWord_5982844
  simp only [CollatzResearch.WordTrace]
  refine ⟨109106123768592725625789793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145474831691456967501053057 109106123768592725625789793)
  ·
    refine ⟨81829592826444544219342345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109106123768592725625789793 81829592826444544219342345)
    ·
      refine ⟨61372194619833408164506759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81829592826444544219342345 61372194619833408164506759)
      ·
        refine ⟨92058291929750112246760139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61372194619833408164506759 92058291929750112246760139)
        ·
          refine ⟨138087437894625168370140209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92058291929750112246760139 138087437894625168370140209)
          ·
            refine ⟨103565578420968876277605157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138087437894625168370140209 103565578420968876277605157)
            ·
              refine ⟨19418545953931664302050967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103565578420968876277605157 19418545953931664302050967)
              ·
                refine ⟨29127818930897496453076451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19418545953931664302050967 29127818930897496453076451)
                ·
                  refine ⟨43691728396346244679614677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29127818930897496453076451 43691728396346244679614677)
                  ·
                    refine ⟨1024024884289365109678469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43691728396346244679614677 1024024884289365109678469)
                    ·
                      rfl

theorem cell23_5982844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_5982844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5982844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5982844 prefixEnd_5982844 := by exact prefixLift 5982844
  have htrace : WordTrace (prefixWord ++ tailWord_5982844) baseStart_5982844 baseEnd_5982844 := by
    simpa [prefixWord, tailWord_5982844, baseEnd_5982844] using wordTrace_append hprefix tailTrace_5982844
  have hstable : (prefixWord ++ tailWord_5982844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5982844).length < 2 ^ (prefixWord ++ tailWord_5982844).sum := by decide
  have hdescent : baseEnd_5982844 < baseStart_5982844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5982844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5982848 : List Nat := [2, 1, 1, 2, 1, 7, 1, 3, 5]
def baseStart_5982848 : Nat := 118140960795 + 5982848 * 2 ^ 59
def prefixEnd_5982848 : Nat := 4983230072969 + 3 ^ 40 * 5982848 * 2
def baseEnd_5982848 : Nat := 341341856310079257042821

theorem tailTrace_5982848 : CollatzResearch.WordTrace tailWord_5982848 prefixEnd_5982848 341341856310079257042821 := by
  unfold tailWord_5982848
  simp only [CollatzResearch.WordTrace]
  refine ⟨109106196714585479967362599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145474928952780639956483465 109106196714585479967362599)
  ·
    refine ⟨163659295071878219951043899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109106196714585479967362599 163659295071878219951043899)
    ·
      refine ⟨245488942607817329926565849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163659295071878219951043899 245488942607817329926565849)
      ·
        refine ⟨184116706955862997444924387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245488942607817329926565849 184116706955862997444924387)
        ·
          refine ⟨276175060433794496167386581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184116706955862997444924387 276175060433794496167386581)
          ·
            refine ⟨6472852978917058503923123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 276175060433794496167386581 6472852978917058503923123)
            ·
              refine ⟨9709279468375587755884685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6472852978917058503923123 9709279468375587755884685)
              ·
                refine ⟨3640979800640845408456757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9709279468375587755884685 3640979800640845408456757)
                ·
                  refine ⟨341341856310079257042821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3640979800640845408456757 341341856310079257042821)
                  ·
                    rfl

theorem cell23_5982848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 3, 5].length) (baseStart_5982848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5982848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5982848 prefixEnd_5982848 := by exact prefixLift 5982848
  have htrace : WordTrace (prefixWord ++ tailWord_5982848) baseStart_5982848 baseEnd_5982848 := by
    simpa [prefixWord, tailWord_5982848, baseEnd_5982848] using wordTrace_append hprefix tailTrace_5982848
  have hstable : (prefixWord ++ tailWord_5982848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5982848).length < 2 ^ (prefixWord ++ tailWord_5982848).sum := by decide
  have hdescent : baseEnd_5982848 < baseStart_5982848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5982848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5982944 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 7]
def baseStart_5982944 : Nat := 118140960795 + 5982944 * 2 ^ 59
def prefixEnd_5982944 : Nat := 4983230072969 + 3 ^ 40 * 5982944 * 2
def baseEnd_5982944 : Nat := 3072126000933544937784947

theorem tailTrace_5982944 : CollatzResearch.WordTrace tailWord_5982944 prefixEnd_5982944 3072126000933544937784947 := by
  unfold tailWord_5982944
  simp only [CollatzResearch.WordTrace]
  refine ⟨109107947418411584165109943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145477263224548778886813257 109107947418411584165109943)
  ·
    refine ⟨163661921127617376247664915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109107947418411584165109943 163661921127617376247664915)
    ·
      refine ⟨245492881691426064371497373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163661921127617376247664915 245492881691426064371497373)
      ·
        refine ⟨92059830634284774139311515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245492881691426064371497373 92059830634284774139311515)
        ·
          refine ⟨138089745951427161208967273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92059830634284774139311515 138089745951427161208967273)
          ·
            refine ⟨103567309463570370906725455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138089745951427161208967273 103567309463570370906725455)
            ·
              refine ⟨155350964195355556360088183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103567309463570370906725455 155350964195355556360088183)
              ·
                refine ⟨233026446293033334540132275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155350964195355556360088183 233026446293033334540132275)
                ·
                  refine ⟨349539669439550001810198413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 233026446293033334540132275 349539669439550001810198413)
                  ·
                    refine ⟨131077376039831250678824405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 349539669439550001810198413 131077376039831250678824405)
                    ·
                      refine ⟨3072126000933544937784947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 131077376039831250678824405 3072126000933544937784947)
                      ·
                        rfl

theorem cell23_5982944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_5982944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5982944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5982944 prefixEnd_5982944 := by exact prefixLift 5982944
  have htrace : WordTrace (prefixWord ++ tailWord_5982944) baseStart_5982944 baseEnd_5982944 := by
    simpa [prefixWord, tailWord_5982944, baseEnd_5982944] using wordTrace_append hprefix tailTrace_5982944
  have hstable : (prefixWord ++ tailWord_5982944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5982944).length < 2 ^ (prefixWord ++ tailWord_5982944).sum := by decide
  have hdescent : baseEnd_5982944 < baseStart_5982944 := by decide
  rcases family_descends (prefixWord ++ tailWord_5982944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5982948 : List Nat := [2, 3, 1, 1, 1, 4, 1, 1, 5, 1, 3]
def baseStart_5982948 : Nat := 118140960795 + 5982948 * 2 ^ 59
def prefixEnd_5982948 : Nat := 4983230072969 + 3 ^ 40 * 5982948 * 2
def baseEnd_5982948 : Nat := 3072128054856162922134929

theorem tailTrace_5982948 : CollatzResearch.WordTrace tailWord_5982948 prefixEnd_5982948 3072128054856162922134929 := by
  unfold tailWord_5982948
  simp only [CollatzResearch.WordTrace]
  refine ⟨109108020364404338506682749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145477360485872451342243665 109108020364404338506682749)
  ·
    refine ⟨40915507636651626940006031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109108020364404338506682749 40915507636651626940006031)
    ·
      refine ⟨61373261454977440410009047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40915507636651626940006031 61373261454977440410009047)
      ·
        refine ⟨92059892182466160615013571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61373261454977440410009047 92059892182466160615013571)
        ·
          refine ⟨138089838273699240922520357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92059892182466160615013571 138089838273699240922520357)
          ·
            refine ⟨25891844676318607672972567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 138089838273699240922520357 25891844676318607672972567)
            ·
              refine ⟨38837767014477911509458851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25891844676318607672972567 38837767014477911509458851)
              ·
                refine ⟨58256650521716867264188277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38837767014477911509458851 58256650521716867264188277)
                ·
                  refine ⟨5461560986410956306017651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58256650521716867264188277 5461560986410956306017651)
                  ·
                    refine ⟨8192341479616434459026477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5461560986410956306017651 8192341479616434459026477)
                    ·
                      refine ⟨3072128054856162922134929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8192341479616434459026477 3072128054856162922134929)
                      ·
                        rfl

theorem cell23_5982948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 5, 1, 3].length) (baseStart_5982948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5982948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5982948 prefixEnd_5982948 := by exact prefixLift 5982948
  have htrace : WordTrace (prefixWord ++ tailWord_5982948) baseStart_5982948 baseEnd_5982948 := by
    simpa [prefixWord, tailWord_5982948, baseEnd_5982948] using wordTrace_append hprefix tailTrace_5982948
  have hstable : (prefixWord ++ tailWord_5982948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5982948).length < 2 ^ (prefixWord ++ tailWord_5982948).sum := by decide
  have hdescent : baseEnd_5982948 < baseStart_5982948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5982948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5982952 : List Nat := [2, 1, 4, 1, 5, 1, 1, 1, 2, 2, 3]
def baseStart_5982952 : Nat := 118140960795 + 5982952 * 2 ^ 59
def prefixEnd_5982952 : Nat := 4983230072969 + 3 ^ 40 * 5982952 * 2
def baseEnd_5982952 : Nat := 3072130108778780906484911

theorem tailTrace_5982952 : CollatzResearch.WordTrace tailWord_5982952 prefixEnd_5982952 3072130108778780906484911 := by
  unfold tailWord_5982952
  simp only [CollatzResearch.WordTrace]
  refine ⟨109108093310397092848255555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145477457747196123797674073 109108093310397092848255555)
  ·
    refine ⟨163662139965595639272383333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109108093310397092848255555 163662139965595639272383333)
    ·
      refine ⟨30686651243549182363571875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163662139965595639272383333 30686651243549182363571875)
      ·
        refine ⟨46029976865323773545357813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30686651243549182363571875 46029976865323773545357813)
        ·
          refine ⟨4315310331124103769877295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46029976865323773545357813 4315310331124103769877295)
          ·
            refine ⟨6472965496686155654815943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4315310331124103769877295 6472965496686155654815943)
            ·
              refine ⟨9709448245029233482223915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6472965496686155654815943 9709448245029233482223915)
              ·
                refine ⟨14564172367543850223335873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9709448245029233482223915 14564172367543850223335873)
                ·
                  refine ⟨10923129275657887667501905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14564172367543850223335873 10923129275657887667501905)
                  ·
                    refine ⟨8192346956743415750626429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10923129275657887667501905 8192346956743415750626429)
                    ·
                      refine ⟨3072130108778780906484911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8192346956743415750626429 3072130108778780906484911)
                      ·
                        rfl

theorem cell23_5982952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 2, 2, 3].length) (baseStart_5982952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5982952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5982952 prefixEnd_5982952 := by exact prefixLift 5982952
  have htrace : WordTrace (prefixWord ++ tailWord_5982952) baseStart_5982952 baseEnd_5982952 := by
    simpa [prefixWord, tailWord_5982952, baseEnd_5982952] using wordTrace_append hprefix tailTrace_5982952
  have hstable : (prefixWord ++ tailWord_5982952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5982952).length < 2 ^ (prefixWord ++ tailWord_5982952).sum := by decide
  have hdescent : baseEnd_5982952 < baseStart_5982952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5982952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5982991 : List Nat := [1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 5]
def baseStart_5982991 : Nat := 118140960795 + 5982991 * 2 ^ 59
def prefixEnd_5982991 : Nat := 4983230072969 + 3 ^ 40 * 5982991 * 2
def baseEnd_5982991 : Nat := 3072150134524306253897231

theorem tailTrace_5982991 : CollatzResearch.WordTrace tailWord_5982991 prefixEnd_5982991 3072150134524306253897231 := by
  unfold tailWord_5982991
  simp only [CollatzResearch.WordTrace]
  refine ⟨218217609067652895357180827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145478406045101930238120551 218217609067652895357180827)
  ·
    refine ⟨327326413601479343035771241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218217609067652895357180827 327326413601479343035771241)
    ·
      refine ⟨245494810201109507276828431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327326413601479343035771241 245494810201109507276828431)
      ·
        refine ⟨368242215301664260915242647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245494810201109507276828431 368242215301664260915242647)
        ·
          refine ⟨552363322952496391372863971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368242215301664260915242647 552363322952496391372863971)
          ·
            refine ⟨828544984428744587059295957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552363322952496391372863971 828544984428744587059295957)
            ·
              refine ⟨19419023072548701259202249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 828544984428744587059295957 19419023072548701259202249)
              ·
                refine ⟨14564267304411525944401687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19419023072548701259202249 14564267304411525944401687)
                ·
                  refine ⟨21846400956617288916602531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14564267304411525944401687 21846400956617288916602531)
                  ·
                    refine ⟨32769601434925933374903797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21846400956617288916602531 32769601434925933374903797)
                    ·
                      refine ⟨3072150134524306253897231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32769601434925933374903797 3072150134524306253897231)
                      ·
                        rfl

theorem cell23_5982991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 5].length) (baseStart_5982991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5982991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5982991 prefixEnd_5982991 := by exact prefixLift 5982991
  have htrace : WordTrace (prefixWord ++ tailWord_5982991) baseStart_5982991 baseEnd_5982991 := by
    simpa [prefixWord, tailWord_5982991, baseEnd_5982991] using wordTrace_append hprefix tailTrace_5982991
  have hstable : (prefixWord ++ tailWord_5982991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5982991).length < 2 ^ (prefixWord ++ tailWord_5982991).sum := by decide
  have hdescent : baseEnd_5982991 < baseStart_5982991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5982991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5983001 : List Nat := [1, 2, 1, 2, 1, 1, 1, 7, 1, 2, 4]
def baseStart_5983001 : Nat := 118140960795 + 5983001 * 2 ^ 59
def prefixEnd_5983001 : Nat := 4983230072969 + 3 ^ 40 * 5983001 * 2
def baseEnd_5983001 : Nat := 3072155269330851214772185

theorem tailTrace_5983001 : CollatzResearch.WordTrace tailWord_5983001 prefixEnd_5983001 3072155269330851214772185 := by
  unfold tailWord_5983001
  simp only [CollatzResearch.WordTrace]
  refine ⟨218217973797616667065044857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145478649198411111376696571 218217973797616667065044857)
  ·
    refine ⟨163663480348212500298783643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218217973797616667065044857 163663480348212500298783643)
    ·
      refine ⟨245495220522318750448175465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163663480348212500298783643 245495220522318750448175465)
      ·
        refine ⟨184121415391739062836131599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245495220522318750448175465 184121415391739062836131599)
        ·
          refine ⟨276182123087608594254197399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184121415391739062836131599 276182123087608594254197399)
          ·
            refine ⟨414273184631412891381296099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276182123087608594254197399 414273184631412891381296099)
            ·
              refine ⟨621409776947119337071944149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414273184631412891381296099 621409776947119337071944149)
              ·
                refine ⟨14564291647198109462623691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 621409776947119337071944149 14564291647198109462623691)
                ·
                  refine ⟨21846437470797164193935537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14564291647198109462623691 21846437470797164193935537)
                  ·
                    refine ⟨16384828103097873145451653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21846437470797164193935537 16384828103097873145451653)
                    ·
                      refine ⟨3072155269330851214772185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16384828103097873145451653 3072155269330851214772185)
                      ·
                        rfl

theorem cell23_5983001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 2, 4].length) (baseStart_5983001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5983001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5983001 prefixEnd_5983001 := by exact prefixLift 5983001
  have htrace : WordTrace (prefixWord ++ tailWord_5983001) baseStart_5983001 baseEnd_5983001 := by
    simpa [prefixWord, tailWord_5983001, baseEnd_5983001] using wordTrace_append hprefix tailTrace_5983001
  have hstable : (prefixWord ++ tailWord_5983001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5983001).length < 2 ^ (prefixWord ++ tailWord_5983001).sum := by decide
  have hdescent : baseEnd_5983001 < baseStart_5983001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5983001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5983065 : List Nat := [1, 2, 1, 2, 2, 5, 1, 1, 3, 3, 2]
def baseStart_5983065 : Nat := 118140960795 + 5983065 * 2 ^ 59
def prefixEnd_5983065 : Nat := 4983230072969 + 3 ^ 40 * 5983065 * 2
def baseEnd_5983065 : Nat := 3072188132092738964371891

theorem tailTrace_5983065 : CollatzResearch.WordTrace tailWord_5983065 prefixEnd_5983065 3072188132092738964371891 := by
  unfold tailWord_5983065
  simp only [CollatzResearch.WordTrace]
  refine ⟨218220308069384805995374649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145480205379589870663583099 218220308069384805995374649)
  ·
    refine ⟨163665231052038604496530987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218220308069384805995374649 163665231052038604496530987)
    ·
      refine ⟨245497846578057906744796481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163665231052038604496530987 245497846578057906744796481)
      ·
        refine ⟨184123384933543430058597361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245497846578057906744796481 184123384933543430058597361)
        ·
          refine ⟨138092538700157572543948021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184123384933543430058597361 138092538700157572543948021)
          ·
            refine ⟨12946175503139772425995127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 138092538700157572543948021 12946175503139772425995127)
            ·
              refine ⟨19419263254709658638992691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12946175503139772425995127 19419263254709658638992691)
              ·
                refine ⟨29128894882064487958489037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19419263254709658638992691 29128894882064487958489037)
                ·
                  refine ⟨10923335580774182984433389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29128894882064487958489037 10923335580774182984433389)
                  ·
                    refine ⟨4096250842790318619162521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10923335580774182984433389 4096250842790318619162521)
                    ·
                      refine ⟨3072188132092738964371891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4096250842790318619162521 3072188132092738964371891)
                      ·
                        rfl

theorem cell23_5983065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3, 3, 2].length) (baseStart_5983065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5983065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5983065 prefixEnd_5983065 := by exact prefixLift 5983065
  have htrace : WordTrace (prefixWord ++ tailWord_5983065) baseStart_5983065 baseEnd_5983065 := by
    simpa [prefixWord, tailWord_5983065, baseEnd_5983065] using wordTrace_append hprefix tailTrace_5983065
  have hstable : (prefixWord ++ tailWord_5983065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5983065).length < 2 ^ (prefixWord ++ tailWord_5983065).sum := by decide
  have hdescent : baseEnd_5983065 < baseStart_5983065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5983065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5983095 : List Nat := [1, 1, 3, 1, 1, 2, 1, 5, 4, 2, 2]
def baseStart_5983095 : Nat := 118140960795 + 5983095 * 2 ^ 59
def prefixEnd_5983095 : Nat := 4983230072969 + 3 ^ 40 * 5983095 * 2
def baseEnd_5983095 : Nat := 3072203536512373846996753

theorem tailTrace_5983095 : CollatzResearch.WordTrace tailWord_5983095 prefixEnd_5983095 3072203536512373846996753 := by
  unfold tailWord_5983095
  simp only [CollatzResearch.WordTrace]
  refine ⟨218221402259276121118966739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145480934839517414079311159 218221402259276121118966739)
  ·
    refine ⟨327332103388914181678450109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218221402259276121118966739 327332103388914181678450109)
    ·
      refine ⟨122749538770842818129418791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 327332103388914181678450109 122749538770842818129418791)
      ·
        refine ⟨184124308156264227194128187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122749538770842818129418791 184124308156264227194128187)
        ·
          refine ⟨276186462234396340791192281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184124308156264227194128187 276186462234396340791192281)
          ·
            refine ⟨207139846675797255593394211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276186462234396340791192281 207139846675797255593394211)
            ·
              refine ⟨310709770013695883390091317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207139846675797255593394211 310709770013695883390091317)
              ·
                refine ⟨29129040938783989067821061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 310709770013695883390091317 29129040938783989067821061)
                ·
                  refine ⟨5461695176021997950216449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29129040938783989067821061 5461695176021997950216449)
                  ·
                    refine ⟨4096271382016498462662337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5461695176021997950216449 4096271382016498462662337)
                    ·
                      refine ⟨3072203536512373846996753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4096271382016498462662337 3072203536512373846996753)
                      ·
                        rfl

theorem cell23_5983095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 4, 2, 2].length) (baseStart_5983095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5983095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5983095 prefixEnd_5983095 := by exact prefixLift 5983095
  have htrace : WordTrace (prefixWord ++ tailWord_5983095) baseStart_5983095 baseEnd_5983095 := by
    simpa [prefixWord, tailWord_5983095, baseEnd_5983095] using wordTrace_append hprefix tailTrace_5983095
  have hstable : (prefixWord ++ tailWord_5983095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5983095).length < 2 ^ (prefixWord ++ tailWord_5983095).sum := by decide
  have hdescent : baseEnd_5983095 < baseStart_5983095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5983095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5983112 : List Nat := [2, 1, 3, 3, 2, 2, 2, 1, 1, 4, 2]
def baseStart_5983112 : Nat := 118140960795 + 5983112 * 2 ^ 59
def prefixEnd_5983112 : Nat := 4983230072969 + 3 ^ 40 * 5983112 * 2
def baseEnd_5983112 : Nat := 3072212265683500280484175

theorem tailTrace_5983112 : CollatzResearch.WordTrace tailWord_5983112 prefixEnd_5983112 3072212265683500280484175 := by
  unfold tailWord_5983112
  simp only [CollatzResearch.WordTrace]
  refine ⟨109111011150107266511167795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145481348200143022014890393 109111011150107266511167795)
  ·
    refine ⟨163666516725160899766751693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109111011150107266511167795 163666516725160899766751693)
    ·
      refine ⟨61374943771935337412531885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163666516725160899766751693 61374943771935337412531885)
      ·
        refine ⟨23015603914475751529699457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61374943771935337412531885 23015603914475751529699457)
        ·
          refine ⟨17261702935856813647274593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23015603914475751529699457 17261702935856813647274593)
          ·
            refine ⟨12946277201892610235455945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17261702935856813647274593 12946277201892610235455945)
            ·
              refine ⟨9709707901419457676591959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12946277201892610235455945 9709707901419457676591959)
              ·
                refine ⟨14564561852129186514887939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9709707901419457676591959 14564561852129186514887939)
                ·
                  refine ⟨21846842778193779772331909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14564561852129186514887939 21846842778193779772331909)
                  ·
                    refine ⟨4096283020911333707312233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21846842778193779772331909 4096283020911333707312233)
                    ·
                      refine ⟨3072212265683500280484175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4096283020911333707312233 3072212265683500280484175)
                      ·
                        rfl

theorem cell23_5983112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_5983112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5983112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5983112 prefixEnd_5983112 := by exact prefixLift 5983112
  have htrace : WordTrace (prefixWord ++ tailWord_5983112) baseStart_5983112 baseEnd_5983112 := by
    simpa [prefixWord, tailWord_5983112, baseEnd_5983112] using wordTrace_append hprefix tailTrace_5983112
  have hstable : (prefixWord ++ tailWord_5983112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5983112).length < 2 ^ (prefixWord ++ tailWord_5983112).sum := by decide
  have hdescent : baseEnd_5983112 < baseStart_5983112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5983112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5983135 : List Nat := [1, 1, 2, 5, 2, 1, 1, 5, 5]
def baseStart_5983135 : Nat := 118140960795 + 5983135 * 2 ^ 59
def prefixEnd_5983135 : Nat := 4983230072969 + 3 ^ 40 * 5983135 * 2
def baseEnd_5983135 : Nat := 341358230637617076721841

theorem tailTrace_5983135 : CollatzResearch.WordTrace tailWord_5983135 prefixEnd_5983135 341358230637617076721841 := by
  unfold tailWord_5983135
  simp only [CollatzResearch.WordTrace]
  refine ⟨218222861179131207950422859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145481907452754138633615239 218222861179131207950422859)
  ·
    refine ⟨327334291768696811925634289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218222861179131207950422859 327334291768696811925634289)
    ·
      refine ⟨245500718826522608944225717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327334291768696811925634289 245500718826522608944225717)
      ·
        refine ⟨23015692389986494588521161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 245500718826522608944225717 23015692389986494588521161)
        ·
          refine ⟨17261769292489870941390871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23015692389986494588521161 17261769292489870941390871)
          ·
            refine ⟨25892653938734806412086307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17261769292489870941390871 25892653938734806412086307)
            ·
              refine ⟨38838980908102209618129461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25892653938734806412086307 38838980908102209618129461)
              ·
                refine ⟨3641154460134582151699637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38838980908102209618129461 3641154460134582151699637)
                ·
                  refine ⟨341358230637617076721841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3641154460134582151699637 341358230637617076721841)
                  ·
                    rfl

theorem cell23_5983135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 5, 5].length) (baseStart_5983135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5983135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5983135 prefixEnd_5983135 := by exact prefixLift 5983135
  have htrace : WordTrace (prefixWord ++ tailWord_5983135) baseStart_5983135 baseEnd_5983135 := by
    simpa [prefixWord, tailWord_5983135, baseEnd_5983135] using wordTrace_append hprefix tailTrace_5983135
  have hstable : (prefixWord ++ tailWord_5983135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5983135).length < 2 ^ (prefixWord ++ tailWord_5983135).sum := by decide
  have hdescent : baseEnd_5983135 < baseStart_5983135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5983135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5983168 : List Nat := [2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 4]
def baseStart_5983168 : Nat := 118140960795 + 5983168 * 2 ^ 59
def prefixEnd_5983168 : Nat := 4983230072969 + 3 ^ 40 * 5983168 * 2
def baseEnd_5983168 : Nat := 3072241020600152061383917

theorem tailTrace_5983168 : CollatzResearch.WordTrace tailWord_5983168 prefixEnd_5983168 3072241020600152061383917 := by
  unfold tailWord_5983168
  simp only [CollatzResearch.WordTrace]
  refine ⟨109112032394005827293187079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145482709858674436390916105 109112032394005827293187079)
  ·
    refine ⟨163668048591008740939780619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109112032394005827293187079 163668048591008740939780619)
    ·
      refine ⟨245502072886513111409670929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163668048591008740939780619 245502072886513111409670929)
      ·
        refine ⟨184126554664884833557253197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245502072886513111409670929 184126554664884833557253197)
        ·
          refine ⟨69047457999331812583969949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184126554664884833557253197 69047457999331812583969949)
          ·
            refine ⟨25892796749749429718988731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69047457999331812583969949 25892796749749429718988731)
            ·
              refine ⟨38839195124624144578483097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25892796749749429718988731 38839195124624144578483097)
              ·
                refine ⟨29129396343468108433862323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38839195124624144578483097 29129396343468108433862323)
                ·
                  refine ⟨43694094515202162650793485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29129396343468108433862323 43694094515202162650793485)
                  ·
                    refine ⟨16385285443200810994047557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43694094515202162650793485 16385285443200810994047557)
                    ·
                      refine ⟨3072241020600152061383917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16385285443200810994047557 3072241020600152061383917)
                      ·
                        rfl

theorem cell23_5983168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 4].length) (baseStart_5983168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5983168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5983168 prefixEnd_5983168 := by exact prefixLift 5983168
  have htrace : WordTrace (prefixWord ++ tailWord_5983168) baseStart_5983168 baseEnd_5983168 := by
    simpa [prefixWord, tailWord_5983168, baseEnd_5983168] using wordTrace_append hprefix tailTrace_5983168
  have hstable : (prefixWord ++ tailWord_5983168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5983168).length < 2 ^ (prefixWord ++ tailWord_5983168).sum := by decide
  have hdescent : baseEnd_5983168 < baseStart_5983168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5983168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5983202 : List Nat := [3, 3, 3, 1, 1, 1, 1, 1, 4, 1, 4]
def baseStart_5983202 : Nat := 118140960795 + 5983202 * 2 ^ 59
def prefixEnd_5983202 : Nat := 4983230072969 + 3 ^ 40 * 5983202 * 2
def baseEnd_5983202 : Nat := 3072258478942404928358761

theorem tailTrace_5983202 : CollatzResearch.WordTrace tailWord_5983202 prefixEnd_5983202 3072258478942404928358761 := by
  unfold tailWord_5983202
  simp only [CollatzResearch.WordTrace]
  refine ⟨54556326217472119598277965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145483536579925652262074573 54556326217472119598277965)
  ·
    refine ⟨20458622331552044849354237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54556326217472119598277965 20458622331552044849354237)
    ·
      refine ⟨7671983374332016818507839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20458622331552044849354237 7671983374332016818507839)
      ·
        refine ⟨11507975061498025227761759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7671983374332016818507839 11507975061498025227761759)
        ·
          refine ⟨17261962592247037841642639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11507975061498025227761759 17261962592247037841642639)
          ·
            refine ⟨25892943888370556762463959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17261962592247037841642639 25892943888370556762463959)
            ·
              refine ⟨38839415832555835143695939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25892943888370556762463959 38839415832555835143695939)
              ·
                refine ⟨58259123748833752715543909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38839415832555835143695939 58259123748833752715543909)
                ·
                  refine ⟨10923585702906328634164483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58259123748833752715543909 10923585702906328634164483)
                  ·
                    refine ⟨16385378554359492951246725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10923585702906328634164483 16385378554359492951246725)
                    ·
                      refine ⟨3072258478942404928358761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16385378554359492951246725 3072258478942404928358761)
                      ·
                        rfl

theorem cell23_5983202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_5983202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5983202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5983202 prefixEnd_5983202 := by exact prefixLift 5983202
  have htrace : WordTrace (prefixWord ++ tailWord_5983202) baseStart_5983202 baseEnd_5983202 := by
    simpa [prefixWord, tailWord_5983202, baseEnd_5983202] using wordTrace_append hprefix tailTrace_5983202
  have hstable : (prefixWord ++ tailWord_5983202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5983202).length < 2 ^ (prefixWord ++ tailWord_5983202).sum := by decide
  have hdescent : baseEnd_5983202 < baseStart_5983202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5983202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5983208 : List Nat := [2, 1, 4, 1, 1, 1, 4, 1, 8]
def baseStart_5983208 : Nat := 118140960795 + 5983208 * 2 ^ 59
def prefixEnd_5983208 : Nat := 4983230072969 + 3 ^ 40 * 5983208 * 2
def baseEnd_5983208 : Nat := 341362395536259100542637

theorem tailTrace_5983208 : CollatzResearch.WordTrace tailWord_5983208 prefixEnd_5983208 341362395536259100542637 := by
  unfold tailWord_5983208
  simp only [CollatzResearch.WordTrace]
  refine ⟨109112761853933370708915139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145483682471911160945220185 109112761853933370708915139)
  ·
    refine ⟨163669142780900056063372709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109112761853933370708915139 163669142780900056063372709)
    ·
      refine ⟨30687964271418760511882383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163669142780900056063372709 30687964271418760511882383)
      ·
        refine ⟨46031946407128140767823575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30687964271418760511882383 46031946407128140767823575)
        ·
          refine ⟨69047919610692211151735363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46031946407128140767823575 69047919610692211151735363)
          ·
            refine ⟨103571879416038316727603045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69047919610692211151735363 103571879416038316727603045)
            ·
              refine ⟨19419727390507184386425571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103571879416038316727603045 19419727390507184386425571)
              ·
                refine ⟨29129591085760776579638357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19419727390507184386425571 29129591085760776579638357)
                ·
                  refine ⟨341362395536259100542637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29129591085760776579638357 341362395536259100542637)
                  ·
                    rfl

theorem cell23_5983208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 8].length) (baseStart_5983208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5983208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5983208 prefixEnd_5983208 := by exact prefixLift 5983208
  have htrace : WordTrace (prefixWord ++ tailWord_5983208) baseStart_5983208 baseEnd_5983208 := by
    simpa [prefixWord, tailWord_5983208, baseEnd_5983208] using wordTrace_append hprefix tailTrace_5983208
  have hstable : (prefixWord ++ tailWord_5983208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5983208).length < 2 ^ (prefixWord ++ tailWord_5983208).sum := by decide
  have hdescent : baseEnd_5983208 < baseStart_5983208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5983208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5983269 : List Nat := [1, 3, 1, 2, 2, 2, 3, 4, 1, 1, 3]
def baseStart_5983269 : Nat := 118140960795 + 5983269 * 2 ^ 59
def prefixEnd_5983269 : Nat := 4983230072969 + 3 ^ 40 * 5983269 * 2
def baseEnd_5983269 : Nat := 3072292882146256166220953

theorem tailTrace_5983269 : CollatzResearch.WordTrace tailWord_5983269 prefixEnd_5983269 3072292882146256166220953 := by
  unfold tailWord_5983269
  simp only [CollatzResearch.WordTrace]
  refine ⟨218227748560645748835800861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145485165707097165890533907 218227748560645748835800861)
  ·
    refine ⟨81835405710242155813425323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218227748560645748835800861 81835405710242155813425323)
    ·
      refine ⟨122753108565363233720137985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81835405710242155813425323 122753108565363233720137985)
      ·
        refine ⟨92064831424022425290103489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122753108565363233720137985 92064831424022425290103489)
        ·
          refine ⟨69048623568016818967577617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92064831424022425290103489 69048623568016818967577617)
          ·
            refine ⟨51786467676012614225683213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69048623568016818967577617 51786467676012614225683213)
            ·
              refine ⟨19419925378504730334631205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51786467676012614225683213 19419925378504730334631205)
              ·
                refine ⟨3641236008469636937743351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19419925378504730334631205 3641236008469636937743351)
                ·
                  refine ⟨5461854012704455406615027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3641236008469636937743351 5461854012704455406615027)
                  ·
                    refine ⟨8192781019056683109922541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5461854012704455406615027 8192781019056683109922541)
                    ·
                      refine ⟨3072292882146256166220953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8192781019056683109922541 3072292882146256166220953)
                      ·
                        rfl

theorem cell23_5983269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 4, 1, 1, 3].length) (baseStart_5983269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5983269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5983269 prefixEnd_5983269 := by exact prefixLift 5983269
  have htrace : WordTrace (prefixWord ++ tailWord_5983269) baseStart_5983269 baseEnd_5983269 := by
    simpa [prefixWord, tailWord_5983269, baseEnd_5983269] using wordTrace_append hprefix tailTrace_5983269
  have hstable : (prefixWord ++ tailWord_5983269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5983269).length < 2 ^ (prefixWord ++ tailWord_5983269).sum := by decide
  have hdescent : baseEnd_5983269 < baseStart_5983269 := by decide
  rcases family_descends (prefixWord ++ tailWord_5983269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5983285 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 6, 4]
def baseStart_5983285 : Nat := 118140960795 + 5983285 * 2 ^ 59
def prefixEnd_5983285 : Nat := 4983230072969 + 3 ^ 40 * 5983285 * 2
def baseEnd_5983285 : Nat := 1024100365945576034540293

theorem tailTrace_5983285 : CollatzResearch.WordTrace tailWord_5983285 prefixEnd_5983285 1024100365945576034540293 := by
  unfold tailWord_5983285
  simp only [CollatzResearch.WordTrace]
  refine ⟨218228332128587783568383309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145485554752391855712255539 218228332128587783568383309)
  ·
    refine ⟨81835624548220418838143741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218228332128587783568383309 81835624548220418838143741)
    ·
      refine ⟨30688359205582657064303903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81835624548220418838143741 30688359205582657064303903)
      ·
        refine ⟨46032538808373985596455855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30688359205582657064303903 46032538808373985596455855)
        ·
          refine ⟨69048808212560978394683783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46032538808373985596455855 69048808212560978394683783)
          ·
            refine ⟨103573212318841467592025675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69048808212560978394683783 103573212318841467592025675)
            ·
              refine ⟨155359818478262201388038513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103573212318841467592025675 155359818478262201388038513)
              ·
                refine ⟨116519863858696651041028885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155359818478262201388038513 116519863858696651041028885)
                ·
                  refine ⟨5461868618376405517548229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 116519863858696651041028885 5461868618376405517548229)
                  ·
                    refine ⟨1024100365945576034540293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5461868618376405517548229 1024100365945576034540293)
                    ·
                      rfl

theorem cell23_5983285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_5983285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5983285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5983285 prefixEnd_5983285 := by exact prefixLift 5983285
  have htrace : WordTrace (prefixWord ++ tailWord_5983285) baseStart_5983285 baseEnd_5983285 := by
    simpa [prefixWord, tailWord_5983285, baseEnd_5983285] using wordTrace_append hprefix tailTrace_5983285
  have hstable : (prefixWord ++ tailWord_5983285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5983285).length < 2 ^ (prefixWord ++ tailWord_5983285).sum := by decide
  have hdescent : baseEnd_5983285 < baseStart_5983285 := by decide
  rcases family_descends (prefixWord ++ tailWord_5983285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5983309 : List Nat := [1, 6, 1, 1, 1, 3, 1, 3, 1, 1, 4]
def baseStart_5983309 : Nat := 118140960795 + 5983309 * 2 ^ 59
def prefixEnd_5983309 : Nat := 4983230072969 + 3 ^ 40 * 5983309 * 2
def baseEnd_5983309 : Nat := 3072313421372436009720769

theorem tailTrace_5983309 : CollatzResearch.WordTrace tailWord_5983309 prefixEnd_5983309 3072313421372436009720769 := by
  unfold tailWord_5983309
  simp only [CollatzResearch.WordTrace]
  refine ⟨218229207480500835667256981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145486138320333890444837987 218229207480500835667256981)
  ·
    refine ⟨10229494100648476671902671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 218229207480500835667256981 10229494100648476671902671)
    ·
      refine ⟨15344241150972715007854007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10229494100648476671902671 15344241150972715007854007)
      ·
        refine ⟨23016361726459072511781011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15344241150972715007854007 23016361726459072511781011)
        ·
          refine ⟨34524542589688608767671517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23016361726459072511781011 34524542589688608767671517)
          ·
            refine ⟨12946703471133228287876819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34524542589688608767671517 12946703471133228287876819)
            ·
              refine ⟨19420055206699842431815229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12946703471133228287876819 19420055206699842431815229)
              ·
                refine ⟨7282520702512440911930711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19420055206699842431815229 7282520702512440911930711)
                ·
                  refine ⟨10923781053768661367896067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7282520702512440911930711 10923781053768661367896067)
                  ·
                    refine ⟨16385671580652992051844101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10923781053768661367896067 16385671580652992051844101)
                    ·
                      refine ⟨3072313421372436009720769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16385671580652992051844101 3072313421372436009720769)
                      ·
                        rfl

theorem cell23_5983309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_5983309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5983309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5983309 prefixEnd_5983309 := by exact prefixLift 5983309
  have htrace : WordTrace (prefixWord ++ tailWord_5983309) baseStart_5983309 baseEnd_5983309 := by
    simpa [prefixWord, tailWord_5983309, baseEnd_5983309] using wordTrace_append hprefix tailTrace_5983309
  have hstable : (prefixWord ++ tailWord_5983309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5983309).length < 2 ^ (prefixWord ++ tailWord_5983309).sum := by decide
  have hdescent : baseEnd_5983309 < baseStart_5983309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5983309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5983336 : List Nat := [2, 1, 4, 4, 2, 1, 1, 1, 1, 6]
def baseStart_5983336 : Nat := 118140960795 + 5983336 * 2 ^ 59
def prefixEnd_5983336 : Nat := 4983230072969 + 3 ^ 40 * 5983336 * 2
def baseEnd_5983336 : Nat := 1024109095116702468027715

theorem tailTrace_5983336 : CollatzResearch.WordTrace tailWord_5983336 prefixEnd_5983336 1024109095116702468027715 := by
  unfold tailWord_5983336
  simp only [CollatzResearch.WordTrace]
  refine ⟨109115096125701509639244931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145486794834268679518993241 109115096125701509639244931)
  ·
    refine ⟨163672644188552264458867397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109115096125701509639244931 163672644188552264458867397)
    ·
      refine ⟨30688620785353549586037637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163672644188552264458867397 30688620785353549586037637)
      ·
        refine ⟨5754116397253790547382057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30688620785353549586037637 5754116397253790547382057)
        ·
          refine ⟨4315587297940342910536543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5754116397253790547382057 4315587297940342910536543)
          ·
            refine ⟨6473380946910514365804815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4315587297940342910536543 6473380946910514365804815)
            ·
              refine ⟨9710071420365771548707223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6473380946910514365804815 9710071420365771548707223)
              ·
                refine ⟨14565107130548657323060835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9710071420365771548707223 14565107130548657323060835)
                ·
                  refine ⟨21847660695822985984591253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14565107130548657323060835 21847660695822985984591253)
                  ·
                    refine ⟨1024109095116702468027715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21847660695822985984591253 1024109095116702468027715)
                    ·
                      rfl

theorem cell23_5983336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_5983336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5983336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5983336 prefixEnd_5983336 := by exact prefixLift 5983336
  have htrace : WordTrace (prefixWord ++ tailWord_5983336) baseStart_5983336 baseEnd_5983336 := by
    simpa [prefixWord, tailWord_5983336, baseEnd_5983336] using wordTrace_append hprefix tailTrace_5983336
  have hstable : (prefixWord ++ tailWord_5983336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5983336).length < 2 ^ (prefixWord ++ tailWord_5983336).sum := by decide
  have hdescent : baseEnd_5983336 < baseStart_5983336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5983336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5983352 : List Nat := [2, 1, 2, 1, 1, 1, 4, 3, 3, 3, 2]
def baseStart_5983352 : Nat := 118140960795 + 5983352 * 2 ^ 59
def prefixEnd_5983352 : Nat := 4983230072969 + 3 ^ 40 * 5983352 * 2
def baseEnd_5983352 : Nat := 3072335501040579341483071

theorem tailTrace_5983352 : CollatzResearch.WordTrace tailWord_5983352 prefixEnd_5983352 3072335501040579341483071 := by
  unfold tailWord_5983352
  simp only [CollatzResearch.WordTrace]
  refine ⟨109115387909672527005536155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145487183879563369340714873 109115387909672527005536155)
  ·
    refine ⟨163673081864508790508304233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109115387909672527005536155 163673081864508790508304233)
    ·
      refine ⟨122754811398381592881228175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163673081864508790508304233 122754811398381592881228175)
      ·
        refine ⟨184132217097572389321842263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122754811398381592881228175 184132217097572389321842263)
        ·
          refine ⟨276198325646358583982763395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184132217097572389321842263 276198325646358583982763395)
          ·
            refine ⟨414297488469537875974145093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276198325646358583982763395 414297488469537875974145093)
            ·
              refine ⟨77680779088038351745152205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 414297488469537875974145093 77680779088038351745152205)
              ·
                refine ⟨29130292158014381904432077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77680779088038351745152205 29130292158014381904432077)
                ·
                  refine ⟨10923859559255393214162029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29130292158014381904432077 10923859559255393214162029)
                  ·
                    refine ⟨4096447334720772455310761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10923859559255393214162029 4096447334720772455310761)
                    ·
                      refine ⟨3072335501040579341483071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4096447334720772455310761 3072335501040579341483071)
                      ·
                        rfl

theorem cell23_5983352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 3, 3, 2].length) (baseStart_5983352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5983352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5983352 prefixEnd_5983352 := by exact prefixLift 5983352
  have htrace : WordTrace (prefixWord ++ tailWord_5983352) baseStart_5983352 baseEnd_5983352 := by
    simpa [prefixWord, tailWord_5983352, baseEnd_5983352] using wordTrace_append hprefix tailTrace_5983352
  have hstable : (prefixWord ++ tailWord_5983352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5983352).length < 2 ^ (prefixWord ++ tailWord_5983352).sum := by decide
  have hdescent : baseEnd_5983352 < baseStart_5983352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5983352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5983369 : List Nat := [1, 2, 1, 1, 4, 3, 2, 3, 1, 3, 2]
def baseStart_5983369 : Nat := 118140960795 + 5983369 * 2 ^ 59
def prefixEnd_5983369 : Nat := 4983230072969 + 3 ^ 40 * 5983369 * 2
def baseEnd_5983369 : Nat := 3072344230211705774970493

theorem tailTrace_5983369 : CollatzResearch.WordTrace tailWord_5983369 prefixEnd_5983369 3072344230211705774970493 := by
  unfold tailWord_5983369
  simp only [CollatzResearch.WordTrace]
  refine ⟨218231395860283465914441161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145487597240188977276294107 218231395860283465914441161)
  ·
    refine ⟨163673546895212599435830871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218231395860283465914441161 163673546895212599435830871)
    ·
      refine ⟨245510320342818899153746307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163673546895212599435830871 245510320342818899153746307)
      ·
        refine ⟨368265480514228348730619461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245510320342818899153746307 368265480514228348730619461)
        ·
          refine ⟨69049777596417815386991149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 368265480514228348730619461 69049777596417815386991149)
          ·
            refine ⟨25893666598656680770121681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69049777596417815386991149 25893666598656680770121681)
            ·
              refine ⟨19420249948992510577591261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25893666598656680770121681 19420249948992510577591261)
              ·
                refine ⟨7282593730872191466596723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19420249948992510577591261 7282593730872191466596723)
                ·
                  refine ⟨10923890596308287199895085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7282593730872191466596723 10923890596308287199895085)
                  ·
                    refine ⟨4096458973615607699960657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10923890596308287199895085 4096458973615607699960657)
                    ·
                      refine ⟨3072344230211705774970493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4096458973615607699960657 3072344230211705774970493)
                      ·
                        rfl

theorem cell23_5983369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3, 1, 3, 2].length) (baseStart_5983369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5983369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5983369 prefixEnd_5983369 := by exact prefixLift 5983369
  have htrace : WordTrace (prefixWord ++ tailWord_5983369) baseStart_5983369 baseEnd_5983369 := by
    simpa [prefixWord, tailWord_5983369, baseEnd_5983369] using wordTrace_append hprefix tailTrace_5983369
  have hstable : (prefixWord ++ tailWord_5983369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5983369).length < 2 ^ (prefixWord ++ tailWord_5983369).sum := by decide
  have hdescent : baseEnd_5983369 < baseStart_5983369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5983369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5983395 : List Nat := [1, 1, 1, 4, 1, 1, 1, 5, 2, 2, 4]
def baseStart_5983395 : Nat := 118140960795 + 5983395 * 2 ^ 59
def prefixEnd_5983395 : Nat := 4983230072969 + 3 ^ 40 * 5983395 * 2
def baseEnd_5983395 : Nat := 3072357580708722673245373

theorem tailTrace_5983395 : CollatzResearch.WordTrace tailWord_5983395 prefixEnd_5983395 3072357580708722673245373 := by
  unfold tailWord_5983395
  simp only [CollatzResearch.WordTrace]
  refine ⟨218232344158189272354887639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145488229438792848236591759 218232344158189272354887639)
  ·
    refine ⟨327348516237283908532331459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218232344158189272354887639 327348516237283908532331459)
    ·
      refine ⟨491022774355925862798497189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327348516237283908532331459 491022774355925862798497189)
      ·
        refine ⟨92066770191736099274718223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 491022774355925862798497189 92066770191736099274718223)
        ·
          refine ⟨138100155287604148912077335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92066770191736099274718223 138100155287604148912077335)
          ·
            refine ⟨207150232931406223368116003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138100155287604148912077335 207150232931406223368116003)
            ·
              refine ⟨310725349397109335052174005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207150232931406223368116003 310725349397109335052174005)
              ·
                refine ⟨29130501505979000161141313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 310725349397109335052174005 29130501505979000161141313)
                ·
                  refine ⟨21847876129484250120855985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29130501505979000161141313 21847876129484250120855985)
                  ·
                    refine ⟨16385907097113187590641989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21847876129484250120855985 16385907097113187590641989)
                    ·
                      refine ⟨3072357580708722673245373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16385907097113187590641989 3072357580708722673245373)
                      ·
                        rfl

theorem cell23_5983395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_5983395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5983395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5983395 prefixEnd_5983395 := by exact prefixLift 5983395
  have htrace : WordTrace (prefixWord ++ tailWord_5983395) baseStart_5983395 baseEnd_5983395 := by
    simpa [prefixWord, tailWord_5983395, baseEnd_5983395] using wordTrace_append hprefix tailTrace_5983395
  have hstable : (prefixWord ++ tailWord_5983395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5983395).length < 2 ^ (prefixWord ++ tailWord_5983395).sum := by decide
  have hdescent : baseEnd_5983395 < baseStart_5983395 := by decide
  rcases family_descends (prefixWord ++ tailWord_5983395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5983435 : List Nat := [1, 1, 1, 1, 3, 2, 2, 3, 4, 5]
def baseStart_5983435 : Nat := 118140960795 + 5983435 * 2 ^ 59
def prefixEnd_5983435 : Nat := 4983230072969 + 3 ^ 40 * 5983435 * 2
def baseEnd_5983435 : Nat := 1024126039978300838915063

theorem tailTrace_5983435 : CollatzResearch.WordTrace tailWord_5983435 prefixEnd_5983435 1024126039978300838915063 := by
  unfold tailWord_5983435
  simp only [CollatzResearch.WordTrace]
  refine ⟨218233803078044359186343759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145489202052029572790895839 218233803078044359186343759)
  ·
    refine ⟨327350704617066538779515639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218233803078044359186343759 327350704617066538779515639)
    ·
      refine ⟨491026056925599808169273459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327350704617066538779515639 491026056925599808169273459)
      ·
        refine ⟨736539085388399712253910189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491026056925599808169273459 736539085388399712253910189)
        ·
          refine ⟨276202157020649892095216321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 736539085388399712253910189 276202157020649892095216321)
          ·
            refine ⟨207151617765487419071412241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276202157020649892095216321 207151617765487419071412241)
            ·
              refine ⟨155363713324115564303559181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207151617765487419071412241 155363713324115564303559181)
              ·
                refine ⟨58261392496543336613834693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155363713324115564303559181 58261392496543336613834693)
                ·
                  refine ⟨10924011093101875615094005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58261392496543336613834693 10924011093101875615094005)
                  ·
                    refine ⟨1024126039978300838915063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10924011093101875615094005 1024126039978300838915063)
                    ·
                      rfl

theorem cell23_5983435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4, 5].length) (baseStart_5983435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5983435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5983435 prefixEnd_5983435 := by exact prefixLift 5983435
  have htrace : WordTrace (prefixWord ++ tailWord_5983435) baseStart_5983435 baseEnd_5983435 := by
    simpa [prefixWord, tailWord_5983435, baseEnd_5983435] using wordTrace_append hprefix tailTrace_5983435
  have hstable : (prefixWord ++ tailWord_5983435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5983435).length < 2 ^ (prefixWord ++ tailWord_5983435).sum := by decide
  have hdescent : baseEnd_5983435 < baseStart_5983435 := by decide
  rcases family_descends (prefixWord ++ tailWord_5983435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5983446 : List Nat := [5, 2, 1, 2, 2, 1, 1, 1, 2, 2, 4]
def baseStart_5983446 : Nat := 118140960795 + 5983446 * 2 ^ 59
def prefixEnd_5983446 : Nat := 4983230072969 + 3 ^ 40 * 5983446 * 2
def baseEnd_5983446 : Nat := 3072383768222101973707639

theorem tailTrace_5983446 : CollatzResearch.WordTrace tailWord_5983446 prefixEnd_5983446 3072383768222101973707639 := by
  unfold tailWord_5983446
  simp only [CollatzResearch.WordTrace]
  refine ⟨13639637767562781754062137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145489469520669672043329461 13639637767562781754062137)
  ·
    refine ⟨10229728325672086315546603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13639637767562781754062137 10229728325672086315546603)
    ·
      refine ⟨15344592488508129473319905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10229728325672086315546603 15344592488508129473319905)
      ·
        refine ⟨11508444366381097104989929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15344592488508129473319905 11508444366381097104989929)
        ·
          refine ⟨8631333274785822828742447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11508444366381097104989929 8631333274785822828742447)
          ·
            refine ⟨12946999912178734243113671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8631333274785822828742447 12946999912178734243113671)
            ·
              refine ⟨19420499868268101364670507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12946999912178734243113671 19420499868268101364670507)
              ·
                refine ⟨29130749802402152047005761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19420499868268101364670507 29130749802402152047005761)
                ·
                  refine ⟨21848062351801614035254321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29130749802402152047005761 21848062351801614035254321)
                  ·
                    refine ⟨16386046763851210526440741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21848062351801614035254321 16386046763851210526440741)
                    ·
                      refine ⟨3072383768222101973707639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16386046763851210526440741 3072383768222101973707639)
                      ·
                        rfl

theorem cell23_5983446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_5983446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5983446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5983446 prefixEnd_5983446 := by exact prefixLift 5983446
  have htrace : WordTrace (prefixWord ++ tailWord_5983446) baseStart_5983446 baseEnd_5983446 := by
    simpa [prefixWord, tailWord_5983446, baseEnd_5983446] using wordTrace_append hprefix tailTrace_5983446
  have hstable : (prefixWord ++ tailWord_5983446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5983446).length < 2 ^ (prefixWord ++ tailWord_5983446).sum := by decide
  have hdescent : baseEnd_5983446 < baseStart_5983446 := by decide
  rcases family_descends (prefixWord ++ tailWord_5983446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5983469 : List Nat := [1, 5, 1, 2, 2, 1, 3, 1, 2, 5]
def baseStart_5983469 : Nat := 118140960795 + 5983469 * 2 ^ 59
def prefixEnd_5983469 : Nat := 4983230072969 + 3 ^ 40 * 5983469 * 2
def baseEnd_5983469 : Nat := 1024131859425718461240011

theorem tailTrace_5983469 : CollatzResearch.WordTrace tailWord_5983469 prefixEnd_5983469 1024131859425718461240011 := by
  unfold tailWord_5983469
  simp only [CollatzResearch.WordTrace]
  refine ⟨218235043159921182993081461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145490028773280788662054307 218235043159921182993081461)
  ·
    refine ⟨20459535296242610905601387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 218235043159921182993081461 20459535296242610905601387)
    ·
      refine ⟨30689302944363916358402081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20459535296242610905601387 30689302944363916358402081)
      ·
        refine ⟨23016977208272937268801561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30689302944363916358402081 23016977208272937268801561)
        ·
          refine ⟨17262732906204702951601171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23016977208272937268801561 17262732906204702951601171)
          ·
            refine ⟨25894099359307054427401757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17262732906204702951601171 25894099359307054427401757)
            ·
              refine ⟨9710287259740145410275659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25894099359307054427401757 9710287259740145410275659)
              ·
                refine ⟨14565430889610218115413489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9710287259740145410275659 14565430889610218115413489)
                ·
                  refine ⟨10924073167207663586560117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14565430889610218115413489 10924073167207663586560117)
                  ·
                    refine ⟨1024131859425718461240011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10924073167207663586560117 1024131859425718461240011)
                    ·
                      rfl

theorem cell23_5983469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_5983469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5983469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5983469 prefixEnd_5983469 := by exact prefixLift 5983469
  have htrace : WordTrace (prefixWord ++ tailWord_5983469) baseStart_5983469 baseEnd_5983469 := by
    simpa [prefixWord, tailWord_5983469, baseEnd_5983469] using wordTrace_append hprefix tailTrace_5983469
  have hstable : (prefixWord ++ tailWord_5983469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5983469).length < 2 ^ (prefixWord ++ tailWord_5983469).sum := by decide
  have hdescent : baseEnd_5983469 < baseStart_5983469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5983469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5983482 : List Nat := [3, 1, 1, 1, 1, 4, 1, 2, 5, 4]
def baseStart_5983482 : Nat := 118140960795 + 5983482 * 2 ^ 59
def prefixEnd_5983482 : Nat := 4983230072969 + 3 ^ 40 * 5983482 * 2
def baseEnd_5983482 : Nat := 1024134084508554610952491

theorem tailTrace_5983482 : CollatzResearch.WordTrace tailWord_5983482 prefixEnd_5983482 1024134084508554610952491 := by
  unfold tailWord_5983482
  simp only [CollatzResearch.WordTrace]
  refine ⟨54558879327218521553326175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145490344872582724142203133 54558879327218521553326175)
  ·
    refine ⟨81838318990827782329989263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54558879327218521553326175 81838318990827782329989263)
    ·
      refine ⟨122757478486241673494983895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81838318990827782329989263 122757478486241673494983895)
      ·
        refine ⟨184136217729362510242475843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122757478486241673494983895 184136217729362510242475843)
        ·
          refine ⟨276204326594043765363713765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184136217729362510242475843 276204326594043765363713765)
          ·
            refine ⟨51788311236383206005696331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 276204326594043765363713765 51788311236383206005696331)
            ·
              refine ⟨77682466854574809008544497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51788311236383206005696331 77682466854574809008544497)
              ·
                refine ⟨58261850140931106756408373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77682466854574809008544497 58261850140931106756408373)
                ·
                  refine ⟨5462048450712291258413285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58261850140931106756408373 5462048450712291258413285)
                  ·
                    refine ⟨1024134084508554610952491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5462048450712291258413285 1024134084508554610952491)
                    ·
                      rfl

theorem cell23_5983482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 5, 4].length) (baseStart_5983482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5983482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5983482 prefixEnd_5983482 := by exact prefixLift 5983482
  have htrace : WordTrace (prefixWord ++ tailWord_5983482) baseStart_5983482 baseEnd_5983482 := by
    simpa [prefixWord, tailWord_5983482, baseEnd_5983482] using wordTrace_append hprefix tailTrace_5983482
  have hstable : (prefixWord ++ tailWord_5983482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5983482).length < 2 ^ (prefixWord ++ tailWord_5983482).sum := by decide
  have hdescent : baseEnd_5983482 < baseStart_5983482 := by decide
  rcases family_descends (prefixWord ++ tailWord_5983482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5983489 : List Nat := [1, 2, 4, 1, 1, 3, 1, 2, 2, 4, 2]
def baseStart_5983489 : Nat := 118140960795 + 5983489 * 2 ^ 59
def prefixEnd_5983489 : Nat := 4983230072969 + 3 ^ 40 * 5983489 * 2
def baseEnd_5983489 : Nat := 3072405847890245305469941

theorem tailTrace_5983489 : CollatzResearch.WordTrace tailWord_5983489 prefixEnd_5983489 3072405847890245305469941 := by
  unfold tailWord_5983489
  simp only [CollatzResearch.WordTrace]
  refine ⟨218235772619848726408809521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145490515079899150939206347 218235772619848726408809521)
  ·
    refine ⟨163676829464886544806607141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218235772619848726408809521 163676829464886544806607141)
    ·
      refine ⟨30689405524666227151238839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163676829464886544806607141 30689405524666227151238839)
      ·
        refine ⟨46034108286999340726858259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30689405524666227151238839 46034108286999340726858259)
        ·
          refine ⟨69051162430499011090287389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46034108286999340726858259 69051162430499011090287389)
          ·
            refine ⟨25894185911437129158857771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69051162430499011090287389 25894185911437129158857771)
            ·
              refine ⟨38841278867155693738286657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25894185911437129158857771 38841278867155693738286657)
              ·
                refine ⟨29130959150366770303714993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38841278867155693738286657 29130959150366770303714993)
                ·
                  refine ⟨21848219362775077727786245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29130959150366770303714993 21848219362775077727786245)
                  ·
                    refine ⟨4096541130520327073959921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21848219362775077727786245 4096541130520327073959921)
                    ·
                      refine ⟨3072405847890245305469941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4096541130520327073959921 3072405847890245305469941)
                      ·
                        rfl

theorem cell23_5983489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 4, 2].length) (baseStart_5983489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5983489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5983489 prefixEnd_5983489 := by exact prefixLift 5983489
  have htrace : WordTrace (prefixWord ++ tailWord_5983489) baseStart_5983489 baseEnd_5983489 := by
    simpa [prefixWord, tailWord_5983489, baseEnd_5983489] using wordTrace_append hprefix tailTrace_5983489
  have hstable : (prefixWord ++ tailWord_5983489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5983489).length < 2 ^ (prefixWord ++ tailWord_5983489).sum := by decide
  have hdescent : baseEnd_5983489 < baseStart_5983489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5983489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5983499 : List Nat := [1, 1, 1, 1, 5, 4, 2, 1, 3, 4]
def baseStart_5983499 : Nat := 118140960795 + 5983499 * 2 ^ 59
def prefixEnd_5983499 : Nat := 4983230072969 + 3 ^ 40 * 5983499 * 2
def baseEnd_5983499 : Nat := 1024136994232263422114965

theorem tailTrace_5983499 : CollatzResearch.WordTrace tailWord_5983499 prefixEnd_5983499 1024136994232263422114965 := by
  unfold tailWord_5983499
  simp only [CollatzResearch.WordTrace]
  refine ⟨218236137349812498116673551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145490758233208332077782367 218236137349812498116673551)
  ·
    refine ⟨327354206024718747175010327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218236137349812498116673551 327354206024718747175010327)
    ·
      refine ⟨491031309037078120762515491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327354206024718747175010327 491031309037078120762515491)
      ·
        refine ⟨736546963555617181143773237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491031309037078120762515491 736546963555617181143773237)
        ·
          refine ⟨69051277833339110732228741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 736546963555617181143773237 69051277833339110732228741)
          ·
            refine ⟨12947114593751083262292889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69051277833339110732228741 12947114593751083262292889)
            ·
              refine ⟨9710335945313312446719667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12947114593751083262292889 9710335945313312446719667)
              ·
                refine ⟨14565503917969968670079501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9710335945313312446719667 14565503917969968670079501)
                ·
                  refine ⟨5462063969238738251279813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14565503917969968670079501 5462063969238738251279813)
                  ·
                    refine ⟨1024136994232263422114965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5462063969238738251279813 1024136994232263422114965)
                    ·
                      rfl

theorem cell23_5983499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 3, 4].length) (baseStart_5983499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5983499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5983499 prefixEnd_5983499 := by exact prefixLift 5983499
  have htrace : WordTrace (prefixWord ++ tailWord_5983499) baseStart_5983499 baseEnd_5983499 := by
    simpa [prefixWord, tailWord_5983499, baseEnd_5983499] using wordTrace_append hprefix tailTrace_5983499
  have hstable : (prefixWord ++ tailWord_5983499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5983499).length < 2 ^ (prefixWord ++ tailWord_5983499).sum := by decide
  have hdescent : baseEnd_5983499 < baseStart_5983499 := by decide
  rcases family_descends (prefixWord ++ tailWord_5983499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5983515 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 6]
def baseStart_5983515 : Nat := 118140960795 + 5983515 * 2 ^ 59
def prefixEnd_5983515 : Nat := 4983230072969 + 3 ^ 40 * 5983515 * 2
def baseEnd_5983515 : Nat := 3072419198387262203744821

theorem tailTrace_5983515 : CollatzResearch.WordTrace tailWord_5983515 prefixEnd_5983515 3072419198387262203744821 := by
  unfold tailWord_5983515
  simp only [CollatzResearch.WordTrace]
  refine ⟨218236720917754532849255999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145491147278503021899503999 218236720917754532849255999)
  ·
    refine ⟨327355081376631799273883999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218236720917754532849255999 327355081376631799273883999)
    ·
      refine ⟨491032622064947698910825999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327355081376631799273883999 491032622064947698910825999)
      ·
        refine ⟨736548933097421548366238999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491032622064947698910825999 736548933097421548366238999)
        ·
          refine ⟨1104823399646132322549358499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 736548933097421548366238999 1104823399646132322549358499)
          ·
            refine ⟨1657235099469198483824037749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1104823399646132322549358499 1657235099469198483824037749)
            ·
              refine ⟨155365790575237357858503539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1657235099469198483824037749 155365790575237357858503539)
              ·
                refine ⟨233048685862856036787755309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155365790575237357858503539 233048685862856036787755309)
                ·
                  refine ⟨87393257198571013795408241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 233048685862856036787755309 87393257198571013795408241)
                  ·
                    refine ⟨65544942898928260346556181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 87393257198571013795408241 65544942898928260346556181)
                    ·
                      refine ⟨3072419198387262203744821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65544942898928260346556181 3072419198387262203744821)
                      ·
                        rfl

theorem cell23_5983515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 6].length) (baseStart_5983515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5983515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5983515 prefixEnd_5983515 := by exact prefixLift 5983515
  have htrace : WordTrace (prefixWord ++ tailWord_5983515) baseStart_5983515 baseEnd_5983515 := by
    simpa [prefixWord, tailWord_5983515, baseEnd_5983515] using wordTrace_append hprefix tailTrace_5983515
  have hstable : (prefixWord ++ tailWord_5983515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5983515).length < 2 ^ (prefixWord ++ tailWord_5983515).sum := by decide
  have hdescent : baseEnd_5983515 < baseStart_5983515 := by decide
  rcases family_descends (prefixWord ++ tailWord_5983515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5983619 : List Nat := [1, 1, 1, 3, 5, 3, 1, 8]
def baseStart_5983619 : Nat := 118140960795 + 5983619 * 2 ^ 59
def prefixEnd_5983619 : Nat := 4983230072969 + 3 ^ 40 * 5983619 * 2
def baseEnd_5983619 : Nat := 113795281495382585068309

theorem tailTrace_5983619 : CollatzResearch.WordTrace tailWord_5983619 prefixEnd_5983619 113795281495382585068309 := by
  unfold tailWord_5983619
  simp only [CollatzResearch.WordTrace]
  refine ⟨218240514109377758611041911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145493676072918505740694607 218240514109377758611041911)
  ·
    refine ⟨327360771164066637916562867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218240514109377758611041911 327360771164066637916562867)
    ·
      refine ⟨491041156746099956874844301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327360771164066637916562867 491041156746099956874844301)
      ·
        refine ⟨184140433779787483828066613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 491041156746099956874844301 184140433779787483828066613)
        ·
          refine ⟨17263165666855076608881245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 184140433779787483828066613 17263165666855076608881245)
          ·
            refine ⟨6473687125070653728330467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17263165666855076608881245 6473687125070653728330467)
            ·
              refine ⟨9710530687605980592495701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6473687125070653728330467 9710530687605980592495701)
              ·
                refine ⟨113795281495382585068309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9710530687605980592495701 113795281495382585068309)
                ·
                  rfl

theorem cell23_5983619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 8].length) (baseStart_5983619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5983619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5983619 prefixEnd_5983619 := by exact prefixLift 5983619
  have htrace : WordTrace (prefixWord ++ tailWord_5983619) baseStart_5983619 baseEnd_5983619 := by
    simpa [prefixWord, tailWord_5983619, baseEnd_5983619] using wordTrace_append hprefix tailTrace_5983619
  have hstable : (prefixWord ++ tailWord_5983619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5983619).length < 2 ^ (prefixWord ++ tailWord_5983619).sum := by decide
  have hdescent : baseEnd_5983619 < baseStart_5983619 := by decide
  rcases family_descends (prefixWord ++ tailWord_5983619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5983630 : List Nat := [4, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2]
def baseStart_5983630 : Nat := 118140960795 + 5983630 * 2 ^ 59
def prefixEnd_5983630 : Nat := 4983230072969 + 3 ^ 40 * 5983630 * 2
def baseEnd_5983630 : Nat := 3072478248662529253806793

theorem tailTrace_5983630 : CollatzResearch.WordTrace tailWord_5983630 prefixEnd_5983630 3072478248662529253806793 := by
  unfold tailWord_5983630
  simp only [CollatzResearch.WordTrace]
  refine ⟨27280114414042238436211543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145493943541558604993128229 27280114414042238436211543)
  ·
    refine ⟨40920171621063357654317315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27280114414042238436211543 40920171621063357654317315)
    ·
      refine ⟨61380257431595036481475973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40920171621063357654317315 61380257431595036481475973)
      ·
        refine ⟨11508798268424069340276745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61380257431595036481475973 11508798268424069340276745)
        ·
          refine ⟨8631598701318052005207559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11508798268424069340276745 8631598701318052005207559)
          ·
            refine ⟨12947398051977078007811339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8631598701318052005207559 12947398051977078007811339)
            ·
              refine ⟨19421097077965617011717009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12947398051977078007811339 19421097077965617011717009)
              ·
                refine ⟨14565822808474212758787757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19421097077965617011717009 14565822808474212758787757)
                ·
                  refine ⟨5462183553177829784545409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14565822808474212758787757 5462183553177829784545409)
                  ·
                    refine ⟨4096637664883372338409057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5462183553177829784545409 4096637664883372338409057)
                    ·
                      refine ⟨3072478248662529253806793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4096637664883372338409057 3072478248662529253806793)
                      ·
                        rfl

theorem cell23_5983630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_5983630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5983630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5983630 prefixEnd_5983630 := by exact prefixLift 5983630
  have htrace : WordTrace (prefixWord ++ tailWord_5983630) baseStart_5983630 baseEnd_5983630 := by
    simpa [prefixWord, tailWord_5983630, baseEnd_5983630] using wordTrace_append hprefix tailTrace_5983630
  have hstable : (prefixWord ++ tailWord_5983630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5983630).length < 2 ^ (prefixWord ++ tailWord_5983630).sum := by decide
  have hdescent : baseEnd_5983630 < baseStart_5983630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5983630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5983636 : List Nat := [2, 4, 2, 1, 2, 2, 3, 7]
def baseStart_5983636 : Nat := 118140960795 + 5983636 * 2 ^ 59
def prefixEnd_5983636 : Nat := 4983230072969 + 3 ^ 40 * 5983636 * 2
def baseEnd_5983636 : Nat := 113795604798016897419695

theorem tailTrace_5983636 : CollatzResearch.WordTrace tailWord_5983636 prefixEnd_5983636 113795604798016897419695 := by
  unfold tailWord_5983636
  simp only [CollatzResearch.WordTrace]
  refine ⟨109120567075158085257205381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145494089433544113676273841 109120567075158085257205381)
  ·
    refine ⟨20460106326592140985726009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109120567075158085257205381 20460106326592140985726009)
    ·
      refine ⟨15345079744944105739294507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20460106326592140985726009 15345079744944105739294507)
      ·
        refine ⟨23017619617416158608941761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15345079744944105739294507 23017619617416158608941761)
        ·
          refine ⟨17263214713062118956706321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23017619617416158608941761 17263214713062118956706321)
          ·
            refine ⟨12947411034796589217529741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17263214713062118956706321 12947411034796589217529741)
            ·
              refine ⟨4855279138048720956573653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12947411034796589217529741 4855279138048720956573653)
              ·
                refine ⟨113795604798016897419695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4855279138048720956573653 113795604798016897419695)
                ·
                  rfl

theorem cell23_5983636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 7].length) (baseStart_5983636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5983636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5983636 prefixEnd_5983636 := by exact prefixLift 5983636
  have htrace : WordTrace (prefixWord ++ tailWord_5983636) baseStart_5983636 baseEnd_5983636 := by
    simpa [prefixWord, tailWord_5983636, baseEnd_5983636] using wordTrace_append hprefix tailTrace_5983636
  have hstable : (prefixWord ++ tailWord_5983636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5983636).length < 2 ^ (prefixWord ++ tailWord_5983636).sum := by decide
  have hdescent : baseEnd_5983636 < baseStart_5983636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5983636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5983650 : List Nat := [3, 3, 1, 2, 1, 4, 2, 1, 1, 2, 3]
def baseStart_5983650 : Nat := 118140960795 + 5983650 * 2 ^ 59
def prefixEnd_5983650 : Nat := 4983230072969 + 3 ^ 40 * 5983650 * 2
def baseEnd_5983650 : Nat := 3072488518275619175556701

theorem tailTrace_5983650 : CollatzResearch.WordTrace tailWord_5983650 prefixEnd_5983650 3072488518275619175556701 := by
  unfold tailWord_5983650
  simp only [CollatzResearch.WordTrace]
  refine ⟨54560411193066362726355101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145494429848176967270280269 54560411193066362726355101)
  ·
    refine ⟨20460154197399886022383163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54560411193066362726355101 20460154197399886022383163)
    ·
      refine ⟨30690231296099829033574745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20460154197399886022383163 30690231296099829033574745)
      ·
        refine ⟨23017673472074871775181059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30690231296099829033574745 23017673472074871775181059)
        ·
          refine ⟨34526510208112307662771589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23017673472074871775181059 34526510208112307662771589)
          ·
            refine ⟨6473720664021057686769673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34526510208112307662771589 6473720664021057686769673)
            ·
              refine ⟨4855290498015793265077255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6473720664021057686769673 4855290498015793265077255)
              ·
                refine ⟨7282935747023689897615883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4855290498015793265077255 7282935747023689897615883)
                ·
                  refine ⟨10924403620535534846423825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7282935747023689897615883 10924403620535534846423825)
                  ·
                    refine ⟨8193302715401651134817869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10924403620535534846423825 8193302715401651134817869)
                    ·
                      refine ⟨3072488518275619175556701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8193302715401651134817869 3072488518275619175556701)
                      ·
                        rfl

theorem cell23_5983650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_5983650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5983650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5983650 prefixEnd_5983650 := by exact prefixLift 5983650
  have htrace : WordTrace (prefixWord ++ tailWord_5983650) baseStart_5983650 baseEnd_5983650 := by
    simpa [prefixWord, tailWord_5983650, baseEnd_5983650] using wordTrace_append hprefix tailTrace_5983650
  have hstable : (prefixWord ++ tailWord_5983650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5983650).length < 2 ^ (prefixWord ++ tailWord_5983650).sum := by decide
  have hdescent : baseEnd_5983650 < baseStart_5983650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5983650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5983820 : List Nat := [2, 2, 1, 3, 1, 4, 2, 3, 1, 4]
def baseStart_5983820 : Nat := 118140960795 + 5983820 * 2 ^ 59
def prefixEnd_5983820 : Nat := 4983230072969 + 3 ^ 40 * 5983820 * 2
def baseEnd_5983820 : Nat := 1024191936662294503476973

theorem tailTrace_5983820 : CollatzResearch.WordTrace tailWord_5983820 prefixEnd_5983820 1024191936662294503476973 := by
  unfold tailWord_5983820
  simp only [CollatzResearch.WordTrace]
  refine ⟨109123922590824784969554457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145498563454433046626072609 109123922590824784969554457)
  ·
    refine ⟨81842941943118588727165843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109123922590824784969554457 81842941943118588727165843)
    ·
      refine ⟨122764412914677883090748765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81842941943118588727165843 122764412914677883090748765)
      ·
        refine ⟨46036654843004206159030787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122764412914677883090748765 46036654843004206159030787)
        ·
          refine ⟨69054982264506309238546181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46036654843004206159030787 69054982264506309238546181)
          ·
            refine ⟨12947809174594932982227409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69054982264506309238546181 12947809174594932982227409)
            ·
              refine ⟨9710856880946199736670557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12947809174594932982227409 9710856880946199736670557)
              ·
                refine ⟨3641571330354824901251459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9710856880946199736670557 3641571330354824901251459)
                ·
                  refine ⟨5462356995532237351877189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3641571330354824901251459 5462356995532237351877189)
                  ·
                    refine ⟨1024191936662294503476973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5462356995532237351877189 1024191936662294503476973)
                    ·
                      rfl

theorem cell23_5983820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 3, 1, 4].length) (baseStart_5983820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5983820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5983820 prefixEnd_5983820 := by exact prefixLift 5983820
  have htrace : WordTrace (prefixWord ++ tailWord_5983820) baseStart_5983820 baseEnd_5983820 := by
    simpa [prefixWord, tailWord_5983820, baseEnd_5983820] using wordTrace_append hprefix tailTrace_5983820
  have hstable : (prefixWord ++ tailWord_5983820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5983820).length < 2 ^ (prefixWord ++ tailWord_5983820).sum := by decide
  have hdescent : baseEnd_5983820 < baseStart_5983820 := by decide
  rcases family_descends (prefixWord ++ tailWord_5983820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5983836 : List Nat := [2, 2, 4, 1, 2, 1, 1, 1, 1, 2, 6]
def baseStart_5983836 : Nat := 118140960795 + 5983836 * 2 ^ 59
def prefixEnd_5983836 : Nat := 4983230072969 + 3 ^ 40 * 5983836 * 2
def baseEnd_5983836 : Nat := 3072584025677355447830845

theorem tailTrace_5983836 : CollatzResearch.WordTrace tailWord_5983836 prefixEnd_5983836 3072584025677355447830845 := by
  unfold tailWord_5983836
  simp only [CollatzResearch.WordTrace]
  refine ⟨109124214374795802335845681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145498952499727736447794241 109124214374795802335845681)
  ·
    refine ⟨81843160781096851751884261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109124214374795802335845681 81843160781096851751884261)
    ·
      refine ⟨15345592646455659703478299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81843160781096851751884261 15345592646455659703478299)
      ·
        refine ⟨23018388969683489555217449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15345592646455659703478299 23018388969683489555217449)
        ·
          refine ⟨17263791727262617166413087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23018388969683489555217449 17263791727262617166413087)
          ·
            refine ⟨25895687590893925749619631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17263791727262617166413087 25895687590893925749619631)
            ·
              refine ⟨38843531386340888624429447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25895687590893925749619631 38843531386340888624429447)
              ·
                refine ⟨58265297079511332936644171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38843531386340888624429447 58265297079511332936644171)
                ·
                  refine ⟨87397945619266999404966257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58265297079511332936644171 87397945619266999404966257)
                  ·
                    refine ⟨65548459214450249553724693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 87397945619266999404966257 65548459214450249553724693)
                    ·
                      refine ⟨3072584025677355447830845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65548459214450249553724693 3072584025677355447830845)
                      ·
                        rfl

theorem cell23_5983836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_5983836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5983836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5983836 prefixEnd_5983836 := by exact prefixLift 5983836
  have htrace : WordTrace (prefixWord ++ tailWord_5983836) baseStart_5983836 baseEnd_5983836 := by
    simpa [prefixWord, tailWord_5983836, baseEnd_5983836] using wordTrace_append hprefix tailTrace_5983836
  have hstable : (prefixWord ++ tailWord_5983836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5983836).length < 2 ^ (prefixWord ++ tailWord_5983836).sum := by decide
  have hdescent : baseEnd_5983836 < baseStart_5983836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5983836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5983837 : List Nat := [1, 4, 4, 2, 1, 1, 2, 1, 3, 4]
def baseStart_5983837 : Nat := 118140960795 + 5983837 * 2 ^ 59
def prefixEnd_5983837 : Nat := 4983230072969 + 3 ^ 40 * 5983837 * 2
def baseEnd_5983837 : Nat := 1024194846386003314639447

theorem tailTrace_5983837 : CollatzResearch.WordTrace tailWord_5983837 prefixEnd_5983837 1024194846386003314639447 := by
  unfold tailWord_5983837
  simp only [CollatzResearch.WordTrace]
  refine ⟨218248465222587981842477765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145498976815058654561651843 218248465222587981842477765)
  ·
    refine ⟨40921587229235246595464581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 218248465222587981842477765 40921587229235246595464581)
    ·
      refine ⟨7672797605481608736649609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40921587229235246595464581 7672797605481608736649609)
      ·
        refine ⟨5754598204111206552487207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7672797605481608736649609 5754598204111206552487207)
        ·
          refine ⟨8631897306166809828730811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5754598204111206552487207 8631897306166809828730811)
          ·
            refine ⟨12947845959250214743096217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8631897306166809828730811 12947845959250214743096217)
            ·
              refine ⟨9710884469437661057322163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12947845959250214743096217 9710884469437661057322163)
              ·
                refine ⟨14566326704156491585983245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9710884469437661057322163 14566326704156491585983245)
                ·
                  refine ⟨5462372514058684344743717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14566326704156491585983245 5462372514058684344743717)
                  ·
                    refine ⟨1024194846386003314639447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5462372514058684344743717 1024194846386003314639447)
                    ·
                      rfl

theorem cell23_5983837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_5983837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5983837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5983837 prefixEnd_5983837 := by exact prefixLift 5983837
  have htrace : WordTrace (prefixWord ++ tailWord_5983837) baseStart_5983837 baseEnd_5983837 := by
    simpa [prefixWord, tailWord_5983837, baseEnd_5983837] using wordTrace_append hprefix tailTrace_5983837
  have hstable : (prefixWord ++ tailWord_5983837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5983837).length < 2 ^ (prefixWord ++ tailWord_5983837).sum := by decide
  have hdescent : baseEnd_5983837 < baseStart_5983837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5983837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5983843 : List Nat := [1, 1, 1, 5, 1, 3, 1, 3, 3, 1, 3]
def baseStart_5983843 : Nat := 118140960795 + 5983843 * 2 ^ 59
def prefixEnd_5983843 : Nat := 4983230072969 + 3 ^ 40 * 5983843 * 2
def baseEnd_5983843 : Nat := 3072587620041936920443313

theorem tailTrace_5983843 : CollatzResearch.WordTrace tailWord_5983843 prefixEnd_5983843 3072587620041936920443313 := by
  unfold tailWord_5983843
  simp only [CollatzResearch.WordTrace]
  refine ⟨218248684060566244867196183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145499122707044163244797455 218248684060566244867196183)
  ·
    refine ⟨327373026090849367300794275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218248684060566244867196183 327373026090849367300794275)
    ·
      refine ⟨491059539136274050951191413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327373026090849367300794275 491059539136274050951191413)
      ·
        refine ⟨46036831794025692276674195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 491059539136274050951191413 46036831794025692276674195)
        ·
          refine ⟨69055247691038538415011293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46036831794025692276674195 69055247691038538415011293)
          ·
            refine ⟨25895717884139451905629235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69055247691038538415011293 25895717884139451905629235)
            ·
              refine ⟨38843576826209177858443853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25895717884139451905629235 38843576826209177858443853)
              ·
                refine ⟨14566341309828441696916445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38843576826209177858443853 14566341309828441696916445)
                ·
                  refine ⟨5462377991185665636343667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14566341309828441696916445 5462377991185665636343667)
                  ·
                    refine ⟨8193566986778498454515501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5462377991185665636343667 8193566986778498454515501)
                    ·
                      refine ⟨3072587620041936920443313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8193566986778498454515501 3072587620041936920443313)
                      ·
                        rfl

theorem cell23_5983843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_5983843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5983843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5983843 prefixEnd_5983843 := by exact prefixLift 5983843
  have htrace : WordTrace (prefixWord ++ tailWord_5983843) baseStart_5983843 baseEnd_5983843 := by
    simpa [prefixWord, tailWord_5983843, baseEnd_5983843] using wordTrace_append hprefix tailTrace_5983843
  have hstable : (prefixWord ++ tailWord_5983843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5983843).length < 2 ^ (prefixWord ++ tailWord_5983843).sum := by decide
  have hdescent : baseEnd_5983843 < baseStart_5983843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5983843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5983896 : List Nat := [2, 1, 2, 4, 1, 2, 1, 2, 1, 1, 6]
def baseStart_5983896 : Nat := 118140960795 + 5983896 * 2 ^ 59
def prefixEnd_5983896 : Nat := 4983230072969 + 3 ^ 40 * 5983896 * 2
def baseEnd_5983896 : Nat := 3072614834516625213080569

theorem tailTrace_5983896 : CollatzResearch.WordTrace tailWord_5983896 prefixEnd_5983896 3072614834516625213080569 := by
  unfold tailWord_5983896
  simp only [CollatzResearch.WordTrace]
  refine ⟨109125308564687117459437771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145500411419582823279250361 109125308564687117459437771)
  ·
    refine ⟨163687962847030676189156657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109125308564687117459437771 163687962847030676189156657)
    ·
      refine ⟨122765972135273007141867493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163687962847030676189156657 122765972135273007141867493)
      ·
        refine ⟨23018619775363688839100155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122765972135273007141867493 23018619775363688839100155)
        ·
          refine ⟨34527929663045533258650233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23018619775363688839100155 34527929663045533258650233)
          ·
            refine ⟨25895947247284149943987675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34527929663045533258650233 25895947247284149943987675)
            ·
              refine ⟨38843920870926224915981513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25895947247284149943987675 38843920870926224915981513)
              ·
                refine ⟨29132940653194668686986135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38843920870926224915981513 29132940653194668686986135)
                ·
                  refine ⟨43699410979792003030479203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29132940653194668686986135 43699410979792003030479203)
                  ·
                    refine ⟨65549116469688004545718805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43699410979792003030479203 65549116469688004545718805)
                    ·
                      refine ⟨3072614834516625213080569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65549116469688004545718805 3072614834516625213080569)
                      ·
                        rfl

theorem cell23_5983896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_5983896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5983896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5983896 prefixEnd_5983896 := by exact prefixLift 5983896
  have htrace : WordTrace (prefixWord ++ tailWord_5983896) baseStart_5983896 baseEnd_5983896 := by
    simpa [prefixWord, tailWord_5983896, baseEnd_5983896] using wordTrace_append hprefix tailTrace_5983896
  have hstable : (prefixWord ++ tailWord_5983896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5983896).length < 2 ^ (prefixWord ++ tailWord_5983896).sum := by decide
  have hdescent : baseEnd_5983896 < baseStart_5983896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5983896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5983916 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 3]
def baseStart_5983916 : Nat := 118140960795 + 5983916 * 2 ^ 59
def prefixEnd_5983916 : Nat := 4983230072969 + 3 ^ 40 * 5983916 * 2
def baseEnd_5983916 : Nat := 3072625104129715134830477

theorem tailTrace_5983916 : CollatzResearch.WordTrace tailWord_5983916 prefixEnd_5983916 3072625104129715134830477 := by
  unfold tailWord_5983916
  simp only [CollatzResearch.WordTrace]
  refine ⟨109125673294650889167301801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145500897726201185556402401 109125673294650889167301801)
  ·
    refine ⟨81844254970988166875476351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109125673294650889167301801 81844254970988166875476351)
    ·
      refine ⟨122766382456482250313214527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81844254970988166875476351 122766382456482250313214527)
      ·
        refine ⟨184149573684723375469821791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122766382456482250313214527 184149573684723375469821791)
        ·
          refine ⟨276224360527085063204732687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184149573684723375469821791 276224360527085063204732687)
          ·
            refine ⟨414336540790627594807099031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276224360527085063204732687 414336540790627594807099031)
            ·
              refine ⟨621504811185941392210648547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414336540790627594807099031 621504811185941392210648547)
              ·
                refine ⟨932257216778912088315972821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 621504811185941392210648547 932257216778912088315972821)
                ·
                  refine ⟨21849778518255752069905613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 932257216778912088315972821 21849778518255752069905613)
                  ·
                    refine ⟨8193666944345907026214605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21849778518255752069905613 8193666944345907026214605)
                    ·
                      refine ⟨3072625104129715134830477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8193666944345907026214605 3072625104129715134830477)
                      ·
                        rfl

theorem cell23_5983916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 3].length) (baseStart_5983916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5983916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5983916 prefixEnd_5983916 := by exact prefixLift 5983916
  have htrace : WordTrace (prefixWord ++ tailWord_5983916) baseStart_5983916 baseEnd_5983916 := by
    simpa [prefixWord, tailWord_5983916, baseEnd_5983916] using wordTrace_append hprefix tailTrace_5983916
  have hstable : (prefixWord ++ tailWord_5983916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5983916).length < 2 ^ (prefixWord ++ tailWord_5983916).sum := by decide
  have hdescent : baseEnd_5983916 < baseStart_5983916 := by decide
  rcases family_descends (prefixWord ++ tailWord_5983916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5983933 : List Nat := [1, 4, 1, 2, 1, 2, 3, 2, 1, 3, 3]
def baseStart_5983933 : Nat := 118140960795 + 5983933 * 2 ^ 59
def prefixEnd_5983933 : Nat := 4983230072969 + 3 ^ 40 * 5983933 * 2
def baseEnd_5983933 : Nat := 3072633833300841568317899

theorem tailTrace_5983933 : CollatzResearch.WordTrace tailWord_5983933 prefixEnd_5983933 3072633833300841568317899 := by
  unfold tailWord_5983933
  simp only [CollatzResearch.WordTrace]
  refine ⟨218251966630240190237972453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145501311086826793491981635 218251966630240190237972453)
  ·
    refine ⟨40922243743170035669619835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 218251966630240190237972453 40922243743170035669619835)
    ·
      refine ⟨61383365614755053504429753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40922243743170035669619835 61383365614755053504429753)
      ·
        refine ⟨46037524211066290128322315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61383365614755053504429753 46037524211066290128322315)
        ·
          refine ⟨69056286316599435192483473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46037524211066290128322315 69056286316599435192483473)
          ·
            refine ⟨51792214737449576394362605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69056286316599435192483473 51792214737449576394362605)
            ·
              refine ⟨19422080526543591147885977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51792214737449576394362605 19422080526543591147885977)
              ·
                refine ⟨14566560394907693360914483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19422080526543591147885977 14566560394907693360914483)
                ·
                  refine ⟨21849840592361540041371725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14566560394907693360914483 21849840592361540041371725)
                  ·
                    refine ⟨8193690222135577515514397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21849840592361540041371725 8193690222135577515514397)
                    ·
                      refine ⟨3072633833300841568317899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8193690222135577515514397 3072633833300841568317899)
                      ·
                        rfl

theorem cell23_5983933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_5983933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5983933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5983933 prefixEnd_5983933 := by exact prefixLift 5983933
  have htrace : WordTrace (prefixWord ++ tailWord_5983933) baseStart_5983933 baseEnd_5983933 := by
    simpa [prefixWord, tailWord_5983933, baseEnd_5983933] using wordTrace_append hprefix tailTrace_5983933
  have hstable : (prefixWord ++ tailWord_5983933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5983933).length < 2 ^ (prefixWord ++ tailWord_5983933).sum := by decide
  have hdescent : baseEnd_5983933 < baseStart_5983933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5983933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5983996 : List Nat := [2, 2, 2, 1, 3, 1, 1, 2, 9]
def baseStart_5983996 : Nat := 118140960795 + 5983996 * 2 ^ 59
def prefixEnd_5983996 : Nat := 4983230072969 + 3 ^ 40 * 5983996 * 2
def baseEnd_5983996 : Nat := 341407353620230535758901

theorem tailTrace_5983996 : CollatzResearch.WordTrace tailWord_5983996 prefixEnd_5983996 341407353620230535758901 := by
  unfold tailWord_5983996
  simp only [CollatzResearch.WordTrace]
  refine ⟨109127132214505975998757921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145502842952674634665010561 109127132214505975998757921)
  ·
    refine ⟨81845349160879481999068441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109127132214505975998757921 81845349160879481999068441)
    ·
      refine ⟨61384011870659611499301331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81845349160879481999068441 61384011870659611499301331)
      ·
        refine ⟨92076017805989417248951997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61384011870659611499301331 92076017805989417248951997)
        ·
          refine ⟨34528506677246031468356999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92076017805989417248951997 34528506677246031468356999)
          ·
            refine ⟨51792760015869047202535499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34528506677246031468356999 51792760015869047202535499)
            ·
              refine ⟨77689140023803570803803249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51792760015869047202535499 77689140023803570803803249)
              ·
                refine ⟨58266855017852678102852437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77689140023803570803803249 58266855017852678102852437)
                ·
                  refine ⟨341407353620230535758901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 58266855017852678102852437 341407353620230535758901)
                  ·
                    rfl

theorem cell23_5983996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 9].length) (baseStart_5983996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5983996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5983996 prefixEnd_5983996 := by exact prefixLift 5983996
  have htrace : WordTrace (prefixWord ++ tailWord_5983996) baseStart_5983996 baseEnd_5983996 := by
    simpa [prefixWord, tailWord_5983996, baseEnd_5983996] using wordTrace_append hprefix tailTrace_5983996
  have hstable : (prefixWord ++ tailWord_5983996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5983996).length < 2 ^ (prefixWord ++ tailWord_5983996).sum := by decide
  have hdescent : baseEnd_5983996 < baseStart_5983996 := by decide
  rcases family_descends (prefixWord ++ tailWord_5983996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5984133 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 5, 5]
def baseStart_5984133 : Nat := 118140960795 + 5984133 * 2 ^ 59
def prefixEnd_5984133 : Nat := 4983230072969 + 3 ^ 40 * 5984133 * 2
def baseEnd_5984133 : Nat := 1024245509810580261938993

theorem tailTrace_5984133 : CollatzResearch.WordTrace tailWord_5984133 prefixEnd_5984133 1024245509810580261938993 := by
  unfold tailWord_5984133
  simp only [CollatzResearch.WordTrace]
  refine ⟨218259261229515624395253053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145506174153010416263502035 218259261229515624395253053)
  ·
    refine ⟨81847222961068359148219895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218259261229515624395253053 81847222961068359148219895)
    ·
      refine ⟨122770834441602538722329843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81847222961068359148219895 122770834441602538722329843)
      ·
        refine ⟨184156251662403808083494765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122770834441602538722329843 184156251662403808083494765)
        ·
          refine ⟨69058594373401428031310537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184156251662403808083494765 69058594373401428031310537)
          ·
            refine ⟨51793945780051071023482903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69058594373401428031310537 51793945780051071023482903)
            ·
              refine ⟨77690918670076606535224355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51793945780051071023482903 77690918670076606535224355)
              ·
                refine ⟨116536378005114909802836533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77690918670076606535224355 116536378005114909802836533)
                ·
                  refine ⟨10925285437979522794015925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 116536378005114909802836533 10925285437979522794015925)
                  ·
                    refine ⟨1024245509810580261938993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10925285437979522794015925 1024245509810580261938993)
                    ·
                      rfl

theorem cell23_5984133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5, 5].length) (baseStart_5984133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5984133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5984133 prefixEnd_5984133 := by exact prefixLift 5984133
  have htrace : WordTrace (prefixWord ++ tailWord_5984133) baseStart_5984133 baseEnd_5984133 := by
    simpa [prefixWord, tailWord_5984133, baseEnd_5984133] using wordTrace_append hprefix tailTrace_5984133
  have hstable : (prefixWord ++ tailWord_5984133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5984133).length < 2 ^ (prefixWord ++ tailWord_5984133).sum := by decide
  have hdescent : baseEnd_5984133 < baseStart_5984133 := by decide
  rcases family_descends (prefixWord ++ tailWord_5984133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5984140 : List Nat := [2, 2, 1, 2, 1, 2, 1, 4, 1, 5, 2]
def baseStart_5984140 : Nat := 118140960795 + 5984140 * 2 ^ 59
def prefixEnd_5984140 : Nat := 4983230072969 + 3 ^ 40 * 5984140 * 2
def baseEnd_5984140 : Nat := 3072740123796322258429447

theorem tailTrace_5984140 : CollatzResearch.WordTrace tailWord_5984140 prefixEnd_5984140 3072740123796322258429447 := by
  unfold tailWord_5984140
  simp only [CollatzResearch.WordTrace]
  refine ⟨109129758270245132295378937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145506344360326843060505249 109129758270245132295378937)
  ·
    refine ⟨81847318702683849221534203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109129758270245132295378937 81847318702683849221534203)
    ·
      refine ⟨122770978054025773832301305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81847318702683849221534203 122770978054025773832301305)
      ·
        refine ⟨92078233540519330374225979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122770978054025773832301305 92078233540519330374225979)
        ·
          refine ⟨138117350310778995561338969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92078233540519330374225979 138117350310778995561338969)
          ·
            refine ⟨103588012733084246671004227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138117350310778995561338969 103588012733084246671004227)
            ·
              refine ⟨155382019099626370006506341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103588012733084246671004227 155382019099626370006506341)
              ·
                refine ⟨29134128581179944376219939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 155382019099626370006506341 29134128581179944376219939)
                ·
                  refine ⟨43701192871769916564329909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29134128581179944376219939 43701192871769916564329909)
                  ·
                    refine ⟨4096986831728429677905929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43701192871769916564329909 4096986831728429677905929)
                    ·
                      refine ⟨3072740123796322258429447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4096986831728429677905929 3072740123796322258429447)
                      ·
                        rfl

theorem cell23_5984140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 1, 5, 2].length) (baseStart_5984140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5984140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5984140 prefixEnd_5984140 := by exact prefixLift 5984140
  have htrace : WordTrace (prefixWord ++ tailWord_5984140) baseStart_5984140 baseEnd_5984140 := by
    simpa [prefixWord, tailWord_5984140, baseEnd_5984140] using wordTrace_append hprefix tailTrace_5984140
  have hstable : (prefixWord ++ tailWord_5984140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5984140).length < 2 ^ (prefixWord ++ tailWord_5984140).sum := by decide
  have hdescent : baseEnd_5984140 < baseStart_5984140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5984140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5984157 : List Nat := [1, 4, 2, 1, 2, 3, 1, 1, 1, 5, 2]
def baseStart_5984157 : Nat := 118140960795 + 5984157 * 2 ^ 59
def prefixEnd_5984157 : Nat := 4983230072969 + 3 ^ 40 * 5984157 * 2
def baseEnd_5984157 : Nat := 3072748852967448691916869

theorem tailTrace_5984157 : CollatzResearch.WordTrace tailWord_5984157 prefixEnd_5984157 3072748852967448691916869 := by
  unfold tailWord_5984157
  simp only [CollatzResearch.WordTrace]
  refine ⟨218260136581428676494126725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145506757720952450996084483 218260136581428676494126725)
  ·
    refine ⟨40923775609017876842648761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 218260136581428676494126725 40923775609017876842648761)
    ·
      refine ⟨30692831706763407631986571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40923775609017876842648761 30692831706763407631986571)
      ·
        refine ⟨46039247560145111447979857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30692831706763407631986571 46039247560145111447979857)
        ·
          refine ⟨34529435670108833585984893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46039247560145111447979857 34529435670108833585984893)
          ·
            refine ⟨12948538376290812594744335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34529435670108833585984893 12948538376290812594744335)
            ·
              refine ⟨19422807564436218892116503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12948538376290812594744335 19422807564436218892116503)
              ·
                refine ⟨29134211346654328338174755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19422807564436218892116503 29134211346654328338174755)
                ·
                  refine ⟨43701317019981492507262133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29134211346654328338174755 43701317019981492507262133)
                  ·
                    refine ⟨4096998470623264922555825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43701317019981492507262133 4096998470623264922555825)
                    ·
                      refine ⟨3072748852967448691916869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4096998470623264922555825 3072748852967448691916869)
                      ·
                        rfl

theorem cell23_5984157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 5, 2].length) (baseStart_5984157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5984157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5984157 prefixEnd_5984157 := by exact prefixLift 5984157
  have htrace : WordTrace (prefixWord ++ tailWord_5984157) baseStart_5984157 baseEnd_5984157 := by
    simpa [prefixWord, tailWord_5984157, baseEnd_5984157] using wordTrace_append hprefix tailTrace_5984157
  have hstable : (prefixWord ++ tailWord_5984157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5984157).length < 2 ^ (prefixWord ++ tailWord_5984157).sum := by decide
  have hdescent : baseEnd_5984157 < baseStart_5984157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5984157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5984158 : List Nat := [4, 3, 1, 3, 1, 1, 2, 3, 1, 4]
def baseStart_5984158 : Nat := 118140960795 + 5984158 * 2 ^ 59
def prefixEnd_5984158 : Nat := 4983230072969 + 3 ^ 40 * 5984158 * 2
def baseEnd_5984158 : Nat := 1024249788816034396001455

theorem tailTrace_5984158 : CollatzResearch.WordTrace tailWord_5984158 prefixEnd_5984158 1024249788816034396001455 := by
  unfold tailWord_5984158
  simp only [CollatzResearch.WordTrace]
  refine ⟨27282521631803131708114141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145506782036283369109942085 27282521631803131708114141)
  ·
    refine ⟨10230945611926174390542803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27282521631803131708114141 10230945611926174390542803)
    ·
      refine ⟨15346418417889261585814205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10230945611926174390542803 15346418417889261585814205)
      ·
        refine ⟨5754906906708473094680327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15346418417889261585814205 5754906906708473094680327)
        ·
          refine ⟨8632360360062709642020491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5754906906708473094680327 8632360360062709642020491)
          ·
            refine ⟨12948540540094064463030737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8632360360062709642020491 12948540540094064463030737)
            ·
              refine ⟨9711405405070548347273053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12948540540094064463030737 9711405405070548347273053)
              ·
                refine ⟨3641777026901455630227395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9711405405070548347273053 3641777026901455630227395)
                ·
                  refine ⟨5462665540352183445341093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3641777026901455630227395 5462665540352183445341093)
                  ·
                    refine ⟨1024249788816034396001455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5462665540352183445341093 1024249788816034396001455)
                    ·
                      rfl

theorem cell23_5984158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_5984158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5984158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5984158 prefixEnd_5984158 := by exact prefixLift 5984158
  have htrace : WordTrace (prefixWord ++ tailWord_5984158) baseStart_5984158 baseEnd_5984158 := by
    simpa [prefixWord, tailWord_5984158, baseEnd_5984158] using wordTrace_append hprefix tailTrace_5984158
  have hstable : (prefixWord ++ tailWord_5984158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5984158).length < 2 ^ (prefixWord ++ tailWord_5984158).sum := by decide
  have hdescent : baseEnd_5984158 < baseStart_5984158 := by decide
  rcases family_descends (prefixWord ++ tailWord_5984158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5984164 : List Nat := [2, 3, 1, 2, 1, 3, 1, 5, 1, 1, 3]
def baseStart_5984164 : Nat := 118140960795 + 5984164 * 2 ^ 59
def prefixEnd_5984164 : Nat := 4983230072969 + 3 ^ 40 * 5984164 * 2
def baseEnd_5984164 : Nat := 3072752447332030164529337

theorem tailTrace_5984164 : CollatzResearch.WordTrace tailWord_5984164 prefixEnd_5984164 3072752447332030164529337 := by
  unfold tailWord_5984164
  simp only [CollatzResearch.WordTrace]
  refine ⟨109130195946201658344815773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145506927928268877793087697 109130195946201658344815773)
  ·
    refine ⟨40923823479825621879305915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109130195946201658344815773 40923823479825621879305915)
    ·
      refine ⟨61385735219738432818958873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40923823479825621879305915 61385735219738432818958873)
      ·
        refine ⟨46039301414803824614219155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61385735219738432818958873 46039301414803824614219155)
        ·
          refine ⟨69058952122205736921328733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46039301414803824614219155 69058952122205736921328733)
          ·
            refine ⟨25897107045827151345498275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69058952122205736921328733 25897107045827151345498275)
            ·
              refine ⟨38845660568740727018247413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25897107045827151345498275 38845660568740727018247413)
              ·
                refine ⟨3641780678319443157960695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38845660568740727018247413 3641780678319443157960695)
                ·
                  refine ⟨5462671017479164736941043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3641780678319443157960695 5462671017479164736941043)
                  ·
                    refine ⟨8194006526218747105411565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5462671017479164736941043 8194006526218747105411565)
                    ·
                      refine ⟨3072752447332030164529337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8194006526218747105411565 3072752447332030164529337)
                      ·
                        rfl

theorem cell23_5984164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 5, 1, 1, 3].length) (baseStart_5984164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5984164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5984164 prefixEnd_5984164 := by exact prefixLift 5984164
  have htrace : WordTrace (prefixWord ++ tailWord_5984164) baseStart_5984164 baseEnd_5984164 := by
    simpa [prefixWord, tailWord_5984164, baseEnd_5984164] using wordTrace_append hprefix tailTrace_5984164
  have hstable : (prefixWord ++ tailWord_5984164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5984164).length < 2 ^ (prefixWord ++ tailWord_5984164).sum := by decide
  have hdescent : baseEnd_5984164 < baseStart_5984164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5984164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5984167 : List Nat := [1, 1, 6, 1, 2, 2, 1, 3, 1, 5]
def baseStart_5984167 : Nat := 118140960795 + 5984167 * 2 ^ 59
def prefixEnd_5984167 : Nat := 4983230072969 + 3 ^ 40 * 5984167 * 2
def baseEnd_5984167 : Nat := 1024251329257997884263941

theorem tailTrace_5984167 : CollatzResearch.WordTrace tailWord_5984167 prefixEnd_5984167 1024251329257997884263941 := by
  unfold tailWord_5984167
  simp only [CollatzResearch.WordTrace]
  refine ⟨218260501311392448201990755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145507000874261632134660503 218260501311392448201990755)
  ·
    refine ⟨327390751967088672302986133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218260501311392448201990755 327390751967088672302986133)
    ·
      refine ⟨15346441498457281514202475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 327390751967088672302986133 15346441498457281514202475)
      ·
        refine ⟨23019662247685922271303713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15346441498457281514202475 23019662247685922271303713)
        ·
          refine ⟨17264746685764441703477785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23019662247685922271303713 17264746685764441703477785)
          ·
            refine ⟨12948560014323331277608339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17264746685764441703477785 12948560014323331277608339)
            ·
              refine ⟨19422840021484996916412509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12948560014323331277608339 19422840021484996916412509)
              ·
                refine ⟨7283565008056873843654691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19422840021484996916412509 7283565008056873843654691)
                ·
                  refine ⟨10925347512085310765482037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7283565008056873843654691 10925347512085310765482037)
                  ·
                    refine ⟨1024251329257997884263941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10925347512085310765482037 1024251329257997884263941)
                    ·
                      rfl

theorem cell23_5984167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_5984167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5984167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5984167 prefixEnd_5984167 := by exact prefixLift 5984167
  have htrace : WordTrace (prefixWord ++ tailWord_5984167) baseStart_5984167 baseEnd_5984167 := by
    simpa [prefixWord, tailWord_5984167, baseEnd_5984167] using wordTrace_append hprefix tailTrace_5984167
  have hstable : (prefixWord ++ tailWord_5984167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5984167).length < 2 ^ (prefixWord ++ tailWord_5984167).sum := by decide
  have hdescent : baseEnd_5984167 < baseStart_5984167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5984167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5984183 : List Nat := [1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 6]
def baseStart_5984183 : Nat := 118140960795 + 5984183 * 2 ^ 59
def prefixEnd_5984183 : Nat := 4983230072969 + 3 ^ 40 * 5984183 * 2
def baseEnd_5984183 : Nat := 3072762203464465590191749

theorem tailTrace_5984183 : CollatzResearch.WordTrace tailWord_5984183 prefixEnd_5984183 3072762203464465590191749 := by
  unfold tailWord_5984183
  simp only [CollatzResearch.WordTrace]
  refine ⟨218261084879334482934573203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145507389919556321956382135 218261084879334482934573203)
  ·
    refine ⟨327391627319001724401859805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218261084879334482934573203 327391627319001724401859805)
    ·
      refine ⟨122771860244625646650697427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 327391627319001724401859805 122771860244625646650697427)
      ·
        refine ⟨184157790366938469976046141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122771860244625646650697427 184157790366938469976046141)
        ·
          refine ⟨69059171387601926241017303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184157790366938469976046141 69059171387601926241017303)
          ·
            refine ⟨103588757081402889361525955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69059171387601926241017303 103588757081402889361525955)
            ·
              refine ⟨155383135622104334042288933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103588757081402889361525955 155383135622104334042288933)
              ·
                refine ⟨29134337929144562632929175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 155383135622104334042288933 29134337929144562632929175)
                ·
                  refine ⟨43701506893716843949393763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29134337929144562632929175 43701506893716843949393763)
                  ·
                    refine ⟨65552260340575265924090645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43701506893716843949393763 65552260340575265924090645)
                    ·
                      refine ⟨3072762203464465590191749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65552260340575265924090645 3072762203464465590191749)
                      ·
                        rfl

theorem cell23_5984183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 6].length) (baseStart_5984183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5984183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5984183 prefixEnd_5984183 := by exact prefixLift 5984183
  have htrace : WordTrace (prefixWord ++ tailWord_5984183) baseStart_5984183 baseEnd_5984183 := by
    simpa [prefixWord, tailWord_5984183, baseEnd_5984183] using wordTrace_append hprefix tailTrace_5984183
  have hstable : (prefixWord ++ tailWord_5984183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5984183).length < 2 ^ (prefixWord ++ tailWord_5984183).sum := by decide
  have hdescent : baseEnd_5984183 < baseStart_5984183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5984183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5984187 : List Nat := [1, 1, 1, 1, 1, 2, 2, 7, 3, 2, 2]
def baseStart_5984187 : Nat := 118140960795 + 5984187 * 2 ^ 59
def prefixEnd_5984187 : Nat := 4983230072969 + 3 ^ 40 * 5984187 * 2
def baseEnd_5984187 : Nat := 3072764257387083574541731

theorem tailTrace_5984187 : CollatzResearch.WordTrace tailWord_5984187 prefixEnd_5984187 3072764257387083574541731 := by
  unfold tailWord_5984187
  simp only [CollatzResearch.WordTrace]
  refine ⟨218261230771319991617718815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145507487180879994411812543 218261230771319991617718815)
  ·
    refine ⟨327391846156979987426578223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218261230771319991617718815 327391846156979987426578223)
    ·
      refine ⟨491087769235469981139867335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327391846156979987426578223 491087769235469981139867335)
      ·
        refine ⟨736631653853204971709801003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491087769235469981139867335 736631653853204971709801003)
        ·
          refine ⟨1104947480779807457564701505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 736631653853204971709801003 1104947480779807457564701505)
          ·
            refine ⟨828710610584855593173526129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1104947480779807457564701505 828710610584855593173526129)
            ·
              refine ⟨621532957938641694880144597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 828710610584855593173526129 621532957938641694880144597)
              ·
                refine ⟨14567178701686914723753389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 621532957938641694880144597 14567178701686914723753389)
                ·
                  refine ⟨5462692013132593021407521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14567178701686914723753389 5462692013132593021407521)
                  ·
                    refine ⟨4097019009849444766055641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5462692013132593021407521 4097019009849444766055641)
                    ·
                      refine ⟨3072764257387083574541731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4097019009849444766055641 3072764257387083574541731)
                      ·
                        rfl

theorem cell23_5984187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 3, 2, 2].length) (baseStart_5984187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5984187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5984187 prefixEnd_5984187 := by exact prefixLift 5984187
  have htrace : WordTrace (prefixWord ++ tailWord_5984187) baseStart_5984187 baseEnd_5984187 := by
    simpa [prefixWord, tailWord_5984187, baseEnd_5984187] using wordTrace_append hprefix tailTrace_5984187
  have hstable : (prefixWord ++ tailWord_5984187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5984187).length < 2 ^ (prefixWord ++ tailWord_5984187).sum := by decide
  have hdescent : baseEnd_5984187 < baseStart_5984187 := by decide
  rcases family_descends (prefixWord ++ tailWord_5984187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5984190 : List Nat := [4, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5]
def baseStart_5984190 : Nat := 118140960795 + 5984190 * 2 ^ 59
def prefixEnd_5984190 : Nat := 4983230072969 + 3 ^ 40 * 5984190 * 2
def baseEnd_5984190 : Nat := 3072765797829047062804217

theorem tailTrace_5984190 : CollatzResearch.WordTrace tailWord_5984190 prefixEnd_5984190 3072765797829047062804217 := by
  unfold tailWord_5984190
  simp only [CollatzResearch.WordTrace]
  refine ⟨27282667523788640391259753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145507560126872748753385349 27282667523788640391259753)
  ·
    refine ⟨20462000642841480293444815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27282667523788640391259753 20462000642841480293444815)
    ·
      refine ⟨30693000964262220440167223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20462000642841480293444815 30693000964262220440167223)
      ·
        refine ⟨46039501446393330660250835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30693000964262220440167223 46039501446393330660250835)
        ·
          refine ⟨69059252169589995990376253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46039501446393330660250835 69059252169589995990376253)
          ·
            refine ⟨25897219563596248496391095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69059252169589995990376253 25897219563596248496391095)
            ·
              refine ⟨38845829345394372744586643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25897219563596248496391095 38845829345394372744586643)
              ·
                refine ⟨58268744018091559116879965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38845829345394372744586643 58268744018091559116879965)
                ·
                  refine ⟨21850779006784334668829987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58268744018091559116879965 21850779006784334668829987)
                  ·
                    refine ⟨32776168510176502003244981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21850779006784334668829987 32776168510176502003244981)
                    ·
                      refine ⟨3072765797829047062804217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32776168510176502003244981 3072765797829047062804217)
                      ·
                        rfl

theorem cell23_5984190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_5984190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5984190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5984190 prefixEnd_5984190 := by exact prefixLift 5984190
  have htrace : WordTrace (prefixWord ++ tailWord_5984190) baseStart_5984190 baseEnd_5984190 := by
    simpa [prefixWord, tailWord_5984190, baseEnd_5984190] using wordTrace_append hprefix tailTrace_5984190
  have hstable : (prefixWord ++ tailWord_5984190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5984190).length < 2 ^ (prefixWord ++ tailWord_5984190).sum := by decide
  have hdescent : baseEnd_5984190 < baseStart_5984190 := by decide
  rcases family_descends (prefixWord ++ tailWord_5984190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5984200 : List Nat := [2, 1, 3, 1, 4, 2, 1, 1, 1, 1, 6]
def baseStart_5984200 : Nat := 118140960795 + 5984200 * 2 ^ 59
def prefixEnd_5984200 : Nat := 4983230072969 + 3 ^ 40 * 5984200 * 2
def baseEnd_5984200 : Nat := 3072770932635592023679171

theorem tailTrace_5984200 : CollatzResearch.WordTrace tailWord_5984200 prefixEnd_5984200 3072770932635592023679171 := by
  unfold tailWord_5984200
  simp only [CollatzResearch.WordTrace]
  refine ⟨109130852460136447418971027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145507803280181929891961369 109130852460136447418971027)
  ·
    refine ⟨163696278690204671128456541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109130852460136447418971027 163696278690204671128456541)
    ·
      refine ⟨61386104508826751673171203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163696278690204671128456541 61386104508826751673171203)
      ·
        refine ⟨92079156763240127509756805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61386104508826751673171203 92079156763240127509756805)
        ·
          refine ⟨17264841893107523908079401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92079156763240127509756805 17264841893107523908079401)
          ·
            refine ⟨12948631419830642931059551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17264841893107523908079401 12948631419830642931059551)
            ·
              refine ⟨19422947129745964396589327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12948631419830642931059551 19422947129745964396589327)
              ·
                refine ⟨29134420694618946594883991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19422947129745964396589327 29134420694618946594883991)
                ·
                  refine ⟨43701631041928419892325987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29134420694618946594883991 43701631041928419892325987)
                  ·
                    refine ⟨65552446562892629838488981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43701631041928419892325987 65552446562892629838488981)
                    ·
                      refine ⟨3072770932635592023679171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65552446562892629838488981 3072770932635592023679171)
                      ·
                        rfl

theorem cell23_5984200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_5984200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5984200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5984200 prefixEnd_5984200 := by exact prefixLift 5984200
  have htrace : WordTrace (prefixWord ++ tailWord_5984200) baseStart_5984200 baseEnd_5984200 := by
    simpa [prefixWord, tailWord_5984200, baseEnd_5984200] using wordTrace_append hprefix tailTrace_5984200
  have hstable : (prefixWord ++ tailWord_5984200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5984200).length < 2 ^ (prefixWord ++ tailWord_5984200).sum := by decide
  have hdescent : baseEnd_5984200 < baseStart_5984200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5984200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5984204 : List Nat := [2, 2, 1, 4, 1, 2, 2, 2, 3, 2, 2]
def baseStart_5984204 : Nat := 118140960795 + 5984204 * 2 ^ 59
def prefixEnd_5984204 : Nat := 4983230072969 + 3 ^ 40 * 5984204 * 2
def baseEnd_5984204 : Nat := 3072772986558210008029153

theorem tailTrace_5984204 : CollatzResearch.WordTrace tailWord_5984204 prefixEnd_5984204 3072772986558210008029153 := by
  unfold tailWord_5984204
  simp only [CollatzResearch.WordTrace]
  refine ⟨109130925406129201760543833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145507900541505602347391777 109130925406129201760543833)
  ·
    refine ⟨81848194054596901320407875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109130925406129201760543833 81848194054596901320407875)
    ·
      refine ⟨122772291081895351980611813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81848194054596901320407875 122772291081895351980611813)
      ·
        refine ⟨23019804577855378496364715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122772291081895351980611813 23019804577855378496364715)
        ·
          refine ⟨34529706866783067744547073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23019804577855378496364715 34529706866783067744547073)
          ·
            refine ⟨25897280150087300808410305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34529706866783067744547073 25897280150087300808410305)
            ·
              refine ⟨19422960112565475606307729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25897280150087300808410305 19422960112565475606307729)
              ·
                refine ⟨14567220084424106704730797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19422960112565475606307729 14567220084424106704730797)
                ·
                  refine ⟨5462707531659040014274049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14567220084424106704730797 5462707531659040014274049)
                  ·
                    refine ⟨4097030648744280010705537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5462707531659040014274049 4097030648744280010705537)
                    ·
                      refine ⟨3072772986558210008029153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4097030648744280010705537 3072772986558210008029153)
                      ·
                        rfl

theorem cell23_5984204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_5984204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5984204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5984204 prefixEnd_5984204 := by exact prefixLift 5984204
  have htrace : WordTrace (prefixWord ++ tailWord_5984204) baseStart_5984204 baseEnd_5984204 := by
    simpa [prefixWord, tailWord_5984204, baseEnd_5984204] using wordTrace_append hprefix tailTrace_5984204
  have hstable : (prefixWord ++ tailWord_5984204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5984204).length < 2 ^ (prefixWord ++ tailWord_5984204).sum := by decide
  have hdescent : baseEnd_5984204 < baseStart_5984204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5984204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5984207 : List Nat := [1, 1, 2, 1, 1, 5, 4, 2, 1, 2, 3]
def baseStart_5984207 : Nat := 118140960795 + 5984207 * 2 ^ 59
def prefixEnd_5984207 : Nat := 4983230072969 + 3 ^ 40 * 5984207 * 2
def baseEnd_5984207 : Nat := 3072774527000173496291639

theorem tailTrace_5984207 : CollatzResearch.WordTrace tailWord_5984207 prefixEnd_5984207 3072774527000173496291639 := by
  unfold tailWord_5984207
  simp only [CollatzResearch.WordTrace]
  refine ⟨218261960231247535033446875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145507973487498356688964583 218261960231247535033446875)
  ·
    refine ⟨327392940346871302550170313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218261960231247535033446875 327392940346871302550170313)
    ·
      refine ⟨245544705260153476912627735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327392940346871302550170313 245544705260153476912627735)
      ·
        refine ⟨368317057890230215368941603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245544705260153476912627735 368317057890230215368941603)
        ·
          refine ⟨552475586835345323053412405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368317057890230215368941603 552475586835345323053412405)
          ·
            refine ⟨51794586265813624036257413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 552475586835345323053412405 51794586265813624036257413)
            ·
              refine ⟨9711484924840054506798265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51794586265813624036257413 9711484924840054506798265)
              ·
                refine ⟨7283613693630040880098699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9711484924840054506798265 7283613693630040880098699)
                ·
                  refine ⟨10925420540445061320148049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7283613693630040880098699 10925420540445061320148049)
                  ·
                    refine ⟨8194065405333795990111037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10925420540445061320148049 8194065405333795990111037)
                    ·
                      refine ⟨3072774527000173496291639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8194065405333795990111037 3072774527000173496291639)
                      ·
                        rfl

theorem cell23_5984207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2, 1, 2, 3].length) (baseStart_5984207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5984207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5984207 prefixEnd_5984207 := by exact prefixLift 5984207
  have htrace : WordTrace (prefixWord ++ tailWord_5984207) baseStart_5984207 baseEnd_5984207 := by
    simpa [prefixWord, tailWord_5984207, baseEnd_5984207] using wordTrace_append hprefix tailTrace_5984207
  have hstable : (prefixWord ++ tailWord_5984207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5984207).length < 2 ^ (prefixWord ++ tailWord_5984207).sum := by decide
  have hdescent : baseEnd_5984207 < baseStart_5984207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5984207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5984280 : List Nat := [2, 1, 2, 3, 2, 1, 1, 3, 2, 1, 5]
def baseStart_5984280 : Nat := 118140960795 + 5984280 * 2 ^ 59
def prefixEnd_5984280 : Nat := 4983230072969 + 3 ^ 40 * 5984280 * 2
def baseEnd_5984280 : Nat := 3072812011087951710678803

theorem tailTrace_5984280 : CollatzResearch.WordTrace tailWord_5984280 prefixEnd_5984280 3072812011087951710678803 := by
  unfold tailWord_5984280
  simp only [CollatzResearch.WordTrace]
  refine ⟨109132311379991534250427147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145509748506655379000569529 109132311379991534250427147)
  ·
    refine ⟨163698467069987301375640721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109132311379991534250427147 163698467069987301375640721)
    ·
      refine ⟨122773850302490476031730541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163698467069987301375640721 122773850302490476031730541)
      ·
        refine ⟨46040193863433928511898953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122773850302490476031730541 46040193863433928511898953)
        ·
          refine ⟨34530145397575446383924215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46040193863433928511898953 34530145397575446383924215)
          ·
            refine ⟨51795218096363169575886323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34530145397575446383924215 51795218096363169575886323)
            ·
              refine ⟨77692827144544754363829485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51795218096363169575886323 77692827144544754363829485)
              ·
                refine ⟨29134810179204282886436057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77692827144544754363829485 29134810179204282886436057)
                ·
                  refine ⟨21851107634403212164827043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29134810179204282886436057 21851107634403212164827043)
                  ·
                    refine ⟨32776661451604818247240565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21851107634403212164827043 32776661451604818247240565)
                    ·
                      refine ⟨3072812011087951710678803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32776661451604818247240565 3072812011087951710678803)
                      ·
                        rfl

theorem cell23_5984280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_5984280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5984280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5984280 prefixEnd_5984280 := by exact prefixLift 5984280
  have htrace : WordTrace (prefixWord ++ tailWord_5984280) baseStart_5984280 baseEnd_5984280 := by
    simpa [prefixWord, tailWord_5984280, baseEnd_5984280] using wordTrace_append hprefix tailTrace_5984280
  have hstable : (prefixWord ++ tailWord_5984280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5984280).length < 2 ^ (prefixWord ++ tailWord_5984280).sum := by decide
  have hdescent : baseEnd_5984280 < baseStart_5984280 := by decide
  rcases family_descends (prefixWord ++ tailWord_5984280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5984283 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 11]
def baseStart_5984283 : Nat := 118140960795 + 5984283 * 2 ^ 59
def prefixEnd_5984283 : Nat := 4983230072969 + 3 ^ 40 * 5984283 * 2
def baseEnd_5984283 : Nat := 341423727947768355437921

theorem tailTrace_5984283 : CollatzResearch.WordTrace tailWord_5984283 prefixEnd_5984283 341423727947768355437921 := by
  unfold tailWord_5984283
  simp only [CollatzResearch.WordTrace]
  refine ⟨218264732178972200013213503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145509821452648133342142335 218264732178972200013213503)
  ·
    refine ⟨327397098268458300019820255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218264732178972200013213503 327397098268458300019820255)
    ·
      refine ⟨491095647402687450029730383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327397098268458300019820255 491095647402687450029730383)
      ·
        refine ⟨736643471104031175044595575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491095647402687450029730383 736643471104031175044595575)
        ·
          refine ⟨1104965206656046762566893363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 736643471104031175044595575 1104965206656046762566893363)
          ·
            refine ⟨1657447809984070143850340045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1104965206656046762566893363 1657447809984070143850340045)
            ·
              refine ⟨621542928744026303943877517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1657447809984070143850340045 621542928744026303943877517)
              ·
                refine ⟨233078598279009863978954069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 621542928744026303943877517 233078598279009863978954069)
                ·
                  refine ⟨341423727947768355437921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 233078598279009863978954069 341423727947768355437921)
                  ·
                    rfl

theorem cell23_5984283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 11].length) (baseStart_5984283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5984283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5984283 prefixEnd_5984283 := by exact prefixLift 5984283
  have htrace : WordTrace (prefixWord ++ tailWord_5984283) baseStart_5984283 baseEnd_5984283 := by
    simpa [prefixWord, tailWord_5984283, baseEnd_5984283] using wordTrace_append hprefix tailTrace_5984283
  have hstable : (prefixWord ++ tailWord_5984283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5984283).length < 2 ^ (prefixWord ++ tailWord_5984283).sum := by decide
  have hdescent : baseEnd_5984283 < baseStart_5984283 := by decide
  rcases family_descends (prefixWord ++ tailWord_5984283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5984334 : List Nat := [4, 1, 1, 1, 1, 5, 2, 3, 5]
def baseStart_5984334 : Nat := 118140960795 + 5984334 * 2 ^ 59
def prefixEnd_5984334 : Nat := 4983230072969 + 3 ^ 40 * 5984334 * 2
def baseEnd_5984334 : Nat := 341426637671477166600395

theorem tailTrace_5984334 : CollatzResearch.WordTrace tailWord_5984334 prefixEnd_5984334 341426637671477166600395 := by
  unfold tailWord_5984334
  simp only [CollatzResearch.WordTrace]
  refine ⟨27283324037723429465415007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145511061534524957148880037 27283324037723429465415007)
  ·
    refine ⟨40924986056585144198122511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27283324037723429465415007 40924986056585144198122511)
    ·
      refine ⟨61387479084877716297183767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40924986056585144198122511 61387479084877716297183767)
      ·
        refine ⟨92081218627316574445775651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61387479084877716297183767 92081218627316574445775651)
        ·
          refine ⟨138121827940974861668663477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92081218627316574445775651 138121827940974861668663477)
          ·
            refine ⟨12948921369466393281437201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 138121827940974861668663477 12948921369466393281437201)
            ·
              refine ⟨9711691027099794961077901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12948921369466393281437201 9711691027099794961077901)
              ·
                refine ⟨3641884135162423110404213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9711691027099794961077901 3641884135162423110404213)
                ·
                  refine ⟨341426637671477166600395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3641884135162423110404213 341426637671477166600395)
                  ·
                    rfl

theorem cell23_5984334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 3, 5].length) (baseStart_5984334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5984334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5984334 prefixEnd_5984334 := by exact prefixLift 5984334
  have htrace : WordTrace (prefixWord ++ tailWord_5984334) baseStart_5984334 baseEnd_5984334 := by
    simpa [prefixWord, tailWord_5984334, baseEnd_5984334] using wordTrace_append hprefix tailTrace_5984334
  have hstable : (prefixWord ++ tailWord_5984334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5984334).length < 2 ^ (prefixWord ++ tailWord_5984334).sum := by decide
  have hdescent : baseEnd_5984334 < baseStart_5984334 := by decide
  rcases family_descends (prefixWord ++ tailWord_5984334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5984387 : List Nat := [1, 1, 1, 3, 3, 3, 2, 1, 1, 4, 3]
def baseStart_5984387 : Nat := 118140960795 + 5984387 * 2 ^ 59
def prefixEnd_5984387 : Nat := 4983230072969 + 3 ^ 40 * 5984387 * 2
def baseEnd_5984387 : Nat := 3072866953517982792040811

theorem tailTrace_5984387 : CollatzResearch.WordTrace tailWord_5984387 prefixEnd_5984387 3072866953517982792040811 := by
  unfold tailWord_5984387
  simp only [CollatzResearch.WordTrace]
  refine ⟨218268525370595425774999415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145512350247063617183332943 218268525370595425774999415)
  ·
    refine ⟨327402788055893138662499123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218268525370595425774999415 327402788055893138662499123)
    ·
      refine ⟨491104182083839707993748685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327402788055893138662499123 491104182083839707993748685)
      ·
        refine ⟨184164068281439890497655757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 491104182083839707993748685 184164068281439890497655757)
        ·
          refine ⟨69061525605539958936620909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184164068281439890497655757 69061525605539958936620909)
          ·
            refine ⟨25898072102077484601232841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69061525605539958936620909 25898072102077484601232841)
            ·
              refine ⟨19423554076558113450924631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25898072102077484601232841 19423554076558113450924631)
              ·
                refine ⟨29135331114837170176386947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19423554076558113450924631 29135331114837170176386947)
                ·
                  refine ⟨43702996672255755264580421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29135331114837170176386947 43702996672255755264580421)
                  ·
                    refine ⟨8194311876047954112108829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43702996672255755264580421 8194311876047954112108829)
                    ·
                      refine ⟨3072866953517982792040811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8194311876047954112108829 3072866953517982792040811)
                      ·
                        rfl

theorem cell23_5984387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 4, 3].length) (baseStart_5984387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5984387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5984387 prefixEnd_5984387 := by exact prefixLift 5984387
  have htrace : WordTrace (prefixWord ++ tailWord_5984387) baseStart_5984387 baseEnd_5984387 := by
    simpa [prefixWord, tailWord_5984387, baseEnd_5984387] using wordTrace_append hprefix tailTrace_5984387
  have hstable : (prefixWord ++ tailWord_5984387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5984387).length < 2 ^ (prefixWord ++ tailWord_5984387).sum := by decide
  have hdescent : baseEnd_5984387 < baseStart_5984387 := by decide
  rcases family_descends (prefixWord ++ tailWord_5984387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5984434 : List Nat := [3, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3]
def baseStart_5984434 : Nat := 118140960795 + 5984434 * 2 ^ 59
def prefixEnd_5984434 : Nat := 4983230072969 + 3 ^ 40 * 5984434 * 2
def baseEnd_5984434 : Nat := 3072891087108744108153095

theorem tailTrace_5984434 : CollatzResearch.WordTrace tailWord_5984434 prefixEnd_5984434 3072891087108744108153095 := by
  unfold tailWord_5984434
  simp only [CollatzResearch.WordTrace]
  refine ⟨54567559900356288200490089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145513493067616768534640237 54567559900356288200490089)
  ·
    refine ⟨40925669925267216150367567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54567559900356288200490089 40925669925267216150367567)
    ·
      refine ⟨61388504887900824225551351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40925669925267216150367567 61388504887900824225551351)
      ·
        refine ⟨92082757331851236338327027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61388504887900824225551351 92082757331851236338327027)
        ·
          refine ⟨138124135997776854507490541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92082757331851236338327027 138124135997776854507490541)
          ·
            refine ⟨51796550999166320440308953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138124135997776854507490541 51796550999166320440308953)
            ·
              refine ⟨38847413249374740330231715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51796550999166320440308953 38847413249374740330231715)
              ·
                refine ⟨58271119874062110495347573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38847413249374740330231715 58271119874062110495347573)
                ·
                  refine ⟨5462917488193322858938835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58271119874062110495347573 5462917488193322858938835)
                  ·
                    refine ⟨8194376232289984288408253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5462917488193322858938835 8194376232289984288408253)
                    ·
                      refine ⟨3072891087108744108153095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8194376232289984288408253 3072891087108744108153095)
                      ·
                        rfl

theorem cell23_5984434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3].length) (baseStart_5984434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5984434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5984434 prefixEnd_5984434 := by exact prefixLift 5984434
  have htrace : WordTrace (prefixWord ++ tailWord_5984434) baseStart_5984434 baseEnd_5984434 := by
    simpa [prefixWord, tailWord_5984434, baseEnd_5984434] using wordTrace_append hprefix tailTrace_5984434
  have hstable : (prefixWord ++ tailWord_5984434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5984434).length < 2 ^ (prefixWord ++ tailWord_5984434).sum := by decide
  have hdescent : baseEnd_5984434 < baseStart_5984434 := by decide
  rcases family_descends (prefixWord ++ tailWord_5984434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5984491 : List Nat := [1, 1, 1, 1, 2, 5, 3, 2, 3, 2, 2]
def baseStart_5984491 : Nat := 118140960795 + 5984491 * 2 ^ 59
def prefixEnd_5984491 : Nat := 4983230072969 + 3 ^ 40 * 5984491 * 2
def baseEnd_5984491 : Nat := 3072920355506050385140333

theorem tailTrace_5984491 : CollatzResearch.WordTrace tailWord_5984491 prefixEnd_5984491 3072920355506050385140333 := by
  unfold tailWord_5984491
  simp only [CollatzResearch.WordTrace]
  refine ⟨218272318562218651536785327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145514879041479101024523551 218272318562218651536785327)
  ·
    refine ⟨327408477843327977305177991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218272318562218651536785327 327408477843327977305177991)
    ·
      refine ⟨491112716764991965957766987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327408477843327977305177991 491112716764991965957766987)
      ·
        refine ⟨736669075147487948936650481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491112716764991965957766987 736669075147487948936650481)
        ·
          refine ⟨552501806360615961702487861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 736669075147487948936650481 552501806360615961702487861)
          ·
            refine ⟨51797044346307746409608237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 552501806360615961702487861 51797044346307746409608237)
            ·
              refine ⟨19423891629865404903603089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51797044346307746409608237 19423891629865404903603089)
              ·
                refine ⟨14567918722399053677702317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19423891629865404903603089 14567918722399053677702317)
                ·
                  refine ⟨5462969520899645129138369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14567918722399053677702317 5462969520899645129138369)
                  ·
                    refine ⟨4097227140674733846853777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5462969520899645129138369 4097227140674733846853777)
                    ·
                      refine ⟨3072920355506050385140333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4097227140674733846853777 3072920355506050385140333)
                      ·
                        rfl

theorem cell23_5984491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 3, 2, 2].length) (baseStart_5984491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5984491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5984491 prefixEnd_5984491 := by exact prefixLift 5984491
  have htrace : WordTrace (prefixWord ++ tailWord_5984491) baseStart_5984491 baseEnd_5984491 := by
    simpa [prefixWord, tailWord_5984491, baseEnd_5984491] using wordTrace_append hprefix tailTrace_5984491
  have hstable : (prefixWord ++ tailWord_5984491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5984491).length < 2 ^ (prefixWord ++ tailWord_5984491).sum := by decide
  have hdescent : baseEnd_5984491 < baseStart_5984491 := by decide
  rcases family_descends (prefixWord ++ tailWord_5984491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5984508 : List Nat := [2, 2, 2, 1, 4, 3, 2, 1, 1, 1, 4]
def baseStart_5984508 : Nat := 118140960795 + 5984508 * 2 ^ 59
def prefixEnd_5984508 : Nat := 4983230072969 + 3 ^ 40 * 5984508 * 2
def baseEnd_5984508 : Nat := 3072929084677176818627755

theorem tailTrace_5984508 : CollatzResearch.WordTrace tailWord_5984508 prefixEnd_5984508 3072929084677176818627755 := by
  unfold tailWord_5984508
  simp only [CollatzResearch.WordTrace]
  refine ⟨109136469301578531720077089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145515292402104708960102785 109136469301578531720077089)
  ·
    refine ⟨81852351976183898790057817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109136469301578531720077089 81852351976183898790057817)
    ·
      refine ⟨61389263982137924092543363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81852351976183898790057817 61389263982137924092543363)
      ·
        refine ⟨92083895973206886138815045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61389263982137924092543363 92083895973206886138815045)
        ·
          refine ⟨17265730494976291151027821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92083895973206886138815045 17265730494976291151027821)
          ·
            refine ⟨6474648935616109181635433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17265730494976291151027821 6474648935616109181635433)
            ·
              refine ⟨4855986701712081886226575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6474648935616109181635433 4855986701712081886226575)
              ·
                refine ⟨7283980052568122829339863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4855986701712081886226575 7283980052568122829339863)
                ·
                  refine ⟨10925970078852184244009795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7283980052568122829339863 10925970078852184244009795)
                  ·
                    refine ⟨16388955118278276366014693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10925970078852184244009795 16388955118278276366014693)
                    ·
                      refine ⟨3072929084677176818627755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16388955118278276366014693 3072929084677176818627755)
                      ·
                        rfl

theorem cell23_5984508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 1, 1, 1, 4].length) (baseStart_5984508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5984508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5984508 prefixEnd_5984508 := by exact prefixLift 5984508
  have htrace : WordTrace (prefixWord ++ tailWord_5984508) baseStart_5984508 baseEnd_5984508 := by
    simpa [prefixWord, tailWord_5984508, baseEnd_5984508] using wordTrace_append hprefix tailTrace_5984508
  have hstable : (prefixWord ++ tailWord_5984508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5984508).length < 2 ^ (prefixWord ++ tailWord_5984508).sum := by decide
  have hdescent : baseEnd_5984508 < baseStart_5984508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5984508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5984514 : List Nat := [3, 4, 1, 1, 2, 2, 10]
def baseStart_5984514 : Nat := 118140960795 + 5984514 * 2 ^ 59
def prefixEnd_5984514 : Nat := 4983230072969 + 3 ^ 40 * 5984514 * 2
def baseEnd_5984514 : Nat := 37937434142729676483367

theorem tailTrace_5984514 : CollatzResearch.WordTrace tailWord_5984514 prefixEnd_5984514 37937434142729676483367 := by
  unfold tailWord_5984514
  simp only [CollatzResearch.WordTrace]
  refine ⟨54568289360283831616218149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145515438294090217643248397 54568289360283831616218149)
  ·
    refine ⟨10231554255053218428040903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54568289360283831616218149 10231554255053218428040903)
    ·
      refine ⟨15347331382579827642061355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10231554255053218428040903 15347331382579827642061355)
      ·
        refine ⟨23020997073869741463092033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15347331382579827642061355 23020997073869741463092033)
        ·
          refine ⟨17265747805402306097319025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23020997073869741463092033 17265747805402306097319025)
          ·
            refine ⟨12949310854051729572989269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17265747805402306097319025 12949310854051729572989269)
            ·
              refine ⟨37937434142729676483367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12949310854051729572989269 37937434142729676483367)
              ·
                rfl

theorem cell23_5984514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 10].length) (baseStart_5984514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5984514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5984514 prefixEnd_5984514 := by exact prefixLift 5984514
  have htrace : WordTrace (prefixWord ++ tailWord_5984514) baseStart_5984514 baseEnd_5984514 := by
    simpa [prefixWord, tailWord_5984514, baseEnd_5984514] using wordTrace_append hprefix tailTrace_5984514
  have hstable : (prefixWord ++ tailWord_5984514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5984514).length < 2 ^ (prefixWord ++ tailWord_5984514).sum := by decide
  have hdescent : baseEnd_5984514 < baseStart_5984514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5984514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5984538 : List Nat := [3, 1, 1, 3, 5, 1, 1, 1, 1, 2, 4]
def baseStart_5984538 : Nat := 118140960795 + 5984538 * 2 ^ 59
def prefixEnd_5984538 : Nat := 4983230072969 + 3 ^ 40 * 5984538 * 2
def baseEnd_5984538 : Nat := 3072944489096811701252617

theorem tailTrace_5984538 : CollatzResearch.WordTrace tailWord_5984538 prefixEnd_5984538 3072944489096811701252617 := by
  unfold tailWord_5984538
  simp only [CollatzResearch.WordTrace]
  refine ⟨54568508198262094640936567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145516021862032252375830845 54568508198262094640936567)
  ·
    refine ⟨81852762297393141961404851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54568508198262094640936567 81852762297393141961404851)
    ·
      refine ⟨122779143446089712942107277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81852762297393141961404851 122779143446089712942107277)
      ·
        refine ⟨46042178792283642353290229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122779143446089712942107277 46042178792283642353290229)
        ·
          refine ⟨4316454261776591470620959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46042178792283642353290229 4316454261776591470620959)
          ·
            refine ⟨6474681392664887205931439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4316454261776591470620959 6474681392664887205931439)
            ·
              refine ⟨9712022088997330808897159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6474681392664887205931439 9712022088997330808897159)
              ·
                refine ⟨14568033133495996213345739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9712022088997330808897159 14568033133495996213345739)
                ·
                  refine ⟨21852049700243994320018609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14568033133495996213345739 21852049700243994320018609)
                  ·
                    refine ⟨16389037275182995740013957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21852049700243994320018609 16389037275182995740013957)
                    ·
                      refine ⟨3072944489096811701252617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16389037275182995740013957 3072944489096811701252617)
                      ·
                        rfl

theorem cell23_5984538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 1, 2, 4].length) (baseStart_5984538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5984538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5984538 prefixEnd_5984538 := by exact prefixLift 5984538
  have htrace : WordTrace (prefixWord ++ tailWord_5984538) baseStart_5984538 baseEnd_5984538 := by
    simpa [prefixWord, tailWord_5984538, baseEnd_5984538] using wordTrace_append hprefix tailTrace_5984538
  have hstable : (prefixWord ++ tailWord_5984538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5984538).length < 2 ^ (prefixWord ++ tailWord_5984538).sum := by decide
  have hdescent : baseEnd_5984538 < baseStart_5984538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5984538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5984587 : List Nat := [1, 1, 1, 1, 3, 1, 1, 7, 7]
def baseStart_5984587 : Nat := 118140960795 + 5984587 * 2 ^ 59
def prefixEnd_5984587 : Nat := 4983230072969 + 3 ^ 40 * 5984587 * 2
def baseEnd_5984587 : Nat := 341441072183209112171099

theorem tailTrace_5984587 : CollatzResearch.WordTrace tailWord_5984587 prefixEnd_5984587 341441072183209112171099 := by
  unfold tailWord_5984587
  simp only [CollatzResearch.WordTrace]
  refine ⟨218275819969870859932280015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145517213313247239954853343 218275819969870859932280015)
  ·
    refine ⟨327413729954806289898420023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218275819969870859932280015 327413729954806289898420023)
    ·
      refine ⟨491120594932209434847630035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327413729954806289898420023 491120594932209434847630035)
      ·
        refine ⟨736680892398314152271445053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491120594932209434847630035 736680892398314152271445053)
        ·
          refine ⟨276255334649367807101791895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 736680892398314152271445053 276255334649367807101791895)
          ·
            refine ⟨414383001974051710652687843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276255334649367807101791895 414383001974051710652687843)
            ·
              refine ⟨621574502961077565979031765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414383001974051710652687843 621574502961077565979031765)
              ·
                refine ⟨14568152413150255452633557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 621574502961077565979031765 14568152413150255452633557)
                ·
                  refine ⟨341441072183209112171099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14568152413150255452633557 341441072183209112171099)
                  ·
                    rfl

theorem cell23_5984587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 7].length) (baseStart_5984587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5984587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5984587 prefixEnd_5984587 := by exact prefixLift 5984587
  have htrace : WordTrace (prefixWord ++ tailWord_5984587) baseStart_5984587 baseEnd_5984587 := by
    simpa [prefixWord, tailWord_5984587, baseEnd_5984587] using wordTrace_append hprefix tailTrace_5984587
  have hstable : (prefixWord ++ tailWord_5984587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5984587).length < 2 ^ (prefixWord ++ tailWord_5984587).sum := by decide
  have hdescent : baseEnd_5984587 < baseStart_5984587 := by decide
  rcases family_descends (prefixWord ++ tailWord_5984587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5984594 : List Nat := [3, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4]
def baseStart_5984594 : Nat := 118140960795 + 5984594 * 2 ^ 59
def prefixEnd_5984594 : Nat := 4983230072969 + 3 ^ 40 * 5984594 * 2
def baseEnd_5984594 : Nat := 3072973244013463482152359

theorem tailTrace_5984594 : CollatzResearch.WordTrace tailWord_5984594 prefixEnd_5984594 3072973244013463482152359 := by
  unfold tailWord_5984594
  simp only [CollatzResearch.WordTrace]
  refine ⟨54569018820211375031946209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145517383520563666751856557 54569018820211375031946209)
  ·
    refine ⟨40926764115158531273959657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54569018820211375031946209 40926764115158531273959657)
    ·
      refine ⟨30695073086368898455469743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40926764115158531273959657 30695073086368898455469743)
      ·
        refine ⟨46042609629553347683204615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30695073086368898455469743 46042609629553347683204615)
        ·
          refine ⟨69063914444330021524806923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46042609629553347683204615 69063914444330021524806923)
          ·
            refine ⟨103595871666495032287210385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69063914444330021524806923 103595871666495032287210385)
            ·
              refine ⟨77696903749871274215407789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103595871666495032287210385 77696903749871274215407789)
              ·
                refine ⟨29136338906201727830777921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77696903749871274215407789 29136338906201727830777921)
                ·
                  refine ⟨21852254179651295873083441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29136338906201727830777921 21852254179651295873083441)
                  ·
                    refine ⟨16389190634738471904812581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21852254179651295873083441 16389190634738471904812581)
                    ·
                      refine ⟨3072973244013463482152359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16389190634738471904812581 3072973244013463482152359)
                      ·
                        rfl

theorem cell23_5984594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_5984594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5984594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5984594 prefixEnd_5984594 := by exact prefixLift 5984594
  have htrace : WordTrace (prefixWord ++ tailWord_5984594) baseStart_5984594 baseEnd_5984594 := by
    simpa [prefixWord, tailWord_5984594, baseEnd_5984594] using wordTrace_append hprefix tailTrace_5984594
  have hstable : (prefixWord ++ tailWord_5984594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5984594).length < 2 ^ (prefixWord ++ tailWord_5984594).sum := by decide
  have hdescent : baseEnd_5984594 < baseStart_5984594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5984594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5984621 : List Nat := [1, 5, 1, 1, 1, 2, 2, 5, 5]
def baseStart_5984621 : Nat := 118140960795 + 5984621 * 2 ^ 59
def prefixEnd_5984621 : Nat := 4983230072969 + 3 ^ 40 * 5984621 * 2
def baseEnd_5984621 : Nat := 341443011999014986279415

theorem tailTrace_5984621 : CollatzResearch.WordTrace tailWord_5984621 prefixEnd_5984621 341443011999014986279415 := by
  unfold tailWord_5984621
  simp only [CollatzResearch.WordTrace]
  refine ⟨218277060051747683739017717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145518040034498455826011811 218277060051747683739017717)
  ·
    refine ⟨20463474379851345350532911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 218277060051747683739017717 20463474379851345350532911)
    ·
      refine ⟨30695211569777018025799367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20463474379851345350532911 30695211569777018025799367)
      ·
        refine ⟨46042817354665527038699051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30695211569777018025799367 46042817354665527038699051)
        ·
          refine ⟨69064226031998290558048577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46042817354665527038699051 69064226031998290558048577)
          ·
            refine ⟨51798169523998717918536433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69064226031998290558048577 51798169523998717918536433)
            ·
              refine ⟨38848627142999038438902325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51798169523998717918536433 38848627142999038438902325)
              ·
                refine ⟨3642058794656159853647093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38848627142999038438902325 3642058794656159853647093)
                ·
                  refine ⟨341443011999014986279415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3642058794656159853647093 341443011999014986279415)
                  ·
                    rfl

theorem cell23_5984621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_5984621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5984621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5984621 prefixEnd_5984621 := by exact prefixLift 5984621
  have htrace : WordTrace (prefixWord ++ tailWord_5984621) baseStart_5984621 baseEnd_5984621 := by
    simpa [prefixWord, tailWord_5984621, baseEnd_5984621] using wordTrace_append hprefix tailTrace_5984621
  have hstable : (prefixWord ++ tailWord_5984621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5984621).length < 2 ^ (prefixWord ++ tailWord_5984621).sum := by decide
  have hdescent : baseEnd_5984621 < baseStart_5984621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5984621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5984627 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 7]
def baseStart_5984627 : Nat := 118140960795 + 5984627 * 2 ^ 59
def prefixEnd_5984627 : Nat := 4983230072969 + 3 ^ 40 * 5984627 * 2
def baseEnd_5984627 : Nat := 3072990188875061853039707

theorem tailTrace_5984627 : CollatzResearch.WordTrace tailWord_5984627 prefixEnd_5984627 3072990188875061853039707 := by
  unfold tailWord_5984627
  simp only [CollatzResearch.WordTrace]
  refine ⟨218277278889725946763736135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145518185926483964509157423 218277278889725946763736135)
  ·
    refine ⟨327415918334588920145604203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218277278889725946763736135 327415918334588920145604203)
    ·
      refine ⟨491123877501883380218406305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327415918334588920145604203 491123877501883380218406305)
      ·
        refine ⟨368342908126412535163804729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 491123877501883380218406305 368342908126412535163804729)
        ·
          refine ⟨276257181094809401372853547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368342908126412535163804729 276257181094809401372853547)
          ·
            refine ⟨414385771642214102059280321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276257181094809401372853547 414385771642214102059280321)
            ·
              refine ⟨310789328731660576544460241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 414385771642214102059280321 310789328731660576544460241)
              ·
                refine ⟨233091996548745432408345181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 310789328731660576544460241 233091996548745432408345181)
                ·
                  refine ⟨87409498705779537153129443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 233091996548745432408345181 87409498705779537153129443)
                  ·
                    refine ⟨131114248058669305729694165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 87409498705779537153129443 131114248058669305729694165)
                    ·
                      refine ⟨3072990188875061853039707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 131114248058669305729694165 3072990188875061853039707)
                      ·
                        rfl

theorem cell23_5984627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 7].length) (baseStart_5984627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5984627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5984627 prefixEnd_5984627 := by exact prefixLift 5984627
  have htrace : WordTrace (prefixWord ++ tailWord_5984627) baseStart_5984627 baseEnd_5984627 := by
    simpa [prefixWord, tailWord_5984627, baseEnd_5984627] using wordTrace_append hprefix tailTrace_5984627
  have hstable : (prefixWord ++ tailWord_5984627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5984627).length < 2 ^ (prefixWord ++ tailWord_5984627).sum := by decide
  have hdescent : baseEnd_5984627 < baseStart_5984627 := by decide
  rcases family_descends (prefixWord ++ tailWord_5984627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5984644 : List Nat := [2, 3, 2, 1, 1, 2, 1, 3, 1, 2, 5]
def baseStart_5984644 : Nat := 118140960795 + 5984644 * 2 ^ 59
def prefixEnd_5984644 : Nat := 4983230072969 + 3 ^ 40 * 5984644 * 2
def baseEnd_5984644 : Nat := 3072998918046188286527129

theorem tailTrace_5984644 : CollatzResearch.WordTrace tailWord_5984644 prefixEnd_5984644 3072998918046188286527129 := by
  unfold tailWord_5984644
  simp only [CollatzResearch.WordTrace]
  refine ⟨109138949465332179333552493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145518599287109572444736657 109138949465332179333552493)
  ·
    refine ⟨40927106049499567250082185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109138949465332179333552493 40927106049499567250082185)
    ·
      refine ⟨30695329537124675437561639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40927106049499567250082185 30695329537124675437561639)
      ·
        refine ⟨46042994305687013156342459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30695329537124675437561639 46042994305687013156342459)
        ·
          refine ⟨69064491458530519734513689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46042994305687013156342459 69064491458530519734513689)
          ·
            refine ⟨51798368593897889800885267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69064491458530519734513689 51798368593897889800885267)
            ·
              refine ⟨77697552890846834701327901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51798368593897889800885267 77697552890846834701327901)
              ·
                refine ⟨29136582334067563012997963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77697552890846834701327901 29136582334067563012997963)
                ·
                  refine ⟨43704873501101344519496945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29136582334067563012997963 43704873501101344519496945)
                  ·
                    refine ⟨32778655125826008389622709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43704873501101344519496945 32778655125826008389622709)
                    ·
                      refine ⟨3072998918046188286527129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32778655125826008389622709 3072998918046188286527129)
                      ·
                        rfl

theorem cell23_5984644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_5984644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5984644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5984644 prefixEnd_5984644 := by exact prefixLift 5984644
  have htrace : WordTrace (prefixWord ++ tailWord_5984644) baseStart_5984644 baseEnd_5984644 := by
    simpa [prefixWord, tailWord_5984644, baseEnd_5984644] using wordTrace_append hprefix tailTrace_5984644
  have hstable : (prefixWord ++ tailWord_5984644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5984644).length < 2 ^ (prefixWord ++ tailWord_5984644).sum := by decide
  have hdescent : baseEnd_5984644 < baseStart_5984644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5984644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5984671 : List Nat := [1, 1, 2, 5, 1, 1, 1, 2, 1, 6, 2]
def baseStart_5984671 : Nat := 118140960795 + 5984671 * 2 ^ 59
def prefixEnd_5984671 : Nat := 4983230072969 + 3 ^ 40 * 5984671 * 2
def baseEnd_5984671 : Nat := 3073012782023859680889505

theorem tailTrace_5984671 : CollatzResearch.WordTrace tailWord_5984671 prefixEnd_5984671 3073012782023859680889505 := by
  unfold tailWord_5984671
  simp only [CollatzResearch.WordTrace]
  refine ⟨218278883701566542278337867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145519255801044361518891911 218278883701566542278337867)
  ·
    refine ⟨327418325552349813417506801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218278883701566542278337867 327418325552349813417506801)
    ·
      refine ⟨245563744164262360063130101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327418325552349813417506801 245563744164262360063130101)
      ·
        refine ⟨23021601015399596255918447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 245563744164262360063130101 23021601015399596255918447)
        ·
          refine ⟨34532401523099394383877671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23021601015399596255918447 34532401523099394383877671)
          ·
            refine ⟨51798602284649091575816507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34532401523099394383877671 51798602284649091575816507)
            ·
              refine ⟨77697903426973637363724761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51798602284649091575816507 77697903426973637363724761)
              ·
                refine ⟨58273427570230228022793571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77697903426973637363724761 58273427570230228022793571)
                ·
                  refine ⟨87410141355345342034190357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58273427570230228022793571 87410141355345342034190357)
                  ·
                    refine ⟨4097350376031812907852673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 87410141355345342034190357 4097350376031812907852673)
                    ·
                      refine ⟨3073012782023859680889505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4097350376031812907852673 3073012782023859680889505)
                      ·
                        rfl

theorem cell23_5984671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_5984671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5984671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5984671 prefixEnd_5984671 := by exact prefixLift 5984671
  have htrace : WordTrace (prefixWord ++ tailWord_5984671) baseStart_5984671 baseEnd_5984671 := by
    simpa [prefixWord, tailWord_5984671, baseEnd_5984671] using wordTrace_append hprefix tailTrace_5984671
  have hstable : (prefixWord ++ tailWord_5984671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5984671).length < 2 ^ (prefixWord ++ tailWord_5984671).sum := by decide
  have hdescent : baseEnd_5984671 < baseStart_5984671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5984671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5984714 : List Nat := [3, 1, 2, 1, 2, 2, 1, 2, 1, 2, 6]
def baseStart_5984714 : Nat := 118140960795 + 5984714 * 2 ^ 59
def prefixEnd_5984714 : Nat := 4983230072969 + 3 ^ 40 * 5984714 * 2
def baseEnd_5984714 : Nat := 3073034861692003012651807

theorem tailTrace_5984714 : CollatzResearch.WordTrace tailWord_5984714 prefixEnd_5984714 3073034861692003012651807 := by
  unfold tailWord_5984714
  simp only [CollatzResearch.WordTrace]
  refine ⟨54570113010102690155538299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145520301360273840414768797 54570113010102690155538299)
  ·
    refine ⟨81855169515154035233307449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54570113010102690155538299 81855169515154035233307449)
    ·
      refine ⟨61391377136365526424980587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81855169515154035233307449 61391377136365526424980587)
      ·
        refine ⟨92087065704548289637470881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61391377136365526424980587 92087065704548289637470881)
        ·
          refine ⟨69065299278411217228103161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92087065704548289637470881 69065299278411217228103161)
          ·
            refine ⟨51798974458808412921077371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69065299278411217228103161 51798974458808412921077371)
            ·
              refine ⟨77698461688212619381616057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51798974458808412921077371 77698461688212619381616057)
              ·
                refine ⟨58273846266159464536212043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77698461688212619381616057 58273846266159464536212043)
                ·
                  refine ⟨87410769399239196804318065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58273846266159464536212043 87410769399239196804318065)
                  ·
                    refine ⟨65558077049429397603238549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 87410769399239196804318065 65558077049429397603238549)
                    ·
                      refine ⟨3073034861692003012651807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65558077049429397603238549 3073034861692003012651807)
                      ·
                        rfl

theorem cell23_5984714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_5984714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5984714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5984714 prefixEnd_5984714 := by exact prefixLift 5984714
  have htrace : WordTrace (prefixWord ++ tailWord_5984714) baseStart_5984714 baseEnd_5984714 := by
    simpa [prefixWord, tailWord_5984714, baseEnd_5984714] using wordTrace_append hprefix tailTrace_5984714
  have hstable : (prefixWord ++ tailWord_5984714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5984714).length < 2 ^ (prefixWord ++ tailWord_5984714).sum := by decide
  have hdescent : baseEnd_5984714 < baseStart_5984714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5984714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5984748 : List Nat := [2, 2, 1, 1, 2, 1, 5, 2, 2, 3, 2]
def baseStart_5984748 : Nat := 118140960795 + 5984748 * 2 ^ 59
def prefixEnd_5984748 : Nat := 4983230072969 + 3 ^ 40 * 5984748 * 2
def baseEnd_5984748 : Nat := 3073052320034255879626651

theorem tailTrace_5984748 : CollatzResearch.WordTrace tailWord_5984748 prefixEnd_5984748 3073052320034255879626651 := by
  unfold tailWord_5984748
  simp only [CollatzResearch.WordTrace]
  refine ⟨109140846061143792214445449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145521128081525056285927265 109140846061143792214445449)
  ·
    refine ⟨81855634545857844160834087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109140846061143792214445449 81855634545857844160834087)
    ·
      refine ⟨122783451818786766241251131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81855634545857844160834087 122783451818786766241251131)
      ·
        refine ⟨184175177728180149361876697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122783451818786766241251131 184175177728180149361876697)
        ·
          refine ⟨138131383296135112021407523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184175177728180149361876697 138131383296135112021407523)
          ·
            refine ⟨207197074944202668032111285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138131383296135112021407523 207197074944202668032111285)
            ·
              refine ⟨19424725776019000128010433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 207197074944202668032111285 19424725776019000128010433)
              ·
                refine ⟨14568544332014250096007825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19424725776019000128010433 14568544332014250096007825)
                ·
                  refine ⟨10926408249010687572005869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14568544332014250096007825 10926408249010687572005869)
                  ·
                    refine ⟨4097403093379007839502201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10926408249010687572005869 4097403093379007839502201)
                    ·
                      refine ⟨3073052320034255879626651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4097403093379007839502201 3073052320034255879626651)
                      ·
                        rfl

theorem cell23_5984748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 3, 2].length) (baseStart_5984748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5984748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5984748 prefixEnd_5984748 := by exact prefixLift 5984748
  have htrace : WordTrace (prefixWord ++ tailWord_5984748) baseStart_5984748 baseEnd_5984748 := by
    simpa [prefixWord, tailWord_5984748, baseEnd_5984748] using wordTrace_append hprefix tailTrace_5984748
  have hstable : (prefixWord ++ tailWord_5984748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5984748).length < 2 ^ (prefixWord ++ tailWord_5984748).sum := by decide
  have hdescent : baseEnd_5984748 < baseStart_5984748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5984748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5984775 : List Nat := [1, 1, 4, 3, 3, 2, 1, 2, 1, 5]
def baseStart_5984775 : Nat := 118140960795 + 5984775 * 2 ^ 59
def prefixEnd_5984775 : Nat := 4983230072969 + 3 ^ 40 * 5984775 * 2
def baseEnd_5984775 : Nat := 1024355394670642424663009

theorem tailTrace_5984775 : CollatzResearch.WordTrace tailWord_5984775 prefixEnd_5984775 1024355394670642424663009 := by
  unfold tailWord_5984775
  simp only [CollatzResearch.WordTrace]
  refine ⟨218282676893189768040123779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145521784595459845360082519 218282676893189768040123779)
  ·
    refine ⟨327424015339784652060185669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218282676893189768040123779 327424015339784652060185669)
    ·
      refine ⟨61392002876209622261284813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 327424015339784652060185669 61392002876209622261284813)
      ·
        refine ⟨23022001078578608347981805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61392002876209622261284813 23022001078578608347981805)
        ·
          refine ⟨8633250404466978130493177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23022001078578608347981805 8633250404466978130493177)
          ·
            refine ⟨6474937803350233597869883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8633250404466978130493177 6474937803350233597869883)
            ·
              refine ⟨9712406705025350396804825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6474937803350233597869883 9712406705025350396804825)
              ·
                refine ⟨7284305028769012797603619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9712406705025350396804825 7284305028769012797603619)
                ·
                  refine ⟨10926457543153519196405429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7284305028769012797603619 10926457543153519196405429)
                  ·
                    refine ⟨1024355394670642424663009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10926457543153519196405429 1024355394670642424663009)
                    ·
                      rfl

theorem cell23_5984775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 2, 1, 5].length) (baseStart_5984775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5984775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5984775 prefixEnd_5984775 := by exact prefixLift 5984775
  have htrace : WordTrace (prefixWord ++ tailWord_5984775) baseStart_5984775 baseEnd_5984775 := by
    simpa [prefixWord, tailWord_5984775, baseEnd_5984775] using wordTrace_append hprefix tailTrace_5984775
  have hstable : (prefixWord ++ tailWord_5984775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5984775).length < 2 ^ (prefixWord ++ tailWord_5984775).sum := by decide
  have hdescent : baseEnd_5984775 < baseStart_5984775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5984775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5984788 : List Nat := [2, 4, 3, 1, 1, 1, 1, 1, 3, 6]
def baseStart_5984788 : Nat := 118140960795 + 5984788 * 2 ^ 59
def prefixEnd_5984788 : Nat := 4983230072969 + 3 ^ 40 * 5984788 * 2
def baseEnd_5984788 : Nat := 1024357619753478574375489

theorem tailTrace_5984788 : CollatzResearch.WordTrace tailWord_5984788 prefixEnd_5984788 1024357619753478574375489 := by
  unfold tailWord_5984788
  simp only [CollatzResearch.WordTrace]
  refine ⟨109141575521071335630173509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145522100694761780840231345 109141575521071335630173509)
  ·
    refine ⟨20464045410200875430657533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109141575521071335630173509 20464045410200875430657533)
    ·
      refine ⟨7674017028825328286496575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20464045410200875430657533 7674017028825328286496575)
      ·
        refine ⟨11511025543237992429744863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7674017028825328286496575 11511025543237992429744863)
        ·
          refine ⟨17266538314856988644617295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11511025543237992429744863 17266538314856988644617295)
          ·
            refine ⟨25899807472285482966925943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17266538314856988644617295 25899807472285482966925943)
            ·
              refine ⟨38849711208428224450388915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25899807472285482966925943 38849711208428224450388915)
              ·
                refine ⟨58274566812642336675583373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38849711208428224450388915 58274566812642336675583373)
                ·
                  refine ⟨21852962554740876253343765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58274566812642336675583373 21852962554740876253343765)
                  ·
                    refine ⟨1024357619753478574375489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21852962554740876253343765 1024357619753478574375489)
                    ·
                      rfl

theorem cell23_5984788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_5984788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5984788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5984788 prefixEnd_5984788 := by exact prefixLift 5984788
  have htrace : WordTrace (prefixWord ++ tailWord_5984788) baseStart_5984788 baseEnd_5984788 := by
    simpa [prefixWord, tailWord_5984788, baseEnd_5984788] using wordTrace_append hprefix tailTrace_5984788
  have hstable : (prefixWord ++ tailWord_5984788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5984788).length < 2 ^ (prefixWord ++ tailWord_5984788).sum := by decide
  have hdescent : baseEnd_5984788 < baseStart_5984788 := by decide
  rcases family_descends (prefixWord ++ tailWord_5984788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5984828 : List Nat := [2, 2, 2, 2, 3, 1, 1, 3, 1, 3, 3]
def baseStart_5984828 : Nat := 118140960795 + 5984828 * 2 ^ 59
def prefixEnd_5984828 : Nat := 4983230072969 + 3 ^ 40 * 5984828 * 2
def baseEnd_5984828 : Nat := 3073093398486615566626283

theorem tailTrace_5984828 : CollatzResearch.WordTrace tailWord_5984828 prefixEnd_5984828 3073093398486615566626283 := by
  unfold tailWord_5984828
  simp only [CollatzResearch.WordTrace]
  refine ⟨109142304980998879045901569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145523073307998505394535425 109142304980998879045901569)
  ·
    refine ⟨81856728735749159284426177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109142304980998879045901569 81856728735749159284426177)
    ·
      refine ⟨61392546551811869463319633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81856728735749159284426177 61392546551811869463319633)
      ·
        refine ⟨46044409913858902097489725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61392546551811869463319633 46044409913858902097489725)
        ·
          refine ⟨17266653717697088286558647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46044409913858902097489725 17266653717697088286558647)
          ·
            refine ⟨25899980576545632429837971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17266653717697088286558647 25899980576545632429837971)
            ·
              refine ⟨38849970864818448644756957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25899980576545632429837971 38849970864818448644756957)
              ·
                refine ⟨14568739074306918241783859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38849970864818448644756957 14568739074306918241783859)
                ·
                  refine ⟨21853108611460377362675789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14568739074306918241783859 21853108611460377362675789)
                  ·
                    refine ⟨8194915729297641511003421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21853108611460377362675789 8194915729297641511003421)
                    ·
                      refine ⟨3073093398486615566626283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8194915729297641511003421 3073093398486615566626283)
                      ·
                        rfl

theorem cell23_5984828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_5984828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5984828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5984828 prefixEnd_5984828 := by exact prefixLift 5984828
  have htrace : WordTrace (prefixWord ++ tailWord_5984828) baseStart_5984828 baseEnd_5984828 := by
    simpa [prefixWord, tailWord_5984828, baseEnd_5984828] using wordTrace_append hprefix tailTrace_5984828
  have hstable : (prefixWord ++ tailWord_5984828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5984828).length < 2 ^ (prefixWord ++ tailWord_5984828).sum := by decide
  have hdescent : baseEnd_5984828 < baseStart_5984828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5984828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5984845 : List Nat := [1, 6, 1, 1, 2, 1, 2, 2, 1, 3, 3]
def baseStart_5984845 : Nat := 118140960795 + 5984845 * 2 ^ 59
def prefixEnd_5984845 : Nat := 4983230072969 + 3 ^ 40 * 5984845 * 2
def baseEnd_5984845 : Nat := 3073102127657742000113705

theorem tailTrace_5984845 : CollatzResearch.WordTrace tailWord_5984845 prefixEnd_5984845 3073102127657742000113705 := by
  unfold tailWord_5984845
  simp only [CollatzResearch.WordTrace]
  refine ⟨218285230002936169995171989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145523486668624113330114659 218285230002936169995171989)
  ·
    refine ⟨10232120156387632968523687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 218285230002936169995171989 10232120156387632968523687)
    ·
      refine ⟨15348180234581449452785531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10232120156387632968523687 15348180234581449452785531)
      ·
        refine ⟨23022270351872174179178297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15348180234581449452785531 23022270351872174179178297)
        ·
          refine ⟨17266702763904130634383723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23022270351872174179178297 17266702763904130634383723)
          ·
            refine ⟨25900054145856195951575585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17266702763904130634383723 25900054145856195951575585)
            ·
              refine ⟨19425040609392146963681689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25900054145856195951575585 19425040609392146963681689)
              ·
                refine ⟨14568780457044110222761267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19425040609392146963681689 14568780457044110222761267)
                ·
                  refine ⟨21853170685566165334141901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14568780457044110222761267 21853170685566165334141901)
                  ·
                    refine ⟨8194939007087312000303213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21853170685566165334141901 8194939007087312000303213)
                    ·
                      refine ⟨3073102127657742000113705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8194939007087312000303213 3073102127657742000113705)
                      ·
                        rfl

theorem cell23_5984845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_5984845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5984845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5984845 prefixEnd_5984845 := by exact prefixLift 5984845
  have htrace : WordTrace (prefixWord ++ tailWord_5984845) baseStart_5984845 baseEnd_5984845 := by
    simpa [prefixWord, tailWord_5984845, baseEnd_5984845] using wordTrace_append hprefix tailTrace_5984845
  have hstable : (prefixWord ++ tailWord_5984845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5984845).length < 2 ^ (prefixWord ++ tailWord_5984845).sum := by decide
  have hdescent : baseEnd_5984845 < baseStart_5984845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5984845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5984855 : List Nat := [1, 1, 3, 2, 2, 2, 3, 3, 1, 3, 2]
def baseStart_5984855 : Nat := 118140960795 + 5984855 * 2 ^ 59
def prefixEnd_5984855 : Nat := 4983230072969 + 3 ^ 40 * 5984855 * 2
def baseEnd_5984855 : Nat := 3073107262464286960988659

theorem tailTrace_5984855 : CollatzResearch.WordTrace tailWord_5984855 prefixEnd_5984855 3073107262464286960988659 := by
  unfold tailWord_5984855
  simp only [CollatzResearch.WordTrace]
  refine ⟨218285594732899941703036019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145523729821933294468690679 218285594732899941703036019)
  ·
    refine ⟨327428392099349912554554029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218285594732899941703036019 327428392099349912554554029)
    ·
      refine ⟨122785647037256217207957761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 327428392099349912554554029 122785647037256217207957761)
      ·
        refine ⟨92089235277942162905968321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122785647037256217207957761 92089235277942162905968321)
        ·
          refine ⟨69066926458456622179476241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92089235277942162905968321 69066926458456622179476241)
          ·
            refine ⟨51800194843842466634607181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69066926458456622179476241 51800194843842466634607181)
            ·
              refine ⟨19425073066440924987977693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51800194843842466634607181 19425073066440924987977693)
              ·
                refine ⟨7284402399915346870491635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19425073066440924987977693 7284402399915346870491635)
                ·
                  refine ⟨10926603599873020305737453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7284402399915346870491635 10926603599873020305737453)
                  ·
                    refine ⟨4097476349952382614651545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10926603599873020305737453 4097476349952382614651545)
                    ·
                      refine ⟨3073107262464286960988659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4097476349952382614651545 3073107262464286960988659)
                      ·
                        rfl

theorem cell23_5984855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3, 1, 3, 2].length) (baseStart_5984855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5984855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5984855 prefixEnd_5984855 := by exact prefixLift 5984855
  have htrace : WordTrace (prefixWord ++ tailWord_5984855) baseStart_5984855 baseEnd_5984855 := by
    simpa [prefixWord, tailWord_5984855, baseEnd_5984855] using wordTrace_append hprefix tailTrace_5984855
  have hstable : (prefixWord ++ tailWord_5984855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5984855).length < 2 ^ (prefixWord ++ tailWord_5984855).sum := by decide
  have hdescent : baseEnd_5984855 < baseStart_5984855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5984855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5984871 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 5]
def baseStart_5984871 : Nat := 118140960795 + 5984871 * 2 ^ 59
def prefixEnd_5984871 : Nat := 4983230072969 + 3 ^ 40 * 5984871 * 2
def baseEnd_5984871 : Nat := 3073115478154758898388585

theorem tailTrace_5984871 : CollatzResearch.WordTrace tailWord_5984871 prefixEnd_5984871 3073115478154758898388585 := by
  unfold tailWord_5984871
  simp only [CollatzResearch.WordTrace]
  refine ⟨218286178300841976435618467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145524118867227984290412311 218286178300841976435618467)
  ·
    refine ⟨327429267451262964653427701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218286178300841976435618467 327429267451262964653427701)
    ·
      refine ⟨30696493823555902936258847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 327429267451262964653427701 30696493823555902936258847)
      ·
        refine ⟨46044740735333854404388271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30696493823555902936258847 46044740735333854404388271)
        ·
          refine ⟨69067111103000781606582407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46044740735333854404388271 69067111103000781606582407)
          ·
            refine ⟨103600666654501172409873611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69067111103000781606582407 103600666654501172409873611)
            ·
              refine ⟨155400999981751758614810417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103600666654501172409873611 155400999981751758614810417)
              ·
                refine ⟨116550749986313818961107813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155400999981751758614810417 116550749986313818961107813)
                ·
                  refine ⟨21853265622433841055207715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116550749986313818961107813 21853265622433841055207715)
                  ·
                    refine ⟨32779898433650761582811573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21853265622433841055207715 32779898433650761582811573)
                    ·
                      refine ⟨3073115478154758898388585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32779898433650761582811573 3073115478154758898388585)
                      ·
                        rfl

theorem cell23_5984871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_5984871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5984871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5984871 prefixEnd_5984871 := by exact prefixLift 5984871
  have htrace : WordTrace (prefixWord ++ tailWord_5984871) baseStart_5984871 baseEnd_5984871 := by
    simpa [prefixWord, tailWord_5984871, baseEnd_5984871] using wordTrace_append hprefix tailTrace_5984871
  have hstable : (prefixWord ++ tailWord_5984871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5984871).length < 2 ^ (prefixWord ++ tailWord_5984871).sum := by decide
  have hdescent : baseEnd_5984871 < baseStart_5984871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5984871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5984878 : List Nat := [4, 1, 2, 2, 2, 1, 2, 1, 2, 6]
def baseStart_5984878 : Nat := 118140960795 + 5984878 * 2 ^ 59
def prefixEnd_5984878 : Nat := 4983230072969 + 3 ^ 40 * 5984878 * 2
def baseEnd_5984878 : Nat := 1024373024173113457000351

theorem tailTrace_5984878 : CollatzResearch.WordTrace tailWord_5984878 prefixEnd_5984878 1024373024173113457000351 := by
  unfold tailWord_5984878
  simp only [CollatzResearch.WordTrace]
  refine ⟨27285804201477077078890411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145524289074544411087415525 27285804201477077078890411)
  ·
    refine ⟨40928706302215615618335617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27285804201477077078890411 40928706302215615618335617)
    ·
      refine ⟨30696529726661711713751713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40928706302215615618335617 30696529726661711713751713)
      ·
        refine ⟨23022397294996283785313785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30696529726661711713751713 23022397294996283785313785)
        ·
          refine ⟨17266797971247212838985339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23022397294996283785313785 17266797971247212838985339)
          ·
            refine ⟨25900196956870819258478009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17266797971247212838985339 25900196956870819258478009)
            ·
              refine ⟨19425147717653114443858507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25900196956870819258478009 19425147717653114443858507)
              ·
                refine ⟨29137721576479671665787761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19425147717653114443858507 29137721576479671665787761)
                ·
                  refine ⟨21853291182359753749340821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29137721576479671665787761 21853291182359753749340821)
                  ·
                    refine ⟨1024373024173113457000351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21853291182359753749340821 1024373024173113457000351)
                    ·
                      rfl

theorem cell23_5984878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_5984878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5984878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5984878 prefixEnd_5984878 := by exact prefixLift 5984878
  have htrace : WordTrace (prefixWord ++ tailWord_5984878) baseStart_5984878 baseEnd_5984878 := by
    simpa [prefixWord, tailWord_5984878, baseEnd_5984878] using wordTrace_append hprefix tailTrace_5984878
  have hstable : (prefixWord ++ tailWord_5984878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5984878).length < 2 ^ (prefixWord ++ tailWord_5984878).sum := by decide
  have hdescent : baseEnd_5984878 < baseStart_5984878 := by decide
  rcases family_descends (prefixWord ++ tailWord_5984878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5984908 : List Nat := [2, 2, 1, 2, 1, 1, 2, 7, 5]
def baseStart_5984908 : Nat := 118140960795 + 5984908 * 2 ^ 59
def prefixEnd_5984908 : Nat := 4983230072969 + 3 ^ 40 * 5984908 * 2
def baseEnd_5984908 : Nat := 341459386326552805958435

theorem tailTrace_5984908 : CollatzResearch.WordTrace tailWord_5984908 prefixEnd_5984908 341459386326552805958435 := by
  unfold tailWord_5984908
  simp only [CollatzResearch.WordTrace]
  refine ⟨109143763900853965877357689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145525018534471954503143585 109143763900853965877357689)
  ·
    refine ⟨81857822925640474408018267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109143763900853965877357689 81857822925640474408018267)
    ·
      refine ⟨122786734388460711612027401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81857822925640474408018267 122786734388460711612027401)
      ·
        refine ⟨92090050791345533709020551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122786734388460711612027401 92090050791345533709020551)
        ·
          refine ⟨138135076187018300563530827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92090050791345533709020551 138135076187018300563530827)
          ·
            refine ⟨207202614280527450845296241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138135076187018300563530827 207202614280527450845296241)
            ·
              refine ⟨155401960710395588133972181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207202614280527450845296241 155401960710395588133972181)
              ·
                refine ⟨3642233454149896596889973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 155401960710395588133972181 3642233454149896596889973)
                ·
                  refine ⟨341459386326552805958435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3642233454149896596889973 341459386326552805958435)
                  ·
                    rfl

theorem cell23_5984908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 7, 5].length) (baseStart_5984908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5984908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5984908 prefixEnd_5984908 := by exact prefixLift 5984908
  have htrace : WordTrace (prefixWord ++ tailWord_5984908) baseStart_5984908 baseEnd_5984908 := by
    simpa [prefixWord, tailWord_5984908, baseEnd_5984908] using wordTrace_append hprefix tailTrace_5984908
  have hstable : (prefixWord ++ tailWord_5984908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5984908).length < 2 ^ (prefixWord ++ tailWord_5984908).sum := by decide
  have hdescent : baseEnd_5984908 < baseStart_5984908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5984908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985025 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 7, 1, 3]
def baseStart_5985025 : Nat := 118140960795 + 5985025 * 2 ^ 59
def prefixEnd_5985025 : Nat := 4983230072969 + 3 ^ 40 * 5985025 * 2
def baseEnd_5985025 : Nat := 3073194554175551295862877

theorem tailTrace_5985025 : CollatzResearch.WordTrace tailWord_5985025 prefixEnd_5985025 3073194554175551295862877 := by
  unfold tailWord_5985025
  simp only [CollatzResearch.WordTrace]
  refine ⟨218291795142284060736724529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145527863428189373824483019 218291795142284060736724529)
  ·
    refine ⟨163718846356713045552543397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218291795142284060736724529 163718846356713045552543397)
    ·
      refine ⟨30697283691883696041101887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163718846356713045552543397 30697283691883696041101887)
      ·
        refine ⟨46045925537825544061652831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30697283691883696041101887 46045925537825544061652831)
        ·
          refine ⟨69068888306738316092479247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46045925537825544061652831 69068888306738316092479247)
          ·
            refine ⟨103603332460107474138718871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69068888306738316092479247 103603332460107474138718871)
            ·
              refine ⟨155404998690161211208078307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103603332460107474138718871 155404998690161211208078307)
              ·
                refine ⟨233107498035241816812117461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155404998690161211208078307 233107498035241816812117461)
                ·
                  refine ⟨5463456985200980081534003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 233107498035241816812117461 5463456985200980081534003)
                  ·
                    refine ⟨8195185477801470122301005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5463456985200980081534003 8195185477801470122301005)
                    ·
                      refine ⟨3073194554175551295862877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8195185477801470122301005 3073194554175551295862877)
                      ·
                        rfl

theorem cell23_5985025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_5985025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985025 prefixEnd_5985025 := by exact prefixLift 5985025
  have htrace : WordTrace (prefixWord ++ tailWord_5985025) baseStart_5985025 baseEnd_5985025 := by
    simpa [prefixWord, tailWord_5985025, baseEnd_5985025] using wordTrace_append hprefix tailTrace_5985025
  have hstable : (prefixWord ++ tailWord_5985025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985025).length < 2 ^ (prefixWord ++ tailWord_5985025).sum := by decide
  have hdescent : baseEnd_5985025 < baseStart_5985025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985035 : List Nat := [1, 1, 1, 1, 5, 1, 1, 3, 4, 3, 2]
def baseStart_5985035 : Nat := 118140960795 + 5985035 * 2 ^ 59
def prefixEnd_5985035 : Nat := 4983230072969 + 3 ^ 40 * 5985035 * 2
def baseEnd_5985035 : Nat := 3073199688982096256737831

theorem tailTrace_5985035 : CollatzResearch.WordTrace tailWord_5985035 prefixEnd_5985035 3073199688982096256737831 := by
  unfold tailWord_5985035
  simp only [CollatzResearch.WordTrace]
  refine ⟨218292159872247832444588559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145528106581498554963059039 218292159872247832444588559)
  ·
    refine ⟨327438239808371748666882839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218292159872247832444588559 327438239808371748666882839)
    ·
      refine ⟨491157359712557623000324259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327438239808371748666882839 491157359712557623000324259)
      ·
        refine ⟨736736039568836434500486389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491157359712557623000324259 736736039568836434500486389)
        ·
          refine ⟨69069003709578415734420599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 736736039568836434500486389 69069003709578415734420599)
          ·
            refine ⟨103603505564367623601630899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69069003709578415734420599 103603505564367623601630899)
            ·
              refine ⟨155405258346551435402446349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103603505564367623601630899 155405258346551435402446349)
              ·
                refine ⟨58276971879956788275917381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155405258346551435402446349 58276971879956788275917381)
                ·
                  refine ⟨10926932227491897801734509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58276971879956788275917381 10926932227491897801734509)
                  ·
                    refine ⟨4097599585309461675650441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10926932227491897801734509 4097599585309461675650441)
                    ·
                      refine ⟨3073199688982096256737831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4097599585309461675650441 3073199688982096256737831)
                      ·
                        rfl

theorem cell23_5985035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4, 3, 2].length) (baseStart_5985035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985035 prefixEnd_5985035 := by exact prefixLift 5985035
  have htrace : WordTrace (prefixWord ++ tailWord_5985035) baseStart_5985035 baseEnd_5985035 := by
    simpa [prefixWord, tailWord_5985035, baseEnd_5985035] using wordTrace_append hprefix tailTrace_5985035
  have hstable : (prefixWord ++ tailWord_5985035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985035).length < 2 ^ (prefixWord ++ tailWord_5985035).sum := by decide
  have hdescent : baseEnd_5985035 < baseStart_5985035 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985068 : List Nat := [2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 5]
def baseStart_5985068 : Nat := 118140960795 + 5985068 * 2 ^ 59
def prefixEnd_5985068 : Nat := 4983230072969 + 3 ^ 40 * 5985068 * 2
def baseEnd_5985068 : Nat := 3073216633843694627625179

theorem tailTrace_5985068 : CollatzResearch.WordTrace tailWord_5985068 prefixEnd_5985068 3073216633843694627625179 := by
  unfold tailWord_5985068
  simp only [CollatzResearch.WordTrace]
  refine ⟨109146681740564139540269929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145528908987418852720359905 109146681740564139540269929)
  ·
    refine ⟨81860011305423104655202447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109146681740564139540269929 81860011305423104655202447)
    ·
      refine ⟨122790016958134656982803671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81860011305423104655202447 122790016958134656982803671)
      ·
        refine ⟨184185025437201985474205507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122790016958134656982803671 184185025437201985474205507)
        ·
          refine ⟨276277538155802978211308261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184185025437201985474205507 276277538155802978211308261)
          ·
            refine ⟨51802038404213058414620299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 276277538155802978211308261 51802038404213058414620299)
            ·
              refine ⟨77703057606319587621930449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51802038404213058414620299 77703057606319587621930449)
              ·
                refine ⟨58277293204739690716447837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77703057606319587621930449 58277293204739690716447837)
                ·
                  refine ⟨21853984951777384018667939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58277293204739690716447837 21853984951777384018667939)
                  ·
                    refine ⟨32780977427666076028001909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21853984951777384018667939 32780977427666076028001909)
                    ·
                      refine ⟨3073216633843694627625179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32780977427666076028001909 3073216633843694627625179)
                      ·
                        rfl

theorem cell23_5985068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 5].length) (baseStart_5985068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985068 prefixEnd_5985068 := by exact prefixLift 5985068
  have htrace : WordTrace (prefixWord ++ tailWord_5985068) baseStart_5985068 baseEnd_5985068 := by
    simpa [prefixWord, tailWord_5985068, baseEnd_5985068] using wordTrace_append hprefix tailTrace_5985068
  have hstable : (prefixWord ++ tailWord_5985068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985068).length < 2 ^ (prefixWord ++ tailWord_5985068).sum := by decide
  have hdescent : baseEnd_5985068 < baseStart_5985068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985075 : List Nat := [1, 1, 1, 2, 6, 1, 1, 2, 4, 4]
def baseStart_5985075 : Nat := 118140960795 + 5985075 * 2 ^ 59
def prefixEnd_5985075 : Nat := 4983230072969 + 3 ^ 40 * 5985075 * 2
def baseEnd_5985075 : Nat := 1024406742736092033412549

theorem tailTrace_5985075 : CollatzResearch.WordTrace tailWord_5985075 prefixEnd_5985075 1024406742736092033412549 := by
  unfold tailWord_5985075
  simp only [CollatzResearch.WordTrace]
  refine ⟨218293618792102919276044679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145529079194735279517363119 218293618792102919276044679)
  ·
    refine ⟨327440428188154378914067019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218293618792102919276044679 327440428188154378914067019)
    ·
      refine ⟨491160642282231568371100529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327440428188154378914067019 491160642282231568371100529)
      ·
        refine ⟨368370481711673676278325397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 491160642282231568371100529 368370481711673676278325397)
        ·
          refine ⟨17267366330234703575546503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 368370481711673676278325397 17267366330234703575546503)
          ·
            refine ⟨25901049495352055363319755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17267366330234703575546503 25901049495352055363319755)
            ·
              refine ⟨38851574243028083044979633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25901049495352055363319755 38851574243028083044979633)
              ·
                refine ⟨29138680682271062283734725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38851574243028083044979633 29138680682271062283734725)
                ·
                  refine ⟨5463502627925824178200261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29138680682271062283734725 5463502627925824178200261)
                  ·
                    refine ⟨1024406742736092033412549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5463502627925824178200261 1024406742736092033412549)
                    ·
                      rfl

theorem cell23_5985075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 4, 4].length) (baseStart_5985075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985075 prefixEnd_5985075 := by exact prefixLift 5985075
  have htrace : WordTrace (prefixWord ++ tailWord_5985075) baseStart_5985075 baseEnd_5985075 := by
    simpa [prefixWord, tailWord_5985075, baseEnd_5985075] using wordTrace_append hprefix tailTrace_5985075
  have hstable : (prefixWord ++ tailWord_5985075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985075).length < 2 ^ (prefixWord ++ tailWord_5985075).sum := by decide
  have hdescent : baseEnd_5985075 < baseStart_5985075 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985105 : List Nat := [1, 2, 2, 1, 6, 1, 2, 8]
def baseStart_5985105 : Nat := 118140960795 + 5985105 * 2 ^ 59
def prefixEnd_5985105 : Nat := 4983230072969 + 3 ^ 40 * 5985105 * 2
def baseEnd_5985105 : Nat := 113823541949181888254167

theorem tailTrace_5985105 : CollatzResearch.WordTrace tailWord_5985105 prefixEnd_5985105 113823541949181888254167 := by
  unfold tailWord_5985105
  simp only [CollatzResearch.WordTrace]
  refine ⟨218294712981994234399636769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145529808654662822933091179 218294712981994234399636769)
  ·
    refine ⟨163721034736495675799727577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218294712981994234399636769 163721034736495675799727577)
    ·
      refine ⟨122790776052371756849795683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163721034736495675799727577 122790776052371756849795683)
      ·
        refine ⟨184186164078557635274693525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122790776052371756849795683 184186164078557635274693525)
        ·
          refine ⟨8633726441182389153501259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 184186164078557635274693525 8633726441182389153501259)
          ·
            refine ⟨12950589661773583730251889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8633726441182389153501259 12950589661773583730251889)
            ·
              refine ⟨9712942246330187797688917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12950589661773583730251889 9712942246330187797688917)
              ·
                refine ⟨113823541949181888254167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9712942246330187797688917 113823541949181888254167)
                ·
                  rfl

theorem cell23_5985105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 8].length) (baseStart_5985105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985105 prefixEnd_5985105 := by exact prefixLift 5985105
  have htrace : WordTrace (prefixWord ++ tailWord_5985105) baseStart_5985105 baseEnd_5985105 := by
    simpa [prefixWord, tailWord_5985105, baseEnd_5985105] using wordTrace_append hprefix tailTrace_5985105
  have hstable : (prefixWord ++ tailWord_5985105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985105).length < 2 ^ (prefixWord ++ tailWord_5985105).sum := by decide
  have hdescent : baseEnd_5985105 < baseStart_5985105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985148 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 3, 8]
def baseStart_5985148 : Nat := 118140960795 + 5985148 * 2 ^ 59
def prefixEnd_5985148 : Nat := 4983230072969 + 3 ^ 40 * 5985148 * 2
def baseEnd_5985148 : Nat := 1024419237432018104874937

theorem tailTrace_5985148 : CollatzResearch.WordTrace tailWord_5985148 prefixEnd_5985148 1024419237432018104874937 := by
  unfold tailWord_5985148
  simp only [CollatzResearch.WordTrace]
  refine ⟨109148140660419226371726049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145530854213892301828968065 109148140660419226371726049)
  ·
    refine ⟨81861105495314419778794537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109148140660419226371726049 81861105495314419778794537)
    ·
      refine ⟨61395829121485814834095903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81861105495314419778794537 61395829121485814834095903)
      ·
        refine ⟨92093743682228722251143855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61395829121485814834095903 92093743682228722251143855)
        ·
          refine ⟨138140615523343083376715783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92093743682228722251143855 138140615523343083376715783)
          ·
            refine ⟨207210923285014625065073675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138140615523343083376715783 207210923285014625065073675)
            ·
              refine ⟨310816384927521937597610513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207210923285014625065073675 310816384927521937597610513)
              ·
                refine ⟨233112288695641453198207885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 310816384927521937597610513 233112288695641453198207885)
                ·
                  refine ⟨87417108260865544949327957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 233112288695641453198207885 87417108260865544949327957)
                  ·
                    refine ⟨1024419237432018104874937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 87417108260865544949327957 1024419237432018104874937)
                    ·
                      rfl

theorem cell23_5985148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_5985148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985148 prefixEnd_5985148 := by exact prefixLift 5985148
  have htrace : WordTrace (prefixWord ++ tailWord_5985148) baseStart_5985148 baseEnd_5985148 := by
    simpa [prefixWord, tailWord_5985148, baseEnd_5985148] using wordTrace_append hprefix tailTrace_5985148
  have hstable : (prefixWord ++ tailWord_5985148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985148).length < 2 ^ (prefixWord ++ tailWord_5985148).sum := by decide
  have hdescent : baseEnd_5985148 < baseStart_5985148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985150 : List Nat := [4, 2, 3, 1, 2, 1, 1, 4, 1, 2, 2]
def baseStart_5985150 : Nat := 118140960795 + 5985150 * 2 ^ 59
def prefixEnd_5985150 : Nat := 4983230072969 + 3 ^ 40 * 5985150 * 2
def baseEnd_5985150 : Nat := 3073258739257363306799803

theorem tailTrace_5985150 : CollatzResearch.WordTrace tailWord_5985150 prefixEnd_5985150 3073258739257363306799803 := by
  unfold tailWord_5985150
  simp only [CollatzResearch.WordTrace]
  refine ⟨27287044283353900885628113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145530902844554138056683269 27287044283353900885628113)
  ·
    refine ⟨20465283212515425664221085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27287044283353900885628113 20465283212515425664221085)
    ·
      refine ⟨7674481204693284624082907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20465283212515425664221085 7674481204693284624082907)
      ·
        refine ⟨11511721807039926936124361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7674481204693284624082907 11511721807039926936124361)
        ·
          refine ⟨8633791355279945202093271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11511721807039926936124361 8633791355279945202093271)
          ·
            refine ⟨12950687032919917803139907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8633791355279945202093271 12950687032919917803139907)
            ·
              refine ⟨19426030549379876704709861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12950687032919917803139907 19426030549379876704709861)
              ·
                refine ⟨3642380728008726882133099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19426030549379876704709861 3642380728008726882133099)
                ·
                  refine ⟨5463571092013090323199649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3642380728008726882133099 5463571092013090323199649)
                  ·
                    refine ⟨4097678319009817742399737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5463571092013090323199649 4097678319009817742399737)
                    ·
                      refine ⟨3073258739257363306799803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4097678319009817742399737 3073258739257363306799803)
                      ·
                        rfl

theorem cell23_5985150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_5985150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985150 prefixEnd_5985150 := by exact prefixLift 5985150
  have htrace : WordTrace (prefixWord ++ tailWord_5985150) baseStart_5985150 baseEnd_5985150 := by
    simpa [prefixWord, tailWord_5985150, baseEnd_5985150] using wordTrace_append hprefix tailTrace_5985150
  have hstable : (prefixWord ++ tailWord_5985150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985150).length < 2 ^ (prefixWord ++ tailWord_5985150).sum := by decide
  have hdescent : baseEnd_5985150 < baseStart_5985150 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985175 : List Nat := [1, 1, 3, 3, 1, 2, 1, 2, 2, 4, 3]
def baseStart_5985175 : Nat := 118140960795 + 5985175 * 2 ^ 59
def prefixEnd_5985175 : Nat := 4983230072969 + 3 ^ 40 * 5985175 * 2
def baseEnd_5985175 : Nat := 3073271576273725708987187

theorem tailTrace_5985175 : CollatzResearch.WordTrace tailWord_5985175 prefixEnd_5985175 3073271576273725708987187 := by
  unfold tailWord_5985175
  simp only [CollatzResearch.WordTrace]
  refine ⟨218297266091740636354684979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145531510727827090903123319 218297266091740636354684979)
  ·
    refine ⟨327445899137610954532027469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218297266091740636354684979 327445899137610954532027469)
    ·
      refine ⟨122792212176604107949510301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 327445899137610954532027469 122792212176604107949510301)
      ·
        refine ⟨46047079566226540481066363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122792212176604107949510301 46047079566226540481066363)
        ·
          refine ⟨69070619349339810721599545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46047079566226540481066363 69070619349339810721599545)
          ·
            refine ⟨51802964512004858041199659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69070619349339810721599545 51802964512004858041199659)
            ·
              refine ⟨77704446768007287061799489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51802964512004858041199659 77704446768007287061799489)
              ·
                refine ⟨58278335076005465296349617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77704446768007287061799489 58278335076005465296349617)
                ·
                  refine ⟨43708751307004098972262213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58278335076005465296349617 43708751307004098972262213)
                  ·
                    refine ⟨8195390870063268557299165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43708751307004098972262213 8195390870063268557299165)
                    ·
                      refine ⟨3073271576273725708987187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8195390870063268557299165 3073271576273725708987187)
                      ·
                        rfl

theorem cell23_5985175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_5985175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985175 prefixEnd_5985175 := by exact prefixLift 5985175
  have htrace : WordTrace (prefixWord ++ tailWord_5985175) baseStart_5985175 baseEnd_5985175 := by
    simpa [prefixWord, tailWord_5985175, baseEnd_5985175] using wordTrace_append hprefix tailTrace_5985175
  have hstable : (prefixWord ++ tailWord_5985175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985175).length < 2 ^ (prefixWord ++ tailWord_5985175).sum := by decide
  have hdescent : baseEnd_5985175 < baseStart_5985175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985319 : List Nat := [1, 1, 7, 1, 1, 1, 1, 4, 6]
def baseStart_5985319 : Nat := 118140960795 + 5985319 * 2 ^ 59
def prefixEnd_5985319 : Nat := 4983230072969 + 3 ^ 40 * 5985319 * 2
def baseEnd_5985319 : Nat := 341482835276441460620725

theorem tailTrace_5985319 : CollatzResearch.WordTrace tailWord_5985319 prefixEnd_5985319 341482835276441460620725 := by
  unfold tailWord_5985319
  simp only [CollatzResearch.WordTrace]
  refine ⟨218302518203218948947927011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145535012135479299298618007 218302518203218948947927011)
  ·
    refine ⟨327453777304828423421890517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218302518203218948947927011 327453777304828423421890517)
    ·
      refine ⟨7674697905581916173950559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 327453777304828423421890517 7674697905581916173950559)
      ·
        refine ⟨11512046858372874260925839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7674697905581916173950559 11512046858372874260925839)
        ·
          refine ⟨17268070287559311391388759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11512046858372874260925839 17268070287559311391388759)
          ·
            refine ⟨25902105431338967087083139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17268070287559311391388759 25902105431338967087083139)
            ·
              refine ⟨38853158147008450630624709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25902105431338967087083139 38853158147008450630624709)
              ·
                refine ⟨7284967152564084493242133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38853158147008450630624709 7284967152564084493242133)
                ·
                  refine ⟨341482835276441460620725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7284967152564084493242133 341482835276441460620725)
                  ·
                    rfl

theorem cell23_5985319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 4, 6].length) (baseStart_5985319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985319 prefixEnd_5985319 := by exact prefixLift 5985319
  have htrace : WordTrace (prefixWord ++ tailWord_5985319) baseStart_5985319 baseEnd_5985319 := by
    simpa [prefixWord, tailWord_5985319, baseEnd_5985319] using wordTrace_append hprefix tailTrace_5985319
  have hstable : (prefixWord ++ tailWord_5985319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985319).length < 2 ^ (prefixWord ++ tailWord_5985319).sum := by decide
  have hdescent : baseEnd_5985319 < baseStart_5985319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985329 : List Nat := [1, 2, 2, 3, 1, 2, 2, 3, 3, 1, 3]
def baseStart_5985329 : Nat := 118140960795 + 5985329 * 2 ^ 59
def prefixEnd_5985329 : Nat := 4983230072969 + 3 ^ 40 * 5985329 * 2
def baseEnd_5985329 : Nat := 3073350652294518106461479

theorem tailTrace_5985329 : CollatzResearch.WordTrace tailWord_5985329 prefixEnd_5985329 3073350652294518106461479 := by
  unfold tailWord_5985329
  simp only [CollatzResearch.WordTrace]
  refine ⟨218302882933182720655791041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145535255288788480437194027 218302882933182720655791041)
  ·
    refine ⟨163727162199887040491843281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218302882933182720655791041 163727162199887040491843281)
    ·
      refine ⟨122795371649915280368882461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163727162199887040491843281 122795371649915280368882461)
      ·
        refine ⟨46048264368718230138330923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122795371649915280368882461 46048264368718230138330923)
        ·
          refine ⟨69072396553077345207496385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46048264368718230138330923 69072396553077345207496385)
          ·
            refine ⟨51804297414808008905622289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69072396553077345207496385 51804297414808008905622289)
            ·
              refine ⟨38853223061106006679216717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51804297414808008905622289 38853223061106006679216717)
              ·
                refine ⟨14569958647914752504706269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38853223061106006679216717 14569958647914752504706269)
                ·
                  refine ⟨5463734492968032189264851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14569958647914752504706269 5463734492968032189264851)
                  ·
                    refine ⟨8195601739452048283897277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5463734492968032189264851 8195601739452048283897277)
                    ·
                      refine ⟨3073350652294518106461479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8195601739452048283897277 3073350652294518106461479)
                      ·
                        rfl

theorem cell23_5985329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_5985329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985329 prefixEnd_5985329 := by exact prefixLift 5985329
  have htrace : WordTrace (prefixWord ++ tailWord_5985329) baseStart_5985329 baseEnd_5985329 := by
    simpa [prefixWord, tailWord_5985329, baseEnd_5985329] using wordTrace_append hprefix tailTrace_5985329
  have hstable : (prefixWord ++ tailWord_5985329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985329).length < 2 ^ (prefixWord ++ tailWord_5985329).sum := by decide
  have hdescent : baseEnd_5985329 < baseStart_5985329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985352 : List Nat := [2, 1, 3, 1, 1, 1, 3, 3, 3, 1, 4]
def baseStart_5985352 : Nat := 118140960795 + 5985352 * 2 ^ 59
def prefixEnd_5985352 : Nat := 4983230072969 + 3 ^ 40 * 5985352 * 2
def baseEnd_5985352 : Nat := 3073362462349571516473873

theorem tailTrace_5985352 : CollatzResearch.WordTrace tailWord_5985352 prefixEnd_5985352 3073362462349571516473873 := by
  unfold tailWord_5985352
  simp only [CollatzResearch.WordTrace]
  refine ⟨109151860906049697791939155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145535814541399597055918873 109151860906049697791939155)
  ·
    refine ⟨163727791359074546687908733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109151860906049697791939155 163727791359074546687908733)
    ·
      refine ⟨61397921759652955007965775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163727791359074546687908733 61397921759652955007965775)
      ·
        refine ⟨92096882639479432511948663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61397921759652955007965775 92096882639479432511948663)
        ·
          refine ⟨138145323959219148767922995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92096882639479432511948663 138145323959219148767922995)
          ·
            refine ⟨207217985938828723151884493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138145323959219148767922995 207217985938828723151884493)
            ·
              refine ⟨77706744727060771181956685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 207217985938828723151884493 77706744727060771181956685)
              ·
                refine ⟨29140029272647789193233757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77706744727060771181956685 29140029272647789193233757)
                ·
                  refine ⟨10927510977242920947462659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29140029272647789193233757 10927510977242920947462659)
                  ·
                    refine ⟨16391266465864381421193989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10927510977242920947462659 16391266465864381421193989)
                    ·
                      refine ⟨3073362462349571516473873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16391266465864381421193989 3073362462349571516473873)
                      ·
                        rfl

theorem cell23_5985352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_5985352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985352 prefixEnd_5985352 := by exact prefixLift 5985352
  have htrace : WordTrace (prefixWord ++ tailWord_5985352) baseStart_5985352 baseEnd_5985352 := by
    simpa [prefixWord, tailWord_5985352, baseEnd_5985352] using wordTrace_append hprefix tailTrace_5985352
  have hstable : (prefixWord ++ tailWord_5985352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985352).length < 2 ^ (prefixWord ++ tailWord_5985352).sum := by decide
  have hdescent : baseEnd_5985352 < baseStart_5985352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985355 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 5]
def baseStart_5985355 : Nat := 118140960795 + 5985355 * 2 ^ 59
def prefixEnd_5985355 : Nat := 4983230072969 + 3 ^ 40 * 5985355 * 2
def baseEnd_5985355 : Nat := 3073364002791535004736359

theorem tailTrace_5985355 : CollatzResearch.WordTrace tailWord_5985355 prefixEnd_5985355 3073364002791535004736359 := by
  unfold tailWord_5985355
  simp only [CollatzResearch.WordTrace]
  refine ⟨218303831231088527096237519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145535887487392351397491679 218303831231088527096237519)
  ·
    refine ⟨327455746846632790644356279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218303831231088527096237519 327455746846632790644356279)
    ·
      refine ⟨491183620269949185966534419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327455746846632790644356279 491183620269949185966534419)
      ·
        refine ⟨736775430404923778949801629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491183620269949185966534419 736775430404923778949801629)
        ·
          refine ⟨276290786401846417106175611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 736775430404923778949801629 276290786401846417106175611)
          ·
            refine ⟨414436179602769625659263417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276290786401846417106175611 414436179602769625659263417)
            ·
              refine ⟨310827134702077219244447563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 414436179602769625659263417 310827134702077219244447563)
              ·
                refine ⟨466240702053115828866671345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 310827134702077219244447563 466240702053115828866671345)
                ·
                  refine ⟨349680526539836871650003509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 466240702053115828866671345 349680526539836871650003509)
                  ·
                    refine ⟨32782549363109706717187829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 349680526539836871650003509 32782549363109706717187829)
                    ·
                      refine ⟨3073364002791535004736359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32782549363109706717187829 3073364002791535004736359)
                      ·
                        rfl

theorem cell23_5985355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 5].length) (baseStart_5985355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985355 prefixEnd_5985355 := by exact prefixLift 5985355
  have htrace : WordTrace (prefixWord ++ tailWord_5985355) baseStart_5985355 baseEnd_5985355 := by
    simpa [prefixWord, tailWord_5985355, baseEnd_5985355] using wordTrace_append hprefix tailTrace_5985355
  have hstable : (prefixWord ++ tailWord_5985355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985355).length < 2 ^ (prefixWord ++ tailWord_5985355).sum := by decide
  have hdescent : baseEnd_5985355 < baseStart_5985355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985375 : List Nat := [1, 1, 2, 3, 1, 1, 14]
def baseStart_5985375 : Nat := 118140960795 + 5985375 * 2 ^ 59
def prefixEnd_5985375 : Nat := 4983230072969 + 3 ^ 40 * 5985375 * 2
def baseEnd_5985375 : Nat := 37942892251908949709707

theorem tailTrace_5985375 : CollatzResearch.WordTrace tailWord_5985375 prefixEnd_5985375 37942892251908949709707 := by
  unfold tailWord_5985375
  simp only [CollatzResearch.WordTrace]
  refine ⟨218304560691016070511965579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145536373794010713674643719 218304560691016070511965579)
  ·
    refine ⟨327456841036524105767948369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218304560691016070511965579 327456841036524105767948369)
    ·
      refine ⟨245592630777393079325961277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327456841036524105767948369 245592630777393079325961277)
      ·
        refine ⟨92097236541522404747235479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245592630777393079325961277 92097236541522404747235479)
        ·
          refine ⟨138145854812283607120853219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92097236541522404747235479 138145854812283607120853219)
          ·
            refine ⟨207218782218425410681279829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138145854812283607120853219 207218782218425410681279829)
            ·
              refine ⟨37942892251908949709707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 207218782218425410681279829 37942892251908949709707)
              ·
                rfl

theorem cell23_5985375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 14].length) (baseStart_5985375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985375 prefixEnd_5985375 := by exact prefixLift 5985375
  have htrace : WordTrace (prefixWord ++ tailWord_5985375) baseStart_5985375 baseEnd_5985375 := by
    simpa [prefixWord, tailWord_5985375, baseEnd_5985375] using wordTrace_append hprefix tailTrace_5985375
  have hstable : (prefixWord ++ tailWord_5985375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985375).length < 2 ^ (prefixWord ++ tailWord_5985375).sum := by decide
  have hdescent : baseEnd_5985375 < baseStart_5985375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985389 : List Nat := [1, 5, 1, 1, 2, 3, 1, 2, 1, 1, 5]
def baseStart_5985389 : Nat := 118140960795 + 5985389 * 2 ^ 59
def prefixEnd_5985389 : Nat := 4983230072969 + 3 ^ 40 * 5985389 * 2
def baseEnd_5985389 : Nat := 3073381461133787871711203

theorem tailTrace_5985389 : CollatzResearch.WordTrace tailWord_5985389 prefixEnd_5985389 3073381461133787871711203 := by
  unfold tailWord_5985389
  simp only [CollatzResearch.WordTrace]
  refine ⟨218305071312965350902975221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145536714208643567268650147 218305071312965350902975221)
  ·
    refine ⟨20466100435590501647153927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 218305071312965350902975221 20466100435590501647153927)
    ·
      refine ⟨30699150653385752470730891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20466100435590501647153927 30699150653385752470730891)
      ·
        refine ⟨46048725980078628706096337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30699150653385752470730891 46048725980078628706096337)
        ·
          refine ⟨34536544485058971529572253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46048725980078628706096337 34536544485058971529572253)
          ·
            refine ⟨12951204181897114323589595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34536544485058971529572253 12951204181897114323589595)
            ·
              refine ⟨19426806272845671485384393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12951204181897114323589595 19426806272845671485384393)
              ·
                refine ⟨14570104704634253614038295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19426806272845671485384393 14570104704634253614038295)
                ·
                  refine ⟨21855157056951380421057443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14570104704634253614038295 21855157056951380421057443)
                  ·
                    refine ⟨32782735585427070631586165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21855157056951380421057443 32782735585427070631586165)
                    ·
                      refine ⟨3073381461133787871711203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32782735585427070631586165 3073381461133787871711203)
                      ·
                        rfl

theorem cell23_5985389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_5985389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985389 prefixEnd_5985389 := by exact prefixLift 5985389
  have htrace : WordTrace (prefixWord ++ tailWord_5985389) baseStart_5985389 baseEnd_5985389 := by
    simpa [prefixWord, tailWord_5985389, baseEnd_5985389] using wordTrace_append hprefix tailTrace_5985389
  have hstable : (prefixWord ++ tailWord_5985389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985389).length < 2 ^ (prefixWord ++ tailWord_5985389).sum := by decide
  have hdescent : baseEnd_5985389 < baseStart_5985389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985409 : List Nat := [1, 2, 4, 2, 2, 1, 4, 7]
def baseStart_5985409 : Nat := 118140960795 + 5985409 * 2 ^ 59
def prefixEnd_5985409 : Nat := 4983230072969 + 3 ^ 40 * 5985409 * 2
def baseEnd_5985409 : Nat := 113829323360995473831893

theorem tailTrace_5985409 : CollatzResearch.WordTrace tailWord_5985409 prefixEnd_5985409 113829323360995473831893 := by
  unfold tailWord_5985409
  simp only [CollatzResearch.WordTrace]
  refine ⟨218305800772892894318703281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145537200515261929545802187 218305800772892894318703281)
  ·
    refine ⟨163729350579669670739027461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218305800772892894318703281 163729350579669670739027461)
    ·
      refine ⟨30699253233688063263567649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163729350579669670739027461 30699253233688063263567649)
      ·
        refine ⟨23024439925266047447675737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30699253233688063263567649 23024439925266047447675737)
        ·
          refine ⟨17268329943949535585756803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23024439925266047447675737 17268329943949535585756803)
          ·
            refine ⟨25902494915924303378635205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17268329943949535585756803 25902494915924303378635205)
            ·
              refine ⟨4856717796735806883494101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25902494915924303378635205 4856717796735806883494101)
              ·
                refine ⟨113829323360995473831893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4856717796735806883494101 113829323360995473831893)
                ·
                  rfl

theorem cell23_5985409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 7].length) (baseStart_5985409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985409 prefixEnd_5985409 := by exact prefixLift 5985409
  have htrace : WordTrace (prefixWord ++ tailWord_5985409) baseStart_5985409 baseEnd_5985409 := by
    simpa [prefixWord, tailWord_5985409, baseEnd_5985409] using wordTrace_append hprefix tailTrace_5985409
  have hstable : (prefixWord ++ tailWord_5985409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985409).length < 2 ^ (prefixWord ++ tailWord_5985409).sum := by decide
  have hdescent : baseEnd_5985409 < baseStart_5985409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985436 : List Nat := [2, 2, 3, 2, 1, 2, 2, 1, 4, 1, 3]
def baseStart_5985436 : Nat := 118140960795 + 5985436 * 2 ^ 59
def prefixEnd_5985436 : Nat := 4983230072969 + 3 ^ 40 * 5985436 * 2
def baseEnd_5985436 : Nat := 3073405594724549187823487

theorem tailTrace_5985436 : CollatzResearch.WordTrace tailWord_5985436 prefixEnd_5985436 3073405594724549187823487 := by
  unfold tailWord_5985436
  simp only [CollatzResearch.WordTrace]
  refine ⟨109153392771897538964968081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145537857029196718619957441 109153392771897538964968081)
  ·
    refine ⟨81865044578923154223726061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109153392771897538964968081 81865044578923154223726061)
    ·
      refine ⟨30699391717096182833897273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81865044578923154223726061 30699391717096182833897273)
      ·
        refine ⟨23024543787822137125422955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30699391717096182833897273 23024543787822137125422955)
        ·
          refine ⟨34536815681733205688134433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23024543787822137125422955 34536815681733205688134433)
          ·
            refine ⟨25902611761299904266100825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34536815681733205688134433 25902611761299904266100825)
            ·
              refine ⟨19426958820974928199575619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25902611761299904266100825 19426958820974928199575619)
              ·
                refine ⟨29140438231462392299363429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19426958820974928199575619 29140438231462392299363429)
                ·
                  refine ⟨5463832168399198556130643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29140438231462392299363429 5463832168399198556130643)
                  ·
                    refine ⟨8195748252598797834195965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5463832168399198556130643 8195748252598797834195965)
                    ·
                      refine ⟨3073405594724549187823487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8195748252598797834195965 3073405594724549187823487)
                      ·
                        rfl

theorem cell23_5985436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_5985436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985436 prefixEnd_5985436 := by exact prefixLift 5985436
  have htrace : WordTrace (prefixWord ++ tailWord_5985436) baseStart_5985436 baseEnd_5985436 := by
    simpa [prefixWord, tailWord_5985436, baseEnd_5985436] using wordTrace_append hprefix tailTrace_5985436
  have hstable : (prefixWord ++ tailWord_5985436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985436).length < 2 ^ (prefixWord ++ tailWord_5985436).sum := by decide
  have hdescent : baseEnd_5985436 < baseStart_5985436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985586 : List Nat := [3, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3]
def baseStart_5985586 : Nat := 118140960795 + 5985586 * 2 ^ 59
def prefixEnd_5985586 : Nat := 4983230072969 + 3 ^ 40 * 5985586 * 2
def baseEnd_5985586 : Nat := 3073482616822723600947797

theorem tailTrace_5985586 : CollatzResearch.WordTrace tailWord_5985586 prefixEnd_5985586 3073482616822723600947797 := by
  unfold tailWord_5985586
  simp only [CollatzResearch.WordTrace]
  refine ⟨54578064123312913386974153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145541504328834435698597741 54578064123312913386974153)
  ·
    refine ⟨40933548092484685040230615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54578064123312913386974153 40933548092484685040230615)
    ·
      refine ⟨61400322138727027560345923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40933548092484685040230615 61400322138727027560345923)
      ·
        refine ⟨92100483208090541340518885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61400322138727027560345923 92100483208090541340518885)
        ·
          refine ⟨17268840601516976501347291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92100483208090541340518885 17268840601516976501347291)
          ·
            refine ⟨25903260902275464752020937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17268840601516976501347291 25903260902275464752020937)
            ·
              refine ⟨19427445676706598564015703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25903260902275464752020937 19427445676706598564015703)
              ·
                refine ⟨29141168515059897846023555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19427445676706598564015703 29141168515059897846023555)
                ·
                  refine ⟨43711752772589846769035333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29141168515059897846023555 43711752772589846769035333)
                  ·
                    refine ⟨8195953644860596269194125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43711752772589846769035333 8195953644860596269194125)
                    ·
                      refine ⟨3073482616822723600947797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8195953644860596269194125 3073482616822723600947797)
                      ·
                        rfl

theorem cell23_5985586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3].length) (baseStart_5985586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985586 prefixEnd_5985586 := by exact prefixLift 5985586
  have htrace : WordTrace (prefixWord ++ tailWord_5985586) baseStart_5985586 baseEnd_5985586 := by
    simpa [prefixWord, tailWord_5985586, baseEnd_5985586] using wordTrace_append hprefix tailTrace_5985586
  have hstable : (prefixWord ++ tailWord_5985586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985586).length < 2 ^ (prefixWord ++ tailWord_5985586).sum := by decide
  have hdescent : baseEnd_5985586 < baseStart_5985586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985589 : List Nat := [1, 3, 3, 1, 2, 2, 1, 2, 8]
def baseStart_5985589 : Nat := 118140960795 + 5985589 * 2 ^ 59
def prefixEnd_5985589 : Nat := 4983230072969 + 3 ^ 40 * 5985589 * 2
def baseEnd_5985589 : Nat := 341498239696076343245587

theorem tailTrace_5985589 : CollatzResearch.WordTrace tailWord_5985589 prefixEnd_5985589 341498239696076343245587 := by
  unfold tailWord_5985589
  simp only [CollatzResearch.WordTrace]
  refine ⟨218312365912240785060255821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145541577274827190040170547 218312365912240785060255821)
  ·
    refine ⟨81867137217090294397595933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218312365912240785060255821 81867137217090294397595933)
    ·
      refine ⟨30700176456408860399098475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81867137217090294397595933 30700176456408860399098475)
      ·
        refine ⟨46050264684613290598647713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30700176456408860399098475 46050264684613290598647713)
        ·
          refine ⟨34537698513459967948985785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46050264684613290598647713 34537698513459967948985785)
          ·
            refine ⟨25903273885094975961739339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34537698513459967948985785 25903273885094975961739339)
            ·
              refine ⟨38854910827642463942609009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25903273885094975961739339 38854910827642463942609009)
              ·
                refine ⟨29141183120731847956956757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38854910827642463942609009 29141183120731847956956757)
                ·
                  refine ⟨341498239696076343245587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29141183120731847956956757 341498239696076343245587)
                  ·
                    rfl

theorem cell23_5985589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 8].length) (baseStart_5985589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985589 prefixEnd_5985589 := by exact prefixLift 5985589
  have htrace : WordTrace (prefixWord ++ tailWord_5985589) baseStart_5985589 baseEnd_5985589 := by
    simpa [prefixWord, tailWord_5985589, baseEnd_5985589] using wordTrace_append hprefix tailTrace_5985589
  have hstable : (prefixWord ++ tailWord_5985589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985589).length < 2 ^ (prefixWord ++ tailWord_5985589).sum := by decide
  have hdescent : baseEnd_5985589 < baseStart_5985589 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985619 : List Nat := [1, 1, 1, 2, 1, 1, 6, 2, 3, 5]
def baseStart_5985619 : Nat := 118140960795 + 5985619 * 2 ^ 59
def prefixEnd_5985619 : Nat := 4983230072969 + 3 ^ 40 * 5985619 * 2
def baseEnd_5985619 : Nat := 1024499853894773990611715

theorem tailTrace_5985619 : CollatzResearch.WordTrace tailWord_5985619 prefixEnd_5985619 1024499853894773990611715 := by
  unfold tailWord_5985619
  simp only [CollatzResearch.WordTrace]
  refine ⟨218313460102132100183847911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145542306734754733455898607 218313460102132100183847911)
  ·
    refine ⟨327470190153198150275771867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218313460102132100183847911 327470190153198150275771867)
    ·
      refine ⟨491205285229797225413657801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327470190153198150275771867 491205285229797225413657801)
      ·
        refine ⟨368403963922347919060243351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 491205285229797225413657801 368403963922347919060243351)
        ·
          refine ⟨552605945883521878590365027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368403963922347919060243351 552605945883521878590365027)
          ·
            refine ⟨828908918825282817885547541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552605945883521878590365027 828908918825282817885547541)
            ·
              refine ⟨38855105569935132088385041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 828908918825282817885547541 38855105569935132088385041)
              ·
                refine ⟨29141329177451349066288781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38855105569935132088385041 29141329177451349066288781)
                ·
                  refine ⟨10927998441544255899858293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29141329177451349066288781 10927998441544255899858293)
                  ·
                    refine ⟨1024499853894773990611715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10927998441544255899858293 1024499853894773990611715)
                    ·
                      rfl

theorem cell23_5985619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3, 5].length) (baseStart_5985619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985619 prefixEnd_5985619 := by exact prefixLift 5985619
  have htrace : WordTrace (prefixWord ++ tailWord_5985619) baseStart_5985619 baseEnd_5985619 := by
    simpa [prefixWord, tailWord_5985619, baseEnd_5985619] using wordTrace_append hprefix tailTrace_5985619
  have hstable : (prefixWord ++ tailWord_5985619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985619).length < 2 ^ (prefixWord ++ tailWord_5985619).sum := by decide
  have hdescent : baseEnd_5985619 < baseStart_5985619 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985623 : List Nat := [1, 1, 3, 2, 3, 4, 2, 1, 6]
def baseStart_5985623 : Nat := 118140960795 + 5985623 * 2 ^ 59
def prefixEnd_5985623 : Nat := 4983230072969 + 3 ^ 40 * 5985623 * 2
def baseEnd_5985623 : Nat := 341500179511882217353903

theorem tailTrace_5985623 : CollatzResearch.WordTrace tailWord_5985623 prefixEnd_5985623 341500179511882217353903 := by
  unfold tailWord_5985623
  simp only [CollatzResearch.WordTrace]
  refine ⟨218313605994117608866993523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145542403996078405911329015 218313605994117608866993523)
  ·
    refine ⟨327470408991176413300490285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218313605994117608866993523 327470408991176413300490285)
    ·
      refine ⟨122801403371691154987683857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 327470408991176413300490285 122801403371691154987683857)
      ·
        refine ⟨92101052528768366240762893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122801403371691154987683857 92101052528768366240762893)
        ·
          refine ⟨34537894698288137340286085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92101052528768366240762893 34537894698288137340286085)
          ·
            refine ⟨6475855255929025751303641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34537894698288137340286085 6475855255929025751303641)
            ·
              refine ⟨4856891441946769313477731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6475855255929025751303641 4856891441946769313477731)
              ·
                refine ⟨7285337162920153970216597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4856891441946769313477731 7285337162920153970216597)
                ·
                  refine ⟨341500179511882217353903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7285337162920153970216597 341500179511882217353903)
                  ·
                    rfl

theorem cell23_5985623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 1, 6].length) (baseStart_5985623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985623 prefixEnd_5985623 := by exact prefixLift 5985623
  have htrace : WordTrace (prefixWord ++ tailWord_5985623) baseStart_5985623 baseEnd_5985623 := by
    simpa [prefixWord, tailWord_5985623, baseEnd_5985623] using wordTrace_append hprefix tailTrace_5985623
  have hstable : (prefixWord ++ tailWord_5985623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985623).length < 2 ^ (prefixWord ++ tailWord_5985623).sum := by decide
  have hdescent : baseEnd_5985623 < baseStart_5985623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985626 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 3, 5, 2]
def baseStart_5985626 : Nat := 118140960795 + 5985626 * 2 ^ 59
def prefixEnd_5985626 : Nat := 4983230072969 + 3 ^ 40 * 5985626 * 2
def baseEnd_5985626 : Nat := 3073503156048903444447613

theorem tailTrace_5985626 : CollatzResearch.WordTrace tailWord_5985626 prefixEnd_5985626 3073503156048903444447613 := by
  unfold tailWord_5985626
  simp only [CollatzResearch.WordTrace]
  refine ⟨54578428853276685094838183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145542476942071160252901821 54578428853276685094838183)
  ·
    refine ⟨81867643279915027642257275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54578428853276685094838183 81867643279915027642257275)
    ·
      refine ⟨122801464919872541463385913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81867643279915027642257275 122801464919872541463385913)
      ·
        refine ⟨92101098689904406097539435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122801464919872541463385913 92101098689904406097539435)
        ·
          refine ⟨138151648034856609146309153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92101098689904406097539435 138151648034856609146309153)
          ·
            refine ⟨103613736026142456859731865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138151648034856609146309153 103613736026142456859731865)
            ·
              refine ⟨77710302019606842644798899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103613736026142456859731865 77710302019606842644798899)
              ·
                refine ⟨116565453029410263967198349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77710302019606842644798899 116565453029410263967198349)
                ·
                  refine ⟨43712044886028848987699381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116565453029410263967198349 43712044886028848987699381)
                  ·
                    refine ⟨4098004208065204592596817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43712044886028848987699381 4098004208065204592596817)
                    ·
                      refine ⟨3073503156048903444447613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4098004208065204592596817 3073503156048903444447613)
                      ·
                        rfl

theorem cell23_5985626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 3, 5, 2].length) (baseStart_5985626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985626 prefixEnd_5985626 := by exact prefixLift 5985626
  have htrace : WordTrace (prefixWord ++ tailWord_5985626) baseStart_5985626 baseEnd_5985626 := by
    simpa [prefixWord, tailWord_5985626, baseEnd_5985626] using wordTrace_append hprefix tailTrace_5985626
  have hstable : (prefixWord ++ tailWord_5985626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985626).length < 2 ^ (prefixWord ++ tailWord_5985626).sum := by decide
  have hdescent : baseEnd_5985626 < baseStart_5985626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985636 : List Nat := [2, 3, 1, 1, 3, 3, 1, 1, 3, 5]
def baseStart_5985636 : Nat := 118140960795 + 5985636 * 2 ^ 59
def prefixEnd_5985636 : Nat := 4983230072969 + 3 ^ 40 * 5985636 * 2
def baseEnd_5985636 : Nat := 1024502763618482801774189

theorem tailTrace_5985636 : CollatzResearch.WordTrace tailWord_5985636 prefixEnd_5985636 1024502763618482801774189 := by
  unfold tailWord_5985636
  simp only [CollatzResearch.WordTrace]
  refine ⟨109157040071535256043608381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145542720095380341391477841 109157040071535256043608381)
  ·
    refine ⟨40933890026825721016353143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109157040071535256043608381 40933890026825721016353143)
    ·
      refine ⟨61400835040238581524529715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40933890026825721016353143 61400835040238581524529715)
      ·
        refine ⟨92101252560357872286794573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61400835040238581524529715 92101252560357872286794573)
        ·
          refine ⟨34537969710134202107547965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92101252560357872286794573 34537969710134202107547965)
          ·
            refine ⟨12951738641300325790330487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34537969710134202107547965 12951738641300325790330487)
            ·
              refine ⟨19427607961950488685495731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12951738641300325790330487 19427607961950488685495731)
              ·
                refine ⟨29141411942925733028243597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19427607961950488685495731 29141411942925733028243597)
                ·
                  refine ⟨10928029478597149885591349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29141411942925733028243597 10928029478597149885591349)
                  ·
                    refine ⟨1024502763618482801774189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10928029478597149885591349 1024502763618482801774189)
                    ·
                      rfl

theorem cell23_5985636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_5985636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985636 prefixEnd_5985636 := by exact prefixLift 5985636
  have htrace : WordTrace (prefixWord ++ tailWord_5985636) baseStart_5985636 baseEnd_5985636 := by
    simpa [prefixWord, tailWord_5985636, baseEnd_5985636] using wordTrace_append hprefix tailTrace_5985636
  have hstable : (prefixWord ++ tailWord_5985636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985636).length < 2 ^ (prefixWord ++ tailWord_5985636).sum := by decide
  have hdescent : baseEnd_5985636 < baseStart_5985636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985649 : List Nat := [1, 2, 2, 2, 1, 2, 3, 1, 3, 6]
def baseStart_5985649 : Nat := 118140960795 + 5985649 * 2 ^ 59
def prefixEnd_5985649 : Nat := 4983230072969 + 3 ^ 40 * 5985649 * 2
def baseEnd_5985649 : Nat := 1024504988701318951486669

theorem tailTrace_5985649 : CollatzResearch.WordTrace tailWord_5985649 prefixEnd_5985649 1024504988701318951486669 := by
  unfold tailWord_5985649
  simp only [CollatzResearch.WordTrace]
  refine ⟨218314554292023415307440001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145543036194682276871626667 218314554292023415307440001)
  ·
    refine ⟨163735915719017561480580001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218314554292023415307440001 163735915719017561480580001)
    ·
      refine ⟨122801936789263171110435001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163735915719017561480580001 122801936789263171110435001)
      ·
        refine ⟨92101452591947378332826251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122801936789263171110435001 92101452591947378332826251)
        ·
          refine ⟨138152178887921067499239377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92101452591947378332826251 138152178887921067499239377)
          ·
            refine ⟨103614134165940800624429533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138152178887921067499239377 103614134165940800624429533)
            ·
              refine ⟨38855300312227800234161075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103614134165940800624429533 38855300312227800234161075)
              ·
                refine ⟨58282950468341700351241613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38855300312227800234161075 58282950468341700351241613)
                ·
                  refine ⟨21856106425628137631715605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58282950468341700351241613 21856106425628137631715605)
                  ·
                    refine ⟨1024504988701318951486669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21856106425628137631715605 1024504988701318951486669)
                    ·
                      rfl

theorem cell23_5985649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 6].length) (baseStart_5985649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985649 prefixEnd_5985649 := by exact prefixLift 5985649
  have htrace : WordTrace (prefixWord ++ tailWord_5985649) baseStart_5985649 baseEnd_5985649 := by
    simpa [prefixWord, tailWord_5985649, baseEnd_5985649] using wordTrace_append hprefix tailTrace_5985649
  have hstable : (prefixWord ++ tailWord_5985649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985649).length < 2 ^ (prefixWord ++ tailWord_5985649).sum := by decide
  have hdescent : baseEnd_5985649 < baseStart_5985649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985650 : List Nat := [3, 2, 1, 2, 1, 2, 2, 5, 1, 1, 3]
def baseStart_5985650 : Nat := 118140960795 + 5985650 * 2 ^ 59
def prefixEnd_5985650 : Nat := 4983230072969 + 3 ^ 40 * 5985650 * 2
def baseEnd_5985650 : Nat := 3073515479584611350547503

theorem tailTrace_5985650 : CollatzResearch.WordTrace tailWord_5985650 prefixEnd_5985650 3073515479584611350547503 := by
  unfold tailWord_5985650
  simp only [CollatzResearch.WordTrace]
  refine ⟨54578647691254948119556601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145543060510013194985484269 54578647691254948119556601)
  ·
    refine ⟨40933985768441211089667451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54578647691254948119556601 40933985768441211089667451)
    ·
      refine ⟨61400978652661816634501177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40933985768441211089667451 61400978652661816634501177)
      ·
        refine ⟨46050733989496362475875883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61400978652661816634501177 46050733989496362475875883)
        ·
          refine ⟨69076100984244543713813825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46050733989496362475875883 69076100984244543713813825)
          ·
            refine ⟨51807075738183407785360369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69076100984244543713813825 51807075738183407785360369)
            ·
              refine ⟨38855306803637555839020277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51807075738183407785360369 38855306803637555839020277)
              ·
                refine ⟨3642685012841020859908151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38855306803637555839020277 3642685012841020859908151)
                ·
                  refine ⟨5464027519261531289862227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3642685012841020859908151 5464027519261531289862227)
                  ·
                    refine ⟨8196041278892296934793341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5464027519261531289862227 8196041278892296934793341)
                    ·
                      refine ⟨3073515479584611350547503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8196041278892296934793341 3073515479584611350547503)
                      ·
                        rfl

theorem cell23_5985650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 5, 1, 1, 3].length) (baseStart_5985650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985650 prefixEnd_5985650 := by exact prefixLift 5985650
  have htrace : WordTrace (prefixWord ++ tailWord_5985650) baseStart_5985650 baseEnd_5985650 := by
    simpa [prefixWord, tailWord_5985650, baseEnd_5985650] using wordTrace_append hprefix tailTrace_5985650
  have hstable : (prefixWord ++ tailWord_5985650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985650).length < 2 ^ (prefixWord ++ tailWord_5985650).sum := by decide
  have hdescent : baseEnd_5985650 < baseStart_5985650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985667 : List Nat := [1, 1, 1, 3, 5, 1, 4, 2, 1, 1, 3]
def baseStart_5985667 : Nat := 118140960795 + 5985667 * 2 ^ 59
def prefixEnd_5985667 : Nat := 4983230072969 + 3 ^ 40 * 5985667 * 2
def baseEnd_5985667 : Nat := 3073524208755737784034925

theorem tailTrace_5985667 : CollatzResearch.WordTrace tailWord_5985667 prefixEnd_5985667 3073524208755737784034925 := by
  unfold tailWord_5985667
  simp only [CollatzResearch.WordTrace]
  refine ⟨218315210805958204381595255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145543473870638802921063503 218315210805958204381595255)
  ·
    refine ⟨327472816208937306572392883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218315210805958204381595255 327472816208937306572392883)
    ·
      refine ⟨491209224313405959858589325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327472816208937306572392883 491209224313405959858589325)
      ·
        refine ⟨184203459117527234946970997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 491209224313405959858589325 184203459117527234946970997)
        ·
          refine ⟨17269074292268178276278531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 184203459117527234946970997 17269074292268178276278531)
          ·
            refine ⟨25903611438402267414417797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17269074292268178276278531 25903611438402267414417797)
            ·
              refine ⟨4856927144700425140203337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25903611438402267414417797 4856927144700425140203337)
              ·
                refine ⟨3642695358525318855152503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4856927144700425140203337 3642695358525318855152503)
                ·
                  refine ⟨5464043037787978282728755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3642695358525318855152503 5464043037787978282728755)
                  ·
                    refine ⟨8196064556681967424093133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5464043037787978282728755 8196064556681967424093133)
                    ·
                      refine ⟨3073524208755737784034925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8196064556681967424093133 3073524208755737784034925)
                      ·
                        rfl

theorem cell23_5985667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 2, 1, 1, 3].length) (baseStart_5985667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985667 prefixEnd_5985667 := by exact prefixLift 5985667
  have htrace : WordTrace (prefixWord ++ tailWord_5985667) baseStart_5985667 baseEnd_5985667 := by
    simpa [prefixWord, tailWord_5985667, baseEnd_5985667] using wordTrace_append hprefix tailTrace_5985667
  have hstable : (prefixWord ++ tailWord_5985667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985667).length < 2 ^ (prefixWord ++ tailWord_5985667).sum := by decide
  have hdescent : baseEnd_5985667 < baseStart_5985667 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985669 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 3, 1, 6]
def baseStart_5985669 : Nat := 118140960795 + 5985669 * 2 ^ 59
def prefixEnd_5985669 : Nat := 4983230072969 + 3 ^ 40 * 5985669 * 2
def baseEnd_5985669 : Nat := 3073525235717046776209915

theorem tailTrace_5985669 : CollatzResearch.WordTrace tailWord_5985669 prefixEnd_5985669 3073525235717046776209915 := by
  unfold tailWord_5985669
  simp only [CollatzResearch.WordTrace]
  refine ⟨218315283751950958723168061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145543522501300639148778707 218315283751950958723168061)
  ·
    refine ⟨81868231406981609521188023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218315283751950958723168061 81868231406981609521188023)
    ·
      refine ⟨122802347110472414281782035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81868231406981609521188023 122802347110472414281782035)
      ·
        refine ⟨184203520665708621422673053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122802347110472414281782035 184203520665708621422673053)
        ·
          refine ⟨69076320249640733033502395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184203520665708621422673053 69076320249640733033502395)
          ·
            refine ⟨103614480374461099550253593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69076320249640733033502395 103614480374461099550253593)
            ·
              refine ⟨77710860280845824662690195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103614480374461099550253593 77710860280845824662690195)
              ·
                refine ⟨116566290421268736994035293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77710860280845824662690195 116566290421268736994035293)
                ·
                  refine ⟨43712358907975776372763235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116566290421268736994035293 43712358907975776372763235)
                  ·
                    refine ⟨65568538361963664559144853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43712358907975776372763235 65568538361963664559144853)
                    ·
                      refine ⟨3073525235717046776209915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65568538361963664559144853 3073525235717046776209915)
                      ·
                        rfl

theorem cell23_5985669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_5985669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985669 prefixEnd_5985669 := by exact prefixLift 5985669
  have htrace : WordTrace (prefixWord ++ tailWord_5985669) baseStart_5985669 baseEnd_5985669 := by
    simpa [prefixWord, tailWord_5985669, baseEnd_5985669] using wordTrace_append hprefix tailTrace_5985669
  have hstable : (prefixWord ++ tailWord_5985669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985669).length < 2 ^ (prefixWord ++ tailWord_5985669).sum := by decide
  have hdescent : baseEnd_5985669 < baseStart_5985669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985676 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 5, 2, 3]
def baseStart_5985676 : Nat := 118140960795 + 5985676 * 2 ^ 59
def prefixEnd_5985676 : Nat := 4983230072969 + 3 ^ 40 * 5985676 * 2
def baseEnd_5985676 : Nat := 3073528830081628248822383

theorem tailTrace_5985676 : CollatzResearch.WordTrace tailWord_5985676 prefixEnd_5985676 3073528830081628248822383 := by
  unfold tailWord_5985676
  simp only [CollatzResearch.WordTrace]
  refine ⟨109157769531462799459336441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145543692708617065945781921 109157769531462799459336441)
  ·
    refine ⟨81868327148597099594502331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109157769531462799459336441 81868327148597099594502331)
    ·
      refine ⟨122802490722895649391753497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81868327148597099594502331 122802490722895649391753497)
      ·
        refine ⟨92101868042171737043815123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122802490722895649391753497 92101868042171737043815123)
        ·
          refine ⟨138152802063257605565722685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92101868042171737043815123 138152802063257605565722685)
          ·
            refine ⟨51807300773721602087146007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138152802063257605565722685 51807300773721602087146007)
            ·
              refine ⟨77710951160582403130719011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51807300773721602087146007 77710951160582403130719011)
              ·
                refine ⟨116566426740873604696078517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77710951160582403130719011 116566426740873604696078517)
                ·
                  refine ⟨10928102506956900440257361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 116566426740873604696078517 10928102506956900440257361)
                  ·
                    refine ⟨8196076880217675330193021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10928102506956900440257361 8196076880217675330193021)
                    ·
                      refine ⟨3073528830081628248822383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8196076880217675330193021 3073528830081628248822383)
                      ·
                        rfl

theorem cell23_5985676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 5, 2, 3].length) (baseStart_5985676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985676 prefixEnd_5985676 := by exact prefixLift 5985676
  have htrace : WordTrace (prefixWord ++ tailWord_5985676) baseStart_5985676 baseEnd_5985676 := by
    simpa [prefixWord, tailWord_5985676, baseEnd_5985676] using wordTrace_append hprefix tailTrace_5985676
  have hstable : (prefixWord ++ tailWord_5985676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985676).length < 2 ^ (prefixWord ++ tailWord_5985676).sum := by decide
  have hdescent : baseEnd_5985676 < baseStart_5985676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985690 : List Nat := [3, 1, 1, 4, 1, 1, 3, 2, 3, 2, 2]
def baseStart_5985690 : Nat := 118140960795 + 5985690 * 2 ^ 59
def prefixEnd_5985690 : Nat := 4983230072969 + 3 ^ 40 * 5985690 * 2
def baseEnd_5985690 : Nat := 3073536018810791194047319

theorem tailTrace_5985690 : CollatzResearch.WordTrace tailWord_5985690 prefixEnd_5985690 3073536018810791194047319 := by
  unfold tailWord_5985690
  simp only [CollatzResearch.WordTrace]
  refine ⟨54579012421218719827420631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145544033123249919539788349 54579012421218719827420631)
  ·
    refine ⟨81868518631828079741130947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54579012421218719827420631 81868518631828079741130947)
    ·
      refine ⟨122802777947742119611696421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81868518631828079741130947 122802777947742119611696421)
      ·
        refine ⟨23025520865201647427193079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122802777947742119611696421 23025520865201647427193079)
        ·
          refine ⟨34538281297802471140789619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23025520865201647427193079 34538281297802471140789619)
          ·
            refine ⟨51807421946703706711184429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34538281297802471140789619 51807421946703706711184429)
            ·
              refine ⟨19427783230013890016694161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51807421946703706711184429 19427783230013890016694161)
              ·
                refine ⟨14570837422510417512520621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19427783230013890016694161 14570837422510417512520621)
                ·
                  refine ⟨5464064033441406567195233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14570837422510417512520621 5464064033441406567195233)
                  ·
                    refine ⟨4098048025081054925396425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5464064033441406567195233 4098048025081054925396425)
                    ·
                      refine ⟨3073536018810791194047319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4098048025081054925396425 3073536018810791194047319)
                      ·
                        rfl

theorem cell23_5985690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_5985690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985690 prefixEnd_5985690 := by exact prefixLift 5985690
  have htrace : WordTrace (prefixWord ++ tailWord_5985690) baseStart_5985690 baseEnd_5985690 := by
    simpa [prefixWord, tailWord_5985690, baseEnd_5985690] using wordTrace_append hprefix tailTrace_5985690
  have hstable : (prefixWord ++ tailWord_5985690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985690).length < 2 ^ (prefixWord ++ tailWord_5985690).sum := by decide
  have hdescent : baseEnd_5985690 < baseStart_5985690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985693 : List Nat := [1, 4, 2, 1, 3, 1, 2, 1, 3, 2, 3]
def baseStart_5985693 : Nat := 118140960795 + 5985693 * 2 ^ 59
def prefixEnd_5985693 : Nat := 4983230072969 + 3 ^ 40 * 5985693 * 2
def baseEnd_5985693 : Nat := 3073537559252754682309805

theorem tailTrace_5985693 : CollatzResearch.WordTrace tailWord_5985693 prefixEnd_5985693 3073537559252754682309805 := by
  unfold tailWord_5985693
  simp only [CollatzResearch.WordTrace]
  refine ⟨218316159103864010822041733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145544106069242673881361155 218316159103864010822041733)
  ·
    refine ⟨40934279831974502029132825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 218316159103864010822041733 40934279831974502029132825)
    ·
      refine ⟨30700709873980876521849619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40934279831974502029132825 30700709873980876521849619)
      ·
        refine ⟨46051064810971314782774429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30700709873980876521849619 46051064810971314782774429)
        ·
          refine ⟨17269149304114243043540411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46051064810971314782774429 17269149304114243043540411)
          ·
            refine ⟨25903723956171364565310617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17269149304114243043540411 25903723956171364565310617)
            ·
              refine ⟨19427792967128523423982963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25903723956171364565310617 19427792967128523423982963)
              ·
                refine ⟨29141689450692785135974445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19427792967128523423982963 29141689450692785135974445)
                ·
                  refine ⟨10928133544009794425990417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29141689450692785135974445 10928133544009794425990417)
                  ·
                    refine ⟨8196100158007345819492813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10928133544009794425990417 8196100158007345819492813)
                    ·
                      refine ⟨3073537559252754682309805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8196100158007345819492813 3073537559252754682309805)
                      ·
                        rfl

theorem cell23_5985693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_5985693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985693 prefixEnd_5985693 := by exact prefixLift 5985693
  have htrace : WordTrace (prefixWord ++ tailWord_5985693) baseStart_5985693 baseEnd_5985693 := by
    simpa [prefixWord, tailWord_5985693, baseEnd_5985693] using wordTrace_append hprefix tailTrace_5985693
  have hstable : (prefixWord ++ tailWord_5985693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985693).length < 2 ^ (prefixWord ++ tailWord_5985693).sum := by decide
  have hdescent : baseEnd_5985693 < baseStart_5985693 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985694 : List Nat := [4, 3, 1, 2, 2, 2, 1, 1, 2, 3, 2]
def baseStart_5985694 : Nat := 118140960795 + 5985694 * 2 ^ 59
def prefixEnd_5985694 : Nat := 4983230072969 + 3 ^ 40 * 5985694 * 2
def baseEnd_5985694 : Nat := 3073538072733409178397301

theorem tailTrace_5985694 : CollatzResearch.WordTrace tailWord_5985694 prefixEnd_5985694 3073538072733409178397301 := by
  unfold tailWord_5985694
  simp only [CollatzResearch.WordTrace]
  refine ⟨27289524447107548499103517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145544130384573591995218757 27289524447107548499103517)
  ·
    refine ⟨10233571667665330687163819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27289524447107548499103517 10233571667665330687163819)
    ·
      refine ⟨15350357501497996030745729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10233571667665330687163819 15350357501497996030745729)
      ·
        refine ⟨11512768126123497023059297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15350357501497996030745729 11512768126123497023059297)
        ·
          refine ⟨8634576094592622767294473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11512768126123497023059297 8634576094592622767294473)
          ·
            refine ⟨6475932070944467075470855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8634576094592622767294473 6475932070944467075470855)
            ·
              refine ⟨9713898106416700613206283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6475932070944467075470855 9713898106416700613206283)
              ·
                refine ⟨14570847159625050919809425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9713898106416700613206283 14570847159625050919809425)
                ·
                  refine ⟨10928135369718788189857069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14570847159625050919809425 10928135369718788189857069)
                  ·
                    refine ⟨4098050763644545571196401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10928135369718788189857069 4098050763644545571196401)
                    ·
                      refine ⟨3073538072733409178397301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4098050763644545571196401 3073538072733409178397301)
                      ·
                        rfl

theorem cell23_5985694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_5985694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985694 prefixEnd_5985694 := by exact prefixLift 5985694
  have htrace : WordTrace (prefixWord ++ tailWord_5985694) baseStart_5985694 baseEnd_5985694 := by
    simpa [prefixWord, tailWord_5985694, baseEnd_5985694] using wordTrace_append hprefix tailTrace_5985694
  have hstable : (prefixWord ++ tailWord_5985694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985694).length < 2 ^ (prefixWord ++ tailWord_5985694).sum := by decide
  have hdescent : baseEnd_5985694 < baseStart_5985694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985696 : List Nat := [2, 1, 1, 4, 1, 2, 5, 7]
def baseStart_5985696 : Nat := 118140960795 + 5985696 * 2 ^ 59
def prefixEnd_5985696 : Nat := 4983230072969 + 3 ^ 40 * 5985696 * 2
def baseEnd_5985696 : Nat := 113834781470174747058233

theorem tailTrace_5985696 : CollatzResearch.WordTrace tailWord_5985696 prefixEnd_5985696 113834781470174747058233 := by
  unfold tailWord_5985696
  simp only [CollatzResearch.WordTrace]
  refine ⟨109158134261426571167200471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145544179015235428222933961 109158134261426571167200471)
  ·
    refine ⟨163737201392139856750800707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109158134261426571167200471 163737201392139856750800707)
    ·
      refine ⟨245605802088209785126201061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163737201392139856750800707 245605802088209785126201061)
      ·
        refine ⟨46051087891539334711162699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 245605802088209785126201061 46051087891539334711162699)
        ·
          refine ⟨69076631837309002066744049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46051087891539334711162699 69076631837309002066744049)
          ·
            refine ⟨51807473877981751550058037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69076631837309002066744049 51807473877981751550058037)
            ·
              refine ⟨4856950676060789207817941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51807473877981751550058037 4856950676060789207817941)
              ·
                refine ⟨113834781470174747058233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4856950676060789207817941 113834781470174747058233)
                ·
                  rfl

theorem cell23_5985696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 7].length) (baseStart_5985696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985696 prefixEnd_5985696 := by exact prefixLift 5985696
  have htrace : WordTrace (prefixWord ++ tailWord_5985696) baseStart_5985696 baseEnd_5985696 := by
    simpa [prefixWord, tailWord_5985696, baseEnd_5985696] using wordTrace_append hprefix tailTrace_5985696
  have hstable : (prefixWord ++ tailWord_5985696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985696).length < 2 ^ (prefixWord ++ tailWord_5985696).sum := by decide
  have hdescent : baseEnd_5985696 < baseStart_5985696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985704 : List Nat := [2, 1, 6, 1, 3, 1, 2, 1, 1, 5]
def baseStart_5985704 : Nat := 118140960795 + 5985704 * 2 ^ 59
def prefixEnd_5985704 : Nat := 4983230072969 + 3 ^ 40 * 5985704 * 2
def baseEnd_5985704 : Nat := 1024514402513318046424085

theorem tailTrace_5985704 : CollatzResearch.WordTrace tailWord_5985704 prefixEnd_5985704 1024514402513318046424085 := by
  unfold tailWord_5985704
  simp only [CollatzResearch.WordTrace]
  refine ⟨109158280153412079850346083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145544373537882773133794777 109158280153412079850346083)
  ·
    refine ⟨163737420230118119775519125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109158280153412079850346083 163737420230118119775519125)
    ·
      refine ⟨7675191573286786864477459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 163737420230118119775519125 7675191573286786864477459)
      ·
        refine ⟨11512787359930180296716189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7675191573286786864477459 11512787359930180296716189)
        ·
          refine ⟨4317295259973817611268571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11512787359930180296716189 4317295259973817611268571)
          ·
            refine ⟨6475942889960726416902857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4317295259973817611268571 6475942889960726416902857)
            ·
              refine ⟨4856957167470544812677143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6475942889960726416902857 4856957167470544812677143)
              ·
                refine ⟨7285435751205817219015715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4856957167470544812677143 7285435751205817219015715)
                ·
                  refine ⟨10928153626808725828523573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7285435751205817219015715 10928153626808725828523573)
                  ·
                    refine ⟨1024514402513318046424085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10928153626808725828523573 1024514402513318046424085)
                    ·
                      rfl

theorem cell23_5985704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_5985704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985704 prefixEnd_5985704 := by exact prefixLift 5985704
  have htrace : WordTrace (prefixWord ++ tailWord_5985704) baseStart_5985704 baseEnd_5985704 := by
    simpa [prefixWord, tailWord_5985704, baseEnd_5985704] using wordTrace_append hprefix tailTrace_5985704
  have hstable : (prefixWord ++ tailWord_5985704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985704).length < 2 ^ (prefixWord ++ tailWord_5985704).sum := by decide
  have hdescent : baseEnd_5985704 < baseStart_5985704 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985740 : List Nat := [2, 2, 1, 4, 2, 3, 1, 1, 1, 3, 3]
def baseStart_5985740 : Nat := 118140960795 + 5985740 * 2 ^ 59
def prefixEnd_5985740 : Nat := 4983230072969 + 3 ^ 40 * 5985740 * 2
def baseEnd_5985740 : Nat := 3073561692843515998422089

theorem tailTrace_5985740 : CollatzResearch.WordTrace tailWord_5985740 prefixEnd_5985740 3073561692843515998422089 := by
  unfold tailWord_5985740
  simp only [CollatzResearch.WordTrace]
  refine ⟨109158936667346868924501337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145545248889795825232668449 109158936667346868924501337)
  ·
    refine ⟨81869202500510151693376003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109158936667346868924501337 81869202500510151693376003)
    ·
      refine ⟨122803803750765227540064005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81869202500510151693376003 122803803750765227540064005)
      ·
        refine ⟨23025713203268480163762001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122803803750765227540064005 23025713203268480163762001)
        ·
          refine ⟨17269284902451360122821501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23025713203268480163762001 17269284902451360122821501)
          ·
            refine ⟨6475981838419260046058063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17269284902451360122821501 6475981838419260046058063)
            ·
              refine ⟨9713972757628890069087095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6475981838419260046058063 9713972757628890069087095)
              ·
                refine ⟨14570959136443335103630643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9713972757628890069087095 14570959136443335103630643)
                ·
                  refine ⟨21856438704665002655445965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14570959136443335103630643 21856438704665002655445965)
                  ·
                    refine ⟨8196164514249375995792237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21856438704665002655445965 8196164514249375995792237)
                    ·
                      refine ⟨3073561692843515998422089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8196164514249375995792237 3073561692843515998422089)
                      ·
                        rfl

theorem cell23_5985740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_5985740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985740 prefixEnd_5985740 := by exact prefixLift 5985740
  have htrace : WordTrace (prefixWord ++ tailWord_5985740) baseStart_5985740 baseEnd_5985740 := by
    simpa [prefixWord, tailWord_5985740, baseEnd_5985740] using wordTrace_append hprefix tailTrace_5985740
  have hstable : (prefixWord ++ tailWord_5985740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985740).length < 2 ^ (prefixWord ++ tailWord_5985740).sum := by decide
  have hdescent : baseEnd_5985740 < baseStart_5985740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985836 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 4]
def baseStart_5985836 : Nat := 118140960795 + 5985836 * 2 ^ 59
def prefixEnd_5985836 : Nat := 4983230072969 + 3 ^ 40 * 5985836 * 2
def baseEnd_5985836 : Nat := 3073610986986347622821647

theorem tailTrace_5985836 : CollatzResearch.WordTrace tailWord_5985836 prefixEnd_5985836 3073610986986347622821647 := by
  unfold tailWord_5985836
  simp only [CollatzResearch.WordTrace]
  refine ⟨109160687371172973122248681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145547583161563964162998241 109160687371172973122248681)
  ·
    refine ⟨81870515528379729841686511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109160687371172973122248681 81870515528379729841686511)
    ·
      refine ⟨122805773292569594762529767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81870515528379729841686511 122805773292569594762529767)
      ·
        refine ⟨184208659938854392143794651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122805773292569594762529767 184208659938854392143794651)
        ·
          refine ⟨276312989908281588215691977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184208659938854392143794651 276312989908281588215691977)
          ·
            refine ⟨207234742431211191161768983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276312989908281588215691977 207234742431211191161768983)
            ·
              refine ⟨310852113646816786742653475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207234742431211191161768983 310852113646816786742653475)
              ·
                refine ⟨466278170470225180113980213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 310852113646816786742653475 466278170470225180113980213)
                ·
                  refine ⟨43713578481583610635685645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 466278170470225180113980213 43713578481583610635685645)
                  ·
                    refine ⟨16392591930593853988382117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43713578481583610635685645 16392591930593853988382117)
                    ·
                      refine ⟨3073610986986347622821647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16392591930593853988382117 3073610986986347622821647)
                      ·
                        rfl

theorem cell23_5985836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 4].length) (baseStart_5985836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985836 prefixEnd_5985836 := by exact prefixLift 5985836
  have htrace : WordTrace (prefixWord ++ tailWord_5985836) baseStart_5985836 baseEnd_5985836 := by
    simpa [prefixWord, tailWord_5985836, baseEnd_5985836] using wordTrace_append hprefix tailTrace_5985836
  have hstable : (prefixWord ++ tailWord_5985836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985836).length < 2 ^ (prefixWord ++ tailWord_5985836).sum := by decide
  have hdescent : baseEnd_5985836 < baseStart_5985836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985873 : List Nat := [1, 2, 2, 1, 3, 2, 3, 1, 1, 4, 3]
def baseStart_5985873 : Nat := 118140960795 + 5985873 * 2 ^ 59
def prefixEnd_5985873 : Nat := 4983230072969 + 3 ^ 40 * 5985873 * 2
def baseEnd_5985873 : Nat := 3073629985770563978058977

theorem tailTrace_5985873 : CollatzResearch.WordTrace tailWord_5985873 prefixEnd_5985873 3073629985770563978058977 := by
  unfold tailWord_5985873
  simp only [CollatzResearch.WordTrace]
  refine ⟨218322724243211901563594273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145548482828807934375729515 218322724243211901563594273)
  ·
    refine ⟨163742043182408926172695705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218322724243211901563594273 163742043182408926172695705)
    ·
      refine ⟨122806532386806694629521779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163742043182408926172695705 122806532386806694629521779)
      ·
        refine ⟨184209798580210041944282669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122806532386806694629521779 184209798580210041944282669)
        ·
          refine ⟨69078674467578765729106001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184209798580210041944282669 69078674467578765729106001)
          ·
            refine ⟨51809005850684074296829501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69078674467578765729106001 51809005850684074296829501)
            ·
              refine ⟨19428377194006527861311063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51809005850684074296829501 19428377194006527861311063)
              ·
                refine ⟨29142565791009791791966595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19428377194006527861311063 29142565791009791791966595)
                ·
                  refine ⟨43713848686514687687949893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29142565791009791791966595 43713848686514687687949893)
                  ·
                    refine ⟨8196346628721503941490605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43713848686514687687949893 8196346628721503941490605)
                    ·
                      refine ⟨3073629985770563978058977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8196346628721503941490605 3073629985770563978058977)
                      ·
                        rfl

theorem cell23_5985873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 4, 3].length) (baseStart_5985873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985873 prefixEnd_5985873 := by exact prefixLift 5985873
  have htrace : WordTrace (prefixWord ++ tailWord_5985873) baseStart_5985873 baseEnd_5985873 := by
    simpa [prefixWord, tailWord_5985873, baseEnd_5985873] using wordTrace_append hprefix tailTrace_5985873
  have hstable : (prefixWord ++ tailWord_5985873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985873).length < 2 ^ (prefixWord ++ tailWord_5985873).sum := by decide
  have hdescent : baseEnd_5985873 < baseStart_5985873 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985893 : List Nat := [1, 3, 1, 3, 3, 2, 1, 1, 8]
def baseStart_5985893 : Nat := 118140960795 + 5985893 * 2 ^ 59
def prefixEnd_5985893 : Nat := 4983230072969 + 3 ^ 40 * 5985893 * 2
def baseEnd_5985893 : Nat := 341515583931517099978765

theorem tailTrace_5985893 : CollatzResearch.WordTrace tailWord_5985893 prefixEnd_5985893 341515583931517099978765 := by
  unfold tailWord_5985893
  simp only [CollatzResearch.WordTrace]
  refine ⟨218323453703139444979322333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145548969135426296652881555 218323453703139444979322333)
  ·
    refine ⟨81871295138677291867245875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218323453703139444979322333 81871295138677291867245875)
    ·
      refine ⟨122806942708015937800868813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81871295138677291867245875 122806942708015937800868813)
      ·
        refine ⟨46052603515505976675325805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122806942708015937800868813 46052603515505976675325805)
        ·
          refine ⟨17269726318314741253247177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46052603515505976675325805 17269726318314741253247177)
          ·
            refine ⟨12952294738736055939935383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17269726318314741253247177 12952294738736055939935383)
            ·
              refine ⟨19428442108104083909903075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12952294738736055939935383 19428442108104083909903075)
              ·
                refine ⟨29142663162156125864854613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19428442108104083909903075 29142663162156125864854613)
                ·
                  refine ⟨341515583931517099978765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29142663162156125864854613 341515583931517099978765)
                  ·
                    rfl

theorem cell23_5985893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 8].length) (baseStart_5985893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985893 prefixEnd_5985893 := by exact prefixLift 5985893
  have htrace : WordTrace (prefixWord ++ tailWord_5985893) baseStart_5985893 baseEnd_5985893 := by
    simpa [prefixWord, tailWord_5985893, baseEnd_5985893] using wordTrace_append hprefix tailTrace_5985893
  have hstable : (prefixWord ++ tailWord_5985893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985893).length < 2 ^ (prefixWord ++ tailWord_5985893).sum := by decide
  have hdescent : baseEnd_5985893 < baseStart_5985893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985920 : List Nat := [2, 1, 1, 2, 1, 4, 1, 4, 3, 1, 3]
def baseStart_5985920 : Nat := 118140960795 + 5985920 * 2 ^ 59
def prefixEnd_5985920 : Nat := 4983230072969 + 3 ^ 40 * 5985920 * 2
def baseEnd_5985920 : Nat := 3073654119361325294171261

theorem tailTrace_5985920 : CollatzResearch.WordTrace tailWord_5985920 prefixEnd_5985920 3073654119361325294171261 := by
  unfold tailWord_5985920
  simp only [CollatzResearch.WordTrace]
  refine ⟨109162219237020814295277607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145549625649361085727036809 109162219237020814295277607)
  ·
    refine ⟨163743328855531221442916411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109162219237020814295277607 163743328855531221442916411)
    ·
      refine ⟨245614993283296832164374617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163743328855531221442916411 245614993283296832164374617)
      ·
        refine ⟨184211244962472624123280963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245614993283296832164374617 184211244962472624123280963)
        ·
          refine ⟨276316867443708936184921445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184211244962472624123280963 276316867443708936184921445)
          ·
            refine ⟨51809412645695425534672771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 276316867443708936184921445 51809412645695425534672771)
            ·
              refine ⟨77714118968543138302009157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51809412645695425534672771 77714118968543138302009157)
              ·
                refine ⟨14571397306601838431626717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77714118968543138302009157 14571397306601838431626717)
                ·
                  refine ⟨5464273989975689411860019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14571397306601838431626717 5464273989975689411860019)
                  ·
                    refine ⟨8196410984963534117790029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5464273989975689411860019 8196410984963534117790029)
                    ·
                      refine ⟨3073654119361325294171261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8196410984963534117790029 3073654119361325294171261)
                      ·
                        rfl

theorem cell23_5985920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 3, 1, 3].length) (baseStart_5985920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985920 prefixEnd_5985920 := by exact prefixLift 5985920
  have htrace : WordTrace (prefixWord ++ tailWord_5985920) baseStart_5985920 baseEnd_5985920 := by
    simpa [prefixWord, tailWord_5985920, baseEnd_5985920] using wordTrace_append hprefix tailTrace_5985920
  have hstable : (prefixWord ++ tailWord_5985920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985920).length < 2 ^ (prefixWord ++ tailWord_5985920).sum := by decide
  have hdescent : baseEnd_5985920 < baseStart_5985920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985937 : List Nat := [1, 2, 2, 1, 1, 1, 1, 9, 1, 1, 3]
def baseStart_5985937 : Nat := 118140960795 + 5985937 * 2 ^ 59
def prefixEnd_5985937 : Nat := 4983230072969 + 3 ^ 40 * 5985937 * 2
def baseEnd_5985937 : Nat := 3073662848532451727658683

theorem tailTrace_5985937 : CollatzResearch.WordTrace tailWord_5985937 prefixEnd_5985937 3073662848532451727658683 := by
  unfold tailWord_5985937
  simp only [CollatzResearch.WordTrace]
  refine ⟨218325058514980040493924065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145550039009986693662616043 218325058514980040493924065)
  ·
    refine ⟨163743793886235030370443049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218325058514980040493924065 163743793886235030370443049)
    ·
      refine ⟨122807845414676272777832287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163743793886235030370443049 122807845414676272777832287)
      ·
        refine ⟨184211768122014409166748431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122807845414676272777832287 184211768122014409166748431)
        ·
          refine ⟨276317652183021613750122647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184211768122014409166748431 276317652183021613750122647)
          ·
            refine ⟨414476478274532420625183971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276317652183021613750122647 414476478274532420625183971)
            ·
              refine ⟨621714717411798630937775957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414476478274532420625183971 621714717411798630937775957)
              ·
                refine ⟨3642859672334757603151031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 621714717411798630937775957 3642859672334757603151031)
                ·
                  refine ⟨5464289508502136404726547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3642859672334757603151031 5464289508502136404726547)
                  ·
                    refine ⟨8196434262753204607089821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5464289508502136404726547 8196434262753204607089821)
                    ·
                      refine ⟨3073662848532451727658683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8196434262753204607089821 3073662848532451727658683)
                      ·
                        rfl

theorem cell23_5985937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 9, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 9, 1, 1, 3].length) (baseStart_5985937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985937 prefixEnd_5985937 := by exact prefixLift 5985937
  have htrace : WordTrace (prefixWord ++ tailWord_5985937) baseStart_5985937 baseEnd_5985937 := by
    simpa [prefixWord, tailWord_5985937, baseEnd_5985937] using wordTrace_append hprefix tailTrace_5985937
  have hstable : (prefixWord ++ tailWord_5985937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985937).length < 2 ^ (prefixWord ++ tailWord_5985937).sum := by decide
  have hdescent : baseEnd_5985937 < baseStart_5985937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985974 : List Nat := [5, 1, 3, 1, 1, 1, 3, 2, 1, 5]
def baseStart_5985974 : Nat := 118140960795 + 5985974 * 2 ^ 59
def prefixEnd_5985974 : Nat := 4983230072969 + 3 ^ 40 * 5985974 * 2
def baseEnd_5985974 : Nat := 1024560615772222694298671

theorem tailTrace_5985974 : CollatzResearch.WordTrace tailWord_5985974 prefixEnd_5985974 1024560615772222694298671 := by
  unfold tailWord_5985974
  simp only [CollatzResearch.WordTrace]
  refine ⟨13645400500990374738313811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145550938677230663875347317 13645400500990374738313811)
  ·
    refine ⟨20468100751485562107470717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13645400500990374738313811 20468100751485562107470717)
    ·
      refine ⟨7675537781807085790301519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20468100751485562107470717 7675537781807085790301519)
      ·
        refine ⟨11513306672710628685452279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7675537781807085790301519 11513306672710628685452279)
        ·
          refine ⟨17269960009065943028178419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11513306672710628685452279 17269960009065943028178419)
          ·
            refine ⟨25904940013598914542267629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17269960009065943028178419 25904940013598914542267629)
            ·
              refine ⟨9714352505099592953350361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25904940013598914542267629 9714352505099592953350361)
              ·
                refine ⟨7285764378824694715012771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9714352505099592953350361 7285764378824694715012771)
                ·
                  refine ⟨10928646568237042072519157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7285764378824694715012771 10928646568237042072519157)
                  ·
                    refine ⟨1024560615772222694298671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10928646568237042072519157 1024560615772222694298671)
                    ·
                      rfl

theorem cell23_5985974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_5985974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985974 prefixEnd_5985974 := by exact prefixLift 5985974
  have htrace : WordTrace (prefixWord ++ tailWord_5985974) baseStart_5985974 baseEnd_5985974 := by
    simpa [prefixWord, tailWord_5985974, baseEnd_5985974] using wordTrace_append hprefix tailTrace_5985974
  have hstable : (prefixWord ++ tailWord_5985974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985974).length < 2 ^ (prefixWord ++ tailWord_5985974).sum := by decide
  have hdescent : baseEnd_5985974 < baseStart_5985974 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985977 : List Nat := [1, 2, 1, 4, 1, 1, 2, 4, 3, 2, 2]
def baseStart_5985977 : Nat := 118140960795 + 5985977 * 2 ^ 59
def prefixEnd_5985977 : Nat := 4983230072969 + 3 ^ 40 * 5985977 * 2
def baseEnd_5985977 : Nat := 3073683387758631571158499

theorem tailTrace_5985977 : CollatzResearch.WordTrace tailWord_5985977 prefixEnd_5985977 3073683387758631571158499 := by
  unfold tailWord_5985977
  simp only [CollatzResearch.WordTrace]
  refine ⟨218326517434835127325380185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145551011623223418216920123 218326517434835127325380185)
  ·
    refine ⟨163744888076126345494035139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218326517434835127325380185 163744888076126345494035139)
    ·
      refine ⟨245617332114189518241052709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163744888076126345494035139 245617332114189518241052709)
      ·
        refine ⟨46053249771410534670197383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 245617332114189518241052709 46053249771410534670197383)
        ·
          refine ⟨69079874657115802005296075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46053249771410534670197383 69079874657115802005296075)
          ·
            refine ⟨103619811985673703007944113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69079874657115802005296075 103619811985673703007944113)
            ·
              refine ⟨77714858989255277255958085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103619811985673703007944113 77714858989255277255958085)
              ·
                refine ⟨14571536060485364485492141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77714858989255277255958085 14571536060485364485492141)
                ·
                  refine ⟨5464326022682011682059553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14571536060485364485492141 5464326022682011682059553)
                  ·
                    refine ⟨4098244517011508761544665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5464326022682011682059553 4098244517011508761544665)
                    ·
                      refine ⟨3073683387758631571158499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4098244517011508761544665 3073683387758631571158499)
                      ·
                        rfl

theorem cell23_5985977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 3, 2, 2].length) (baseStart_5985977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985977 prefixEnd_5985977 := by exact prefixLift 5985977
  have htrace : WordTrace (prefixWord ++ tailWord_5985977) baseStart_5985977 baseEnd_5985977 := by
    simpa [prefixWord, tailWord_5985977, baseEnd_5985977] using wordTrace_append hprefix tailTrace_5985977
  have hstable : (prefixWord ++ tailWord_5985977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985977).length < 2 ^ (prefixWord ++ tailWord_5985977).sum := by decide
  have hdescent : baseEnd_5985977 < baseStart_5985977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5985994 : List Nat := [3, 1, 2, 1, 5, 1, 3, 1, 1, 1, 4]
def baseStart_5985994 : Nat := 118140960795 + 5985994 * 2 ^ 59
def prefixEnd_5985994 : Nat := 4983230072969 + 3 ^ 40 * 5985994 * 2
def baseEnd_5985994 : Nat := 3073692116929758004645921

theorem tailTrace_5985994 : CollatzResearch.WordTrace tailWord_5985994 prefixEnd_5985994 3073692116929758004645921 := by
  unfold tailWord_5985994
  simp only [CollatzResearch.WordTrace]
  refine ⟨54581784368943384807187259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145551424983849026152499357 54581784368943384807187259)
  ·
    refine ⟨81872676553415077210780889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54581784368943384807187259 81872676553415077210780889)
    ·
      refine ⟨61404507415061307908085667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81872676553415077210780889 61404507415061307908085667)
      ·
        refine ⟨92106761122591961862128501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61404507415061307908085667 92106761122591961862128501)
        ·
          refine ⟨8635008855242996424574547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92106761122591961862128501 8635008855242996424574547)
          ·
            refine ⟨12952513282864494636861821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8635008855242996424574547 12952513282864494636861821)
            ·
              refine ⟨4857192481074185488823183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12952513282864494636861821 4857192481074185488823183)
              ·
                refine ⟨7285788721611278233234775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4857192481074185488823183 7285788721611278233234775)
                ·
                  refine ⟨10928683082416917349852163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7285788721611278233234775 10928683082416917349852163)
                  ·
                    refine ⟨16393024623625376024778245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10928683082416917349852163 16393024623625376024778245)
                    ·
                      refine ⟨3073692116929758004645921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16393024623625376024778245 3073692116929758004645921)
                      ·
                        rfl

theorem cell23_5985994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 1, 1, 1, 4].length) (baseStart_5985994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5985994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5985994 prefixEnd_5985994 := by exact prefixLift 5985994
  have htrace : WordTrace (prefixWord ++ tailWord_5985994) baseStart_5985994 baseEnd_5985994 := by
    simpa [prefixWord, tailWord_5985994, baseEnd_5985994] using wordTrace_append hprefix tailTrace_5985994
  have hstable : (prefixWord ++ tailWord_5985994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5985994).length < 2 ^ (prefixWord ++ tailWord_5985994).sum := by decide
  have hdescent : baseEnd_5985994 < baseStart_5985994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5985994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986004 : List Nat := [2, 4, 1, 3, 1, 2, 2, 2, 2, 4]
def baseStart_5986004 : Nat := 118140960795 + 5986004 * 2 ^ 59
def prefixEnd_5986004 : Nat := 4983230072969 + 3 ^ 40 * 5986004 * 2
def baseEnd_5986004 : Nat := 1024565750578767655173625

theorem tailTrace_5986004 : CollatzResearch.WordTrace tailWord_5986004 prefixEnd_5986004 1024565750578767655173625 := by
  unfold tailWord_5986004
  simp only [CollatzResearch.WordTrace]
  refine ⟨109163751102868655468306533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145551668137158207291075377 109163751102868655468306533)
  ·
    refine ⟨20468203331787872900307475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109163751102868655468306533 20468203331787872900307475)
    ·
      refine ⟨30702304997681809350461213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20468203331787872900307475 30702304997681809350461213)
      ·
        refine ⟨11513364374130678506422955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30702304997681809350461213 11513364374130678506422955)
        ·
          refine ⟨17270046561196017759634433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11513364374130678506422955 17270046561196017759634433)
          ·
            refine ⟨12952534920897013319725825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17270046561196017759634433 12952534920897013319725825)
            ·
              refine ⟨9714401190672759989794369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12952534920897013319725825 9714401190672759989794369)
              ·
                refine ⟨7285800893004569992345777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9714401190672759989794369 7285800893004569992345777)
                ·
                  refine ⟨5464350669753427494259333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7285800893004569992345777 5464350669753427494259333)
                  ·
                    refine ⟨1024565750578767655173625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5464350669753427494259333 1024565750578767655173625)
                    ·
                      rfl

theorem cell23_5986004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_5986004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986004 prefixEnd_5986004 := by exact prefixLift 5986004
  have htrace : WordTrace (prefixWord ++ tailWord_5986004) baseStart_5986004 baseEnd_5986004 := by
    simpa [prefixWord, tailWord_5986004, baseEnd_5986004] using wordTrace_append hprefix tailTrace_5986004
  have hstable : (prefixWord ++ tailWord_5986004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986004).length < 2 ^ (prefixWord ++ tailWord_5986004).sum := by decide
  have hdescent : baseEnd_5986004 < baseStart_5986004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986017 : List Nat := [1, 2, 3, 1, 6, 1, 1, 8]
def baseStart_5986017 : Nat := 118140960795 + 5986017 * 2 ^ 59
def prefixEnd_5986017 : Nat := 4983230072969 + 3 ^ 40 * 5986017 * 2
def baseEnd_5986017 : Nat := 113840886184622644987345

theorem tailTrace_5986017 : CollatzResearch.WordTrace tailWord_5986017 prefixEnd_5986017 113840886184622644987345 := by
  unfold tailWord_5986017
  simp only [CollatzResearch.WordTrace]
  refine ⟨218327976354690214156836305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145551984236460142771224203 218327976354690214156836305)
  ·
    refine ⟨163745982266017660617627229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218327976354690214156836305 163745982266017660617627229)
    ·
      refine ⟨61404743349756622731610211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163745982266017660617627229 61404743349756622731610211)
      ·
        refine ⟨92107115024634934097415317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61404743349756622731610211 92107115024634934097415317)
        ·
          refine ⟨4317521016779762535816343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 92107115024634934097415317 4317521016779762535816343)
          ·
            refine ⟨6476281525169643803724515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4317521016779762535816343 6476281525169643803724515)
            ·
              refine ⟨9714422287754465705586773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6476281525169643803724515 9714422287754465705586773)
              ·
                refine ⟨113840886184622644987345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9714422287754465705586773 113840886184622644987345)
                ·
                  rfl

theorem cell23_5986017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 8].length) (baseStart_5986017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986017 prefixEnd_5986017 := by exact prefixLift 5986017
  have htrace : WordTrace (prefixWord ++ tailWord_5986017) baseStart_5986017 baseEnd_5986017 := by
    simpa [prefixWord, tailWord_5986017, baseEnd_5986017] using wordTrace_append hprefix tailTrace_5986017
  have hstable : (prefixWord ++ tailWord_5986017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986017).length < 2 ^ (prefixWord ++ tailWord_5986017).sum := by decide
  have hdescent : baseEnd_5986017 < baseStart_5986017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986027 : List Nat := [1, 1, 1, 1, 2, 4, 4, 3, 2, 1, 3]
def baseStart_5986027 : Nat := 118140960795 + 5986027 * 2 ^ 59
def prefixEnd_5986027 : Nat := 4983230072969 + 3 ^ 40 * 5986027 * 2
def baseEnd_5986027 : Nat := 3073709061791356375533269

theorem tailTrace_5986027 : CollatzResearch.WordTrace tailWord_5986027 prefixEnd_5986027 3073709061791356375533269 := by
  unfold tailWord_5986027
  simp only [CollatzResearch.WordTrace]
  refine ⟨218328341084653985864700335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145552227389769323909800223 218328341084653985864700335)
  ·
    refine ⟨327492511626980978797050503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218328341084653985864700335 327492511626980978797050503)
    ·
      refine ⟨491238767440471468195575755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327492511626980978797050503 491238767440471468195575755)
      ·
        refine ⟨736858151160707202293363633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491238767440471468195575755 736858151160707202293363633)
        ·
          refine ⟨552643613370530401720022725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 736858151160707202293363633 552643613370530401720022725)
          ·
            refine ⟨103620677506974450322504261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 552643613370530401720022725 103620677506974450322504261)
            ·
              refine ⟨19428877032557709435469549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103620677506974450322504261 19428877032557709435469549)
              ·
                refine ⟨7285828887209141038301081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19428877032557709435469549 7285828887209141038301081)
                ·
                  refine ⟨5464371665406855778725811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7285828887209141038301081 5464371665406855778725811)
                  ·
                    refine ⟨8196557498110283668088717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5464371665406855778725811 8196557498110283668088717)
                    ·
                      refine ⟨3073709061791356375533269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8196557498110283668088717 3073709061791356375533269)
                      ·
                        rfl

theorem cell23_5986027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3, 2, 1, 3].length) (baseStart_5986027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986027 prefixEnd_5986027 := by exact prefixLift 5986027
  have htrace : WordTrace (prefixWord ++ tailWord_5986027) baseStart_5986027 baseEnd_5986027 := by
    simpa [prefixWord, tailWord_5986027, baseEnd_5986027] using wordTrace_append hprefix tailTrace_5986027
  have hstable : (prefixWord ++ tailWord_5986027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986027).length < 2 ^ (prefixWord ++ tailWord_5986027).sum := by decide
  have hdescent : baseEnd_5986027 < baseStart_5986027 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986078 : List Nat := [4, 3, 2, 2, 1, 2, 1, 1, 1, 3, 3]
def baseStart_5986078 : Nat := 118140960795 + 5986078 * 2 ^ 59
def prefixEnd_5986078 : Nat := 4983230072969 + 3 ^ 40 * 5986078 * 2
def baseEnd_5986078 : Nat := 3073735249304735675995535

theorem tailTrace_5986078 : CollatzResearch.WordTrace tailWord_5986078 prefixEnd_5986078 3073735249304735675995535 := by
  unfold tailWord_5986078
  simp only [CollatzResearch.WordTrace]
  refine ⟨27291275150933652696850861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145553467471646147716537925 27291275150933652696850861)
  ·
    refine ⟨10234228181600119761319073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27291275150933652696850861 10234228181600119761319073)
    ·
      refine ⟨7675671136200089820989305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10234228181600119761319073 7675671136200089820989305)
      ·
        refine ⟨5756753352150067365741979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7675671136200089820989305 5756753352150067365741979)
        ·
          refine ⟨8635130028225101048612969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5756753352150067365741979 8635130028225101048612969)
          ·
            refine ⟨6476347521168825786459727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8635130028225101048612969 6476347521168825786459727)
            ·
              refine ⟨9714521281753238679689591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6476347521168825786459727 9714521281753238679689591)
              ·
                refine ⟨14571781922629858019534387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9714521281753238679689591 14571781922629858019534387)
                ·
                  refine ⟨21857672883944787029301581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14571781922629858019534387 21857672883944787029301581)
                  ·
                    refine ⟨8196627331479295135988093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21857672883944787029301581 8196627331479295135988093)
                    ·
                      refine ⟨3073735249304735675995535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8196627331479295135988093 3073735249304735675995535)
                      ·
                        rfl

theorem cell23_5986078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_5986078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986078 prefixEnd_5986078 := by exact prefixLift 5986078
  have htrace : WordTrace (prefixWord ++ tailWord_5986078) baseStart_5986078 baseEnd_5986078 := by
    simpa [prefixWord, tailWord_5986078, baseEnd_5986078] using wordTrace_append hprefix tailTrace_5986078
  have hstable : (prefixWord ++ tailWord_5986078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986078).length < 2 ^ (prefixWord ++ tailWord_5986078).sum := by decide
  have hdescent : baseEnd_5986078 < baseStart_5986078 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986080 : List Nat := [2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 4]
def baseStart_5986080 : Nat := 118140960795 + 5986080 * 2 ^ 59
def prefixEnd_5986080 : Nat := 4983230072969 + 3 ^ 40 * 5986080 * 2
def baseEnd_5986080 : Nat := 3073736276266044668170525

theorem tailTrace_5986080 : CollatzResearch.WordTrace tailWord_5986080 prefixEnd_5986080 3073736276266044668170525 := by
  unfold tailWord_5986080
  simp only [CollatzResearch.WordTrace]
  refine ⟨109165137076730987958189847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145553516102307983944253129 109165137076730987958189847)
  ·
    refine ⟨163747705615096481937284771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109165137076730987958189847 163747705615096481937284771)
    ·
      refine ⟨245621558422644722905927157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163747705615096481937284771 245621558422644722905927157)
      ·
        refine ⟨23027021102122942772430671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 245621558422644722905927157 23027021102122942772430671)
        ·
          refine ⟨34540531653184414158646007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23027021102122942772430671 34540531653184414158646007)
          ·
            refine ⟨51810797479776621237969011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34540531653184414158646007 51810797479776621237969011)
            ·
              refine ⟨77716196219664931856953517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51810797479776621237969011 77716196219664931856953517)
              ·
                refine ⟨29143573582374349446357569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77716196219664931856953517 29143573582374349446357569)
                ·
                  refine ⟨21857680186780762084768177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29143573582374349446357569 21857680186780762084768177)
                  ·
                    refine ⟨16393260140085571563576133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21857680186780762084768177 16393260140085571563576133)
                    ·
                      refine ⟨3073736276266044668170525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16393260140085571563576133 3073736276266044668170525)
                      ·
                        rfl

theorem cell23_5986080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_5986080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986080 prefixEnd_5986080 := by exact prefixLift 5986080
  have htrace : WordTrace (prefixWord ++ tailWord_5986080) baseStart_5986080 baseEnd_5986080 := by
    simpa [prefixWord, tailWord_5986080, baseEnd_5986080] using wordTrace_append hprefix tailTrace_5986080
  have hstable : (prefixWord ++ tailWord_5986080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986080).length < 2 ^ (prefixWord ++ tailWord_5986080).sum := by decide
  have hdescent : baseEnd_5986080 < baseStart_5986080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986084 : List Nat := [2, 3, 1, 3, 2, 1, 3, 1, 1, 4, 2]
def baseStart_5986084 : Nat := 118140960795 + 5986084 * 2 ^ 59
def prefixEnd_5986084 : Nat := 4983230072969 + 3 ^ 40 * 5986084 * 2
def baseEnd_5986084 : Nat := 3073738330188662652520507

theorem tailTrace_5986084 : CollatzResearch.WordTrace tailWord_5986084 prefixEnd_5986084 3073738330188662652520507 := by
  unfold tailWord_5986084
  simp only [CollatzResearch.WordTrace]
  refine ⟨109165210022723742299762653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145553613363631656399683537 109165210022723742299762653)
  ·
    refine ⟨40936953758521403362410995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109165210022723742299762653 40936953758521403362410995)
    ·
      refine ⟨61405430637782105043616493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40936953758521403362410995 61405430637782105043616493)
      ·
        refine ⟨23027036489168289391356185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61405430637782105043616493 23027036489168289391356185)
        ·
          refine ⟨17270277366876217043517139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23027036489168289391356185 17270277366876217043517139)
          ·
            refine ⟨25905416050314325565275709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17270277366876217043517139 25905416050314325565275709)
            ·
              refine ⟨9714531018867872086978391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25905416050314325565275709 9714531018867872086978391)
              ·
                refine ⟨14571796528301808130467587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9714531018867872086978391 14571796528301808130467587)
                ·
                  refine ⟨21857694792452712195701381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14571796528301808130467587 21857694792452712195701381)
                  ·
                    refine ⟨4098317773584883536694009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21857694792452712195701381 4098317773584883536694009)
                    ·
                      refine ⟨3073738330188662652520507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4098317773584883536694009 3073738330188662652520507)
                      ·
                        rfl

theorem cell23_5986084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_5986084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986084 prefixEnd_5986084 := by exact prefixLift 5986084
  have htrace : WordTrace (prefixWord ++ tailWord_5986084) baseStart_5986084 baseEnd_5986084 := by
    simpa [prefixWord, tailWord_5986084, baseEnd_5986084] using wordTrace_append hprefix tailTrace_5986084
  have hstable : (prefixWord ++ tailWord_5986084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986084).length < 2 ^ (prefixWord ++ tailWord_5986084).sum := by decide
  have hdescent : baseEnd_5986084 < baseStart_5986084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986118 : List Nat := [6, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2]
def baseStart_5986118 : Nat := 118140960795 + 5986118 * 2 ^ 59
def prefixEnd_5986118 : Nat := 4983230072969 + 3 ^ 40 * 5986118 * 2
def baseEnd_5986118 : Nat := 3073755788530915519495351

theorem tailTrace_5986118 : CollatzResearch.WordTrace tailWord_5986118 prefixEnd_5986118 3073755788530915519495351 := by
  unfold tailWord_5986118
  simp only [CollatzResearch.WordTrace]
  refine ⟨6822864378978884637695719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 145554440084882872270842005 6822864378978884637695719)
  ·
    refine ⟨10234296568468326956543579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6822864378978884637695719 10234296568468326956543579)
    ·
      refine ⟨15351444852702490434815369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10234296568468326956543579 15351444852702490434815369)
      ·
        refine ⟨11513583639526867826111527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15351444852702490434815369 11513583639526867826111527)
        ·
          refine ⟨17270375459290301739167291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11513583639526867826111527 17270375459290301739167291)
          ·
            refine ⟨25905563188935452608750937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17270375459290301739167291 25905563188935452608750937)
            ·
              refine ⟨19429172391701589456563203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25905563188935452608750937 19429172391701589456563203)
              ·
                refine ⟨29143758587552384184844805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19429172391701589456563203 29143758587552384184844805)
                ·
                  refine ⟨5464454735166072034658401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29143758587552384184844805 5464454735166072034658401)
                  ·
                    refine ⟨4098341051374554025993801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5464454735166072034658401 4098341051374554025993801)
                    ·
                      refine ⟨3073755788530915519495351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4098341051374554025993801 3073755788530915519495351)
                      ·
                        rfl

theorem cell23_5986118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_5986118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986118 prefixEnd_5986118 := by exact prefixLift 5986118
  have htrace : WordTrace (prefixWord ++ tailWord_5986118) baseStart_5986118 baseEnd_5986118 := by
    simpa [prefixWord, tailWord_5986118, baseEnd_5986118] using wordTrace_append hprefix tailTrace_5986118
  have hstable : (prefixWord ++ tailWord_5986118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986118).length < 2 ^ (prefixWord ++ tailWord_5986118).sum := by decide
  have hdescent : baseEnd_5986118 < baseStart_5986118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986120 : List Nat := [2, 1, 3, 1, 1, 4, 1, 1, 4, 5]
def baseStart_5986120 : Nat := 118140960795 + 5986120 * 2 ^ 59
def prefixEnd_5986120 : Nat := 4983230072969 + 3 ^ 40 * 5986120 * 2
def baseEnd_5986120 : Nat := 1024585605164074837223447

theorem tailTrace_5986120 : CollatzResearch.WordTrace tailWord_5986120 prefixEnd_5986120 1024585605164074837223447 := by
  unfold tailWord_5986120
  simp only [CollatzResearch.WordTrace]
  refine ⟨109165866536658531373917907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145554488715544708498557209 109165866536658531373917907)
  ·
    refine ⟨163748799804987797060876861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109165866536658531373917907 163748799804987797060876861)
    ·
      refine ⟨61405799926870423897828823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163748799804987797060876861 61405799926870423897828823)
      ·
        refine ⟨92108699890305635846743235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61405799926870423897828823 92108699890305635846743235)
        ·
          refine ⟨138163049835458453770114853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92108699890305635846743235 138163049835458453770114853)
          ·
            refine ⟨25905571844148460081896535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 138163049835458453770114853 25905571844148460081896535)
            ·
              refine ⟨38858357766222690122844803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25905571844148460081896535 38858357766222690122844803)
              ·
                refine ⟨58287536649334035184267205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38858357766222690122844803 58287536649334035184267205)
                ·
                  refine ⟨10928913121750131597050101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58287536649334035184267205 10928913121750131597050101)
                  ·
                    refine ⟨1024585605164074837223447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10928913121750131597050101 1024585605164074837223447)
                    ·
                      rfl

theorem cell23_5986120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_5986120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986120 prefixEnd_5986120 := by exact prefixLift 5986120
  have htrace : WordTrace (prefixWord ++ tailWord_5986120) baseStart_5986120 baseEnd_5986120 := by
    simpa [prefixWord, tailWord_5986120, baseEnd_5986120] using wordTrace_append hprefix tailTrace_5986120
  have hstable : (prefixWord ++ tailWord_5986120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986120).length < 2 ^ (prefixWord ++ tailWord_5986120).sum := by decide
  have hdescent : baseEnd_5986120 < baseStart_5986120 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986123 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 8]
def baseStart_5986123 : Nat := 118140960795 + 5986123 * 2 ^ 59
def prefixEnd_5986123 : Nat := 4983230072969 + 3 ^ 40 * 5986123 * 2
def baseEnd_5986123 : Nat := 3073758355934187999932827

theorem tailTrace_5986123 : CollatzResearch.WordTrace tailWord_5986123 prefixEnd_5986123 3073758355934187999932827 := by
  unfold tailWord_5986123
  simp only [CollatzResearch.WordTrace]
  refine ⟨218331842492306194260195023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145554561661537462840130015 218331842492306194260195023)
  ·
    refine ⟨327497763738459291390292535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218331842492306194260195023 327497763738459291390292535)
    ·
      refine ⟨491246645607688937085438803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327497763738459291390292535 491246645607688937085438803)
      ·
        refine ⟨736869968411533405628158205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491246645607688937085438803 736869968411533405628158205)
        ·
          refine ⟨276326238154325027110559327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 736869968411533405628158205 276326238154325027110559327)
          ·
            refine ⟨414489357231487540665838991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276326238154325027110559327 414489357231487540665838991)
            ·
              refine ⟨621734035847231310998758487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414489357231487540665838991 621734035847231310998758487)
              ·
                refine ⟨932601053770846966498137731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 621734035847231310998758487 932601053770846966498137731)
                ·
                  refine ⟨1398901580656270449747206597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 932601053770846966498137731 1398901580656270449747206597)
                  ·
                    refine ⟨262294046373050709327601237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1398901580656270449747206597 262294046373050709327601237)
                    ·
                      refine ⟨3073758355934187999932827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 262294046373050709327601237 3073758355934187999932827)
                      ·
                        rfl

theorem cell23_5986123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 8].length) (baseStart_5986123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986123 prefixEnd_5986123 := by exact prefixLift 5986123
  have htrace : WordTrace (prefixWord ++ tailWord_5986123) baseStart_5986123 baseEnd_5986123 := by
    simpa [prefixWord, tailWord_5986123, baseEnd_5986123] using wordTrace_append hprefix tailTrace_5986123
  have hstable : (prefixWord ++ tailWord_5986123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986123).length < 2 ^ (prefixWord ++ tailWord_5986123).sum := by decide
  have hdescent : baseEnd_5986123 < baseStart_5986123 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986124 : List Nat := [2, 2, 1, 3, 5, 1, 1, 1, 7]
def baseStart_5986124 : Nat := 118140960795 + 5986124 * 2 ^ 59
def prefixEnd_5986124 : Nat := 4983230072969 + 3 ^ 40 * 5986124 * 2
def baseEnd_5986124 : Nat := 341528763268315832891147

theorem tailTrace_5986124 : CollatzResearch.WordTrace tailWord_5986124 prefixEnd_5986124 341528763268315832891147 := by
  unfold tailWord_5986124
  simp only [CollatzResearch.WordTrace]
  refine ⟨109165939482651285715490713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145554585976868380953987617 109165939482651285715490713)
  ·
    refine ⟨81874454611988464286618035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109165939482651285715490713 81874454611988464286618035)
    ·
      refine ⟨122811681917982696429927053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81874454611988464286618035 122811681917982696429927053)
      ·
        refine ⟨46054380719243511161222645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122811681917982696429927053 46054380719243511161222645)
        ·
          refine ⟨4317598192429079171364623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46054380719243511161222645 4317598192429079171364623)
          ·
            refine ⟨6476397288643618757046935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4317598192429079171364623 6476397288643618757046935)
            ·
              refine ⟨9714595932965428135570403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6476397288643618757046935 9714595932965428135570403)
              ·
                refine ⟨14571893899448142203355605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9714595932965428135570403 14571893899448142203355605)
                ·
                  refine ⟨341528763268315832891147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14571893899448142203355605 341528763268315832891147)
                  ·
                    rfl

theorem cell23_5986124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 7].length) (baseStart_5986124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986124 prefixEnd_5986124 := by exact prefixLift 5986124
  have htrace : WordTrace (prefixWord ++ tailWord_5986124) baseStart_5986124 baseEnd_5986124 := by
    simpa [prefixWord, tailWord_5986124, baseEnd_5986124] using wordTrace_append hprefix tailTrace_5986124
  have hstable : (prefixWord ++ tailWord_5986124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986124).length < 2 ^ (prefixWord ++ tailWord_5986124).sum := by decide
  have hdescent : baseEnd_5986124 < baseStart_5986124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986130 : List Nat := [3, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7]
def baseStart_5986130 : Nat := 118140960795 + 5986130 * 2 ^ 59
def prefixEnd_5986130 : Nat := 4983230072969 + 3 ^ 40 * 5986130 * 2
def baseEnd_5986130 : Nat := 3073761950298769472545295

theorem tailTrace_5986130 : CollatzResearch.WordTrace tailWord_5986130 prefixEnd_5986130 3073761950298769472545295 := by
  unfold tailWord_5986130
  simp only [CollatzResearch.WordTrace]
  refine ⟨54583024450820208613924961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145554731868853889637133229 54583024450820208613924961)
  ·
    refine ⟨40937268338115156460443721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54583024450820208613924961 40937268338115156460443721)
    ·
      refine ⟨30702951253586367345332791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40937268338115156460443721 30702951253586367345332791)
      ·
        refine ⟨46054426880379551017999187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30702951253586367345332791 46054426880379551017999187)
        ·
          refine ⟨69081640320569326526998781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46054426880379551017999187 69081640320569326526998781)
          ·
            refine ⟨25905615120213497447624543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69081640320569326526998781 25905615120213497447624543)
            ·
              refine ⟨38858422680320246171436815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25905615120213497447624543 38858422680320246171436815)
              ·
                refine ⟨58287634020480369257155223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38858422680320246171436815 58287634020480369257155223)
                ·
                  refine ⟨87431451030720553885732835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58287634020480369257155223 87431451030720553885732835)
                  ·
                    refine ⟨131147176546080830828599253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 87431451030720553885732835 131147176546080830828599253)
                    ·
                      refine ⟨3073761950298769472545295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 131147176546080830828599253 3073761950298769472545295)
                      ·
                        rfl

theorem cell23_5986130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_5986130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986130 prefixEnd_5986130 := by exact prefixLift 5986130
  have htrace : WordTrace (prefixWord ++ tailWord_5986130) baseStart_5986130 baseEnd_5986130 := by
    simpa [prefixWord, tailWord_5986130, baseEnd_5986130] using wordTrace_append hprefix tailTrace_5986130
  have hstable : (prefixWord ++ tailWord_5986130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986130).length < 2 ^ (prefixWord ++ tailWord_5986130).sum := by decide
  have hdescent : baseEnd_5986130 < baseStart_5986130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986135 : List Nat := [1, 1, 3, 2, 6, 1, 2, 1, 2, 2, 2]
def baseStart_5986135 : Nat := 118140960795 + 5986135 * 2 ^ 59
def prefixEnd_5986135 : Nat := 4983230072969 + 3 ^ 40 * 5986135 * 2
def baseEnd_5986135 : Nat := 3073764517702041952982773

theorem tailTrace_5986135 : CollatzResearch.WordTrace tailWord_5986135 prefixEnd_5986135 3073764517702041952982773 := by
  unfold tailWord_5986135
  simp only [CollatzResearch.WordTrace]
  refine ⟨218332280168262720309631859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145554853445508480206421239 218332280168262720309631859)
  ·
    refine ⟨327498420252394080464447789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218332280168262720309631859 327498420252394080464447789)
    ·
      refine ⟨122811907594647780174167921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 327498420252394080464447789 122811907594647780174167921)
      ·
        refine ⟨92108930695985835130625941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122811907594647780174167921 92108930695985835130625941)
        ·
          refine ⟨4317606126374336021748091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 92108930695985835130625941 4317606126374336021748091)
          ·
            refine ⟨6476409189561504032622137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4317606126374336021748091 6476409189561504032622137)
            ·
              refine ⟨4857306892171128024466603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6476409189561504032622137 4857306892171128024466603)
              ·
                refine ⟨7285960338256692036699905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4857306892171128024466603 7285960338256692036699905)
                ·
                  refine ⟨5464470253692519027524929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7285960338256692036699905 5464470253692519027524929)
                  ·
                    refine ⟨4098352690269389270643697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5464470253692519027524929 4098352690269389270643697)
                    ·
                      refine ⟨3073764517702041952982773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4098352690269389270643697 3073764517702041952982773)
                      ·
                        rfl

theorem cell23_5986135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 1, 2, 2, 2].length) (baseStart_5986135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986135 prefixEnd_5986135 := by exact prefixLift 5986135
  have htrace : WordTrace (prefixWord ++ tailWord_5986135) baseStart_5986135 baseEnd_5986135 := by
    simpa [prefixWord, tailWord_5986135, baseEnd_5986135] using wordTrace_append hprefix tailTrace_5986135
  have hstable : (prefixWord ++ tailWord_5986135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986135).length < 2 ^ (prefixWord ++ tailWord_5986135).sum := by decide
  have hdescent : baseEnd_5986135 < baseStart_5986135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986157 : List Nat := [1, 5, 1, 1, 1, 1, 3, 3, 2, 1, 4]
def baseStart_5986157 : Nat := 118140960795 + 5986157 * 2 ^ 59
def prefixEnd_5986157 : Nat := 4983230072969 + 3 ^ 40 * 5986157 * 2
def baseEnd_5986157 : Nat := 3073775814276440866907671

theorem tailTrace_5986157 : CollatzResearch.WordTrace tailWord_5986157 prefixEnd_5986157 3073775814276440866907671 := by
  unfold tailWord_5986157
  simp only [CollatzResearch.WordTrace]
  refine ⟨218333082574183018066932725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145555388382788678711288483 218333082574183018066932725)
  ·
    refine ⟨20468726491329657943774943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 218333082574183018066932725 20468726491329657943774943)
    ·
      refine ⟨30703089736994486915662415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20468726491329657943774943 30703089736994486915662415)
      ·
        refine ⟨46054634605491730373493623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30703089736994486915662415 46054634605491730373493623)
        ·
          refine ⟨69081951908237595560240435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46054634605491730373493623 69081951908237595560240435)
          ·
            refine ⟨103622927862356393340360653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69081951908237595560240435 103622927862356393340360653)
            ·
              refine ⟨38858597948383647502635245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103622927862356393340360653 38858597948383647502635245)
              ·
                refine ⟨14571974230643867813488217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38858597948383647502635245 14571974230643867813488217)
                ·
                  refine ⟨10928980672982900860116163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14571974230643867813488217 10928980672982900860116163)
                  ·
                    refine ⟨16393471009474351290174245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10928980672982900860116163 16393471009474351290174245)
                    ·
                      refine ⟨3073775814276440866907671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16393471009474351290174245 3073775814276440866907671)
                      ·
                        rfl

theorem cell23_5986157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_5986157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986157 prefixEnd_5986157 := by exact prefixLift 5986157
  have htrace : WordTrace (prefixWord ++ tailWord_5986157) baseStart_5986157 baseEnd_5986157 := by
    simpa [prefixWord, tailWord_5986157, baseEnd_5986157] using wordTrace_append hprefix tailTrace_5986157
  have hstable : (prefixWord ++ tailWord_5986157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986157).length < 2 ^ (prefixWord ++ tailWord_5986157).sum := by decide
  have hdescent : baseEnd_5986157 < baseStart_5986157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986180 : List Nat := [2, 3, 2, 1, 1, 1, 2, 3, 8]
def baseStart_5986180 : Nat := 118140960795 + 5986180 * 2 ^ 59
def prefixEnd_5986180 : Nat := 4983230072969 + 3 ^ 40 * 5986180 * 2
def baseEnd_5986180 : Nat := 341531958259054919657785

theorem tailTrace_5986180 : CollatzResearch.WordTrace tailWord_5986180 prefixEnd_5986180 341531958259054919657785 := by
  unfold tailWord_5986180
  simp only [CollatzResearch.WordTrace]
  refine ⟨109166960726549846497509997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145555947635399795330013329 109166960726549846497509997)
  ·
    refine ⟨40937610272456192436566249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109166960726549846497509997 40937610272456192436566249)
    ·
      refine ⟨30703207704342144327424687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40937610272456192436566249 30703207704342144327424687)
      ·
        refine ⟨46054811556513216491137031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30703207704342144327424687 46054811556513216491137031)
        ·
          refine ⟨69082217334769824736705547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46054811556513216491137031 69082217334769824736705547)
          ·
            refine ⟨103623326002154737105058321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69082217334769824736705547 103623326002154737105058321)
            ·
              refine ⟨77717494501616052828793741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103623326002154737105058321 77717494501616052828793741)
              ·
                refine ⟨29144060438106019810797653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77717494501616052828793741 29144060438106019810797653)
                ·
                  refine ⟨341531958259054919657785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29144060438106019810797653 341531958259054919657785)
                  ·
                    rfl

theorem cell23_5986180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 8].length) (baseStart_5986180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986180 prefixEnd_5986180 := by exact prefixLift 5986180
  have htrace : WordTrace (prefixWord ++ tailWord_5986180) baseStart_5986180 baseEnd_5986180 := by
    simpa [prefixWord, tailWord_5986180, baseEnd_5986180] using wordTrace_append hprefix tailTrace_5986180
  have hstable : (prefixWord ++ tailWord_5986180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986180).length < 2 ^ (prefixWord ++ tailWord_5986180).sum := by decide
  have hdescent : baseEnd_5986180 < baseStart_5986180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986227 : List Nat := [1, 1, 1, 2, 3, 1, 5, 3, 1, 5]
def baseStart_5986227 : Nat := 118140960795 + 5986227 * 2 ^ 59
def prefixEnd_5986227 : Nat := 4983230072969 + 3 ^ 40 * 5986227 * 2
def baseEnd_5986227 : Nat := 1024603919307418531010783

theorem tailTrace_5986227 : CollatzResearch.WordTrace tailWord_5986227 prefixEnd_5986227 1024603919307418531010783 := by
  unfold tailWord_5986227
  simp only [CollatzResearch.WordTrace]
  refine ⟨218335635683929420021980935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145557090455952946681320623 218335635683929420021980935)
  ·
    refine ⟨327503453525894130032971403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218335635683929420021980935 327503453525894130032971403)
    ·
      refine ⟨491255180288841195049457105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327503453525894130032971403 491255180288841195049457105)
      ·
        refine ⟨368441385216630896287092829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 491255180288841195049457105 368441385216630896287092829)
        ·
          refine ⟨138165519456236586107659811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 368441385216630896287092829 138165519456236586107659811)
          ·
            refine ⟨207248279184354879161489717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138165519456236586107659811 207248279184354879161489717)
            ·
              refine ⟨19429526173533269921389661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 207248279184354879161489717 19429526173533269921389661)
              ·
                refine ⟨7286072315074976220521123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19429526173533269921389661 7286072315074976220521123)
                ·
                  refine ⟨10929108472612464330781685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7286072315074976220521123 10929108472612464330781685)
                  ·
                    refine ⟨1024603919307418531010783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10929108472612464330781685 1024603919307418531010783)
                    ·
                      rfl

theorem cell23_5986227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3, 1, 5].length) (baseStart_5986227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986227 prefixEnd_5986227 := by exact prefixLift 5986227
  have htrace : WordTrace (prefixWord ++ tailWord_5986227) baseStart_5986227 baseEnd_5986227 := by
    simpa [prefixWord, tailWord_5986227, baseEnd_5986227] using wordTrace_append hprefix tailTrace_5986227
  have hstable : (prefixWord ++ tailWord_5986227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986227).length < 2 ^ (prefixWord ++ tailWord_5986227).sum := by decide
  have hdescent : baseEnd_5986227 < baseStart_5986227 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986264 : List Nat := [2, 1, 2, 2, 2, 2, 4, 2, 1, 1, 4]
def baseStart_5986264 : Nat := 118140960795 + 5986264 * 2 ^ 59
def prefixEnd_5986264 : Nat := 4983230072969 + 3 ^ 40 * 5986264 * 2
def baseEnd_5986264 : Nat := 3073830756706471948269679

theorem tailTrace_5986264 : CollatzResearch.WordTrace tailWord_5986264 prefixEnd_5986264 3073830756706471948269679 := by
  unfold tailWord_5986264
  simp only [CollatzResearch.WordTrace]
  refine ⟨109168492592397687670538923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145557990123196916894051897 109168492592397687670538923)
  ·
    refine ⟨163752738888596531505808385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109168492592397687670538923 163752738888596531505808385)
    ·
      refine ⟨122814554166447398629356289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163752738888596531505808385 122814554166447398629356289)
      ·
        refine ⟨92110915624835548972017217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122814554166447398629356289 92110915624835548972017217)
        ·
          refine ⟨69083186718626661729012913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92110915624835548972017217 69083186718626661729012913)
          ·
            refine ⟨51812390038969996296759685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69083186718626661729012913 51812390038969996296759685)
            ·
              refine ⟨9714823132306874305642441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51812390038969996296759685 9714823132306874305642441)
              ·
                refine ⟨7286117349230155729231831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9714823132306874305642441 7286117349230155729231831)
                ·
                  refine ⟨10929176023845233593847747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7286117349230155729231831 10929176023845233593847747)
                  ·
                    refine ⟨16393764035767850390771621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10929176023845233593847747 16393764035767850390771621)
                    ·
                      refine ⟨3073830756706471948269679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16393764035767850390771621 3073830756706471948269679)
                      ·
                        rfl

theorem cell23_5986264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2, 1, 1, 4].length) (baseStart_5986264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5986264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5986264 prefixEnd_5986264 := by exact prefixLift 5986264
  have htrace : WordTrace (prefixWord ++ tailWord_5986264) baseStart_5986264 baseEnd_5986264 := by
    simpa [prefixWord, tailWord_5986264, baseEnd_5986264] using wordTrace_append hprefix tailTrace_5986264
  have hstable : (prefixWord ++ tailWord_5986264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986264).length < 2 ^ (prefixWord ++ tailWord_5986264).sum := by decide
  have hdescent : baseEnd_5986264 < baseStart_5986264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
